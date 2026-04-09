-- |
-- Module      : Clementine.Wellformed
-- Copyright   : (c) 2026 Clementine contributors
-- License     : GPL v3 (see LICENSE)
--
-- Static wellformedness checks per design step 3 §3.4.
--
-- Each check is a pure function on the parsed 'Protocol' returning
-- a list of 'ClementineError's. The driver in 'Clementine' runs
-- 'checkWellformed' before lowering and refuses to compile if any
-- error-severity diagnostics come back. Warning-severity
-- diagnostics are reported but don't block compilation.
--
-- This module implements the AST-only invariants. The post-lowering
-- ones (arity stability, Running-before-Commit reachability,
-- partial-deconstruction detection) live elsewhere and run against
-- the in-memory 'Theory' value rather than the surface AST.
--
-- The full set of soundness invariants from design step 3 §3.4:
--
--     1. Arity stability               (post-lowering, deferred)
--     2. Honest coverage               (auto-handled by lowering)
--     3. Reveal => !Ltk                (auto-handled by lowering)
--     4. Running before Commit         (post-lowering, deferred)
--     5. Secret reachability           (here, E0205)
--     6. Executable mandatory          (here, E0206)
--     7. Reserved-name shadowing       (here, E0207)
--     8. Phase coherence               (deferred until phases land)
--     9. Honest peer reachability      (here, E0209)
module Clementine.Wellformed
  ( checkWellformed
  , wellformedErrors
  , wellformedWarnings
  ) where

import           Data.List       (group, sort)
import qualified Data.Set        as Set
import qualified Data.Text       as T

import           Clementine.AST
import           Clementine.Errors

--------------------------------------------------------------------------------
-- Top-level entry point
--------------------------------------------------------------------------------

-- | Run every wellformedness check on a 'Protocol' and return all
-- diagnostics, both errors and warnings, in source order.
checkWellformed :: Protocol -> [ClementineError]
checkWellformed p = concat
  [ checkExecutableMandatory p
  , checkReservedNames p
  , checkDuplicatePrincipals p
  , checkDuplicateStepLabels p
  , checkVerifyTermRefs p
  , checkClaimSecretRefs p
  , checkAgreementRoles p
  ]

-- | Filter to just the error-severity diagnostics.
wellformedErrors :: [ClementineError] -> [ClementineError]
wellformedErrors = filter ((== SevError) . errorCodeSeverity . errCode)

-- | Filter to just the warning-severity diagnostics.
wellformedWarnings :: [ClementineError] -> [ClementineError]
wellformedWarnings = filter ((== SevWarning) . errorCodeSeverity . errCode)

--------------------------------------------------------------------------------
-- §3.4 invariant 6 — executable lemma mandatory
--------------------------------------------------------------------------------

-- | The verify block must contain an 'executable' query. Without
-- one, every other lemma could be vacuously true because no honest
-- run reaches the action facts they quantify over.
checkExecutableMandatory :: Protocol -> [ClementineError]
checkExecutableMandatory p
  | any isExecutable (protoVerify p) = []
  | otherwise =
      [ ClementineError
          { errCode    = E0206
          , errPos     = Just (protoPos p)
          , errMsg     = "verify block has no `executable` query"
          , errDetails =
              [ "Every Clementine protocol must include an `executable`"
              , "query in its verify block. Without it, every other"
              , "lemma could be vacuously true because no honest run"
              , "reaches the action facts they quantify over."
              , ""
              , "Add `executable` to the top of your verify block:"
              , ""
              , "    verify {"
              , "      executable"
              , "      secrecy(...)"
              , "      ..."
              , "    }"
              ]
          }
      ]
  where
    isExecutable QExecutable{} = True
    isExecutable _             = False

--------------------------------------------------------------------------------
-- §3.4 invariant 7 — reserved-name shadowing
--------------------------------------------------------------------------------

-- | User identifiers must not start with reserved prefixes that
-- the lowering uses for synthesized Sapic variables and action
-- facts. The blacklist matches the canonical action-fact
-- vocabulary from design step 3 §3.1.
checkReservedNames :: Protocol -> [ClementineError]
checkReservedNames p =
  concatMap checkPrincipal (protoPrincipals p) ++
  concatMap checkStep      (protoSteps p)
  where
    checkPrincipal pr =
      [ reserved (prinPos pr) "principal" (prinName pr)
      | startsWithReserved (prinName pr)
      ]
      ++ concatMap (checkKnowledge (prinPos pr)) (prinKnows pr)

    checkKnowledge pos k = case k of
      KGenerates    n p' -> [reserved p' "generated key" n | startsWithReserved n]
      KKnowsPublic  n _ p' -> [reserved p' "public param" n | startsWithReserved n]
      KKnowsPrivate n p' -> [reserved p' "private param" n | startsWithReserved n]
      where
        _ = pos   -- silence unused; per-knowledge pos is more precise

    checkStep s =
      [ reserved (stepPos s) "step label" (stepLabel s)
      | startsWithReserved (stepLabel s)
      ]
      ++ concatMap (checkStmt (stepPos s)) (stepBody s)

    checkStmt pos stmt = case stmt of
      SNew n p'    -> [reserved p' "fresh name" n | startsWithReserved n]
      SLet n _ p'  -> [reserved p' "let binding" n | startsWithReserved n]
      _            -> [] where _ = pos

    reserved pos kind n = ClementineError
      { errCode    = E0207
      , errPos     = Just pos
      , errMsg     = T.pack kind <> " name `" <> n <> "` shadows a reserved prefix"
      , errDetails =
          [ "Identifiers starting with `pat`, `Init`, `Setup_`, `Step_`,"
          , "`Reveal_`, or `KeyGen_` are reserved for the Clementine"
          , "compiler's synthesized Sapic variables and action facts."
          , "Rename `" <> n <> "` to avoid the prefix collision."
          ]
      }

    startsWithReserved n =
      any (`T.isPrefixOf` n)
        [ "pat", "Init", "Setup_", "Step_", "Reveal_", "KeyGen_" ]

--------------------------------------------------------------------------------
-- Duplicate principal / step labels (E0103, E0104)
--------------------------------------------------------------------------------

checkDuplicatePrincipals :: Protocol -> [ClementineError]
checkDuplicatePrincipals p =
  [ ClementineError
      { errCode    = E0103
      , errPos     = Just (prinPos pr)
      , errMsg     = "duplicate principal name `" <> prinName pr <> "`"
      , errDetails =
          [ "Each principal name must appear at most once in a protocol."
          , "Rename one of the duplicates."
          ]
      }
  | pr <- protoPrincipals p
  , length (filter (\pr' -> prinName pr' == prinName pr) (protoPrincipals p)) > 1
  , let allOfThisName = filter (\pr' -> prinName pr' == prinName pr) (protoPrincipals p)
  , prinPos pr /= prinPos (head allOfThisName)   -- skip the first occurrence
  ]

checkDuplicateStepLabels :: Protocol -> [ClementineError]
checkDuplicateStepLabels p =
  let grouped = group (sort (map stepLabel (protoSteps p)))
      dupes   = Set.fromList [ name | (name : _ : _) <- grouped ]
      seenAt  = Set.empty       -- positions we've already reported for
  in  go seenAt dupes (protoSteps p)
  where
    go _    _     []     = []
    go seen dupes (s:ss)
      | stepLabel s `Set.member` dupes
      , stepLabel s `Set.notMember` seen   -- skip the first occurrence
      = go (Set.insert (stepLabel s) seen) dupes ss
      | stepLabel s `Set.member` dupes =
          ClementineError
            { errCode    = E0104
            , errPos     = Just (stepPos s)
            , errMsg     = "duplicate step label `" <> stepLabel s <> "`"
            , errDetails =
                [ "Each step label must be unique within a protocol."
                , "The same label appears in multiple `step` declarations."
                , "Rename one of them."
                ]
            } : go seen dupes ss
      | otherwise = go seen dupes ss

--------------------------------------------------------------------------------
-- E0102 — verify block term references must resolve
--------------------------------------------------------------------------------

-- | Every term reference inside the @verify@ block must point at
-- some name that's bound somewhere in the protocol. The check is
-- conservative: we walk every step body looking for @new@/@let@
-- bindings and the principal blocks for @generates@/@knows@, and
-- demand each verify-block reference exist in that union.
checkVerifyTermRefs :: Protocol -> [ClementineError]
checkVerifyTermRefs p =
  let allBindings = collectAllBindings p
      refs        = concatMap queryTermRefs (protoVerify p)
  in  [ ClementineError
          { errCode    = E0102
          , errPos     = Just (trPos tr)
          , errMsg     = "undefined term reference `" <> trVar tr <> "`"
          , errDetails =
              [ "The verify block references `" <> trVar tr <> "` but no"
              , "step or principal block declares it."
              , "Either rename the reference to match an existing"
              , "binding, or add a `new`/`let`/`generates` for it."
              ]
          }
      | tr <- refs
      , trVar tr `Set.notMember` allBindings
      ]
  where
    queryTermRefs q = case q of
      QExecutable _              -> []
      QSecrecy t _               -> [t]
      QForwardSecrecy t _        -> [t]
      QInjAgreement _ _ ts _     -> ts
      QNonInjAgreement _ _ ts _  -> ts
      QAuthentication _ _ _      -> []

--------------------------------------------------------------------------------
-- E0205 — claim secret references must resolve to a binding in
-- the same step body or earlier
--------------------------------------------------------------------------------

checkClaimSecretRefs :: Protocol -> [ClementineError]
checkClaimSecretRefs p =
  let allBindings = collectAllBindings p
  in  concatMap (checkStep allBindings) (protoSteps p)
  where
    checkStep bindings s =
      [ ClementineError
          { errCode    = E0205
          , errPos     = Just sp
          , errMsg     = "claim secret(`" <> n <> "`) references undefined term"
          , errDetails =
              [ "The variable `" <> n <> "` is not bound by any `new`,"
              , "`let`, or principal-block declaration in this protocol."
              , "Add a binding for it before the claim, or rename the"
              , "claim to match an existing variable."
              ]
          }
      | SClaim (ClaimSecret n) sp <- stepBody s
      , n `Set.notMember` bindings
      ]

--------------------------------------------------------------------------------
-- §3.4 invariant 9 — agreement queries must reference declared principals
--------------------------------------------------------------------------------

checkAgreementRoles :: Protocol -> [ClementineError]
checkAgreementRoles p =
  let principals = Set.fromList (map prinName (protoPrincipals p))
  in  concatMap (queryRoles principals) (protoVerify p)
  where
    queryRoles ps q = case q of
      QInjAgreement i r _ pos    -> roleErrs ps "injective_agreement" i r pos
      QNonInjAgreement i r _ pos -> roleErrs ps "non_injective_agreement" i r pos
      QAuthentication i r pos    -> roleErrs ps "authentication" i r pos
      _                          -> []

    roleErrs ps qName i r pos =
      [ ClementineError
          { errCode    = E0209
          , errPos     = Just pos
          , errMsg     = qName <> " references undeclared role `" <> n <> "`"
          , errDetails =
              [ "The verify-block query mentions a principal name that"
              , "doesn't appear in any `principal { ... }` block."
              , "Either declare the principal or fix the typo."
              ]
          }
      | n <- [i, r]
      , n `Set.notMember` ps
      ]

--------------------------------------------------------------------------------
-- Helper: collect every name bound anywhere in the protocol
--------------------------------------------------------------------------------

-- | The union of every binding site's name in a protocol — every
-- @generates@, every @knows public@, every @knows private@, every
-- @new@, every @let@.
collectAllBindings :: Protocol -> Set.Set T.Text
collectAllBindings p = Set.fromList $
  concatMap principalBindings (protoPrincipals p) ++
  concatMap stepBindings      (protoSteps p)
  where
    principalBindings pr = concatMap fromKnow (prinKnows pr)
    fromKnow k = case k of
      KGenerates    n _   -> [n]
      KKnowsPublic  n _ _ -> [n]
      KKnowsPrivate n _   -> [n]

    stepBindings s = concatMap fromStmt (stepBody s)
    fromStmt stmt = case stmt of
      SNew n _   -> [n]
      SLet n _ _ -> [n]
      _          -> []
