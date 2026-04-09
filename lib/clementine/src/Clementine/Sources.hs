-- |
-- Module      : Clementine.Sources
-- Copyright   : (c) 2026 Clementine contributors
-- License     : GPL v3 (see LICENSE)
--
-- Sources lemma inference (Clementine design step 5).
--
-- == Background
--
-- Tamarin's backward-chaining solver, when faced with a goal that
-- contains a fresh value @~n@ that was wrapped inside a
-- cryptographic envelope on the way out and the receiver gets it
-- in a /different/ envelope, can't tell which @Out(...)@ site
-- originated @~n@. Without help, the search branches at every
-- step and may not terminate. The fix is a /sources lemma/
-- (annotated @[sources]@) that tells the matcher: "if you see
-- @~n@ arriving at this @In(...)@, the only honest sources are
-- this specific list of rules."
--
-- == What this module does
--
-- For each Clementine 'Protocol', detect whether any open chains
-- exist (per design step 5 §5.2) and emit an @auto_sources@
-- lemma that closes them.
--
-- For protocols where the lowering already eliminates open chains
-- — for example, ISO-DH after the @mkDHPatVar@ wire-format fix in
-- 'Clementine.LowerSapic' — this module emits a trivially-true
-- sources lemma. The lemma is harmless: Tamarin proves it
-- instantly and the rest of the proof effort is unaffected.
--
-- For protocols with genuine open chains (like the canonical NSL
-- nonce-in-encryption pattern), this module synthesizes a
-- structurally-correct lemma whose conjuncts assert that each
-- chain's sink either came from @KU@ (adversary-derived) or from
-- the originating fresh-name rule.
--
-- == Status
--
-- This v0.4 cut implements the chain detector (§5.2 step 1-3) but
-- the synthesized lemma is intentionally degenerate: it asserts
-- @True@. The detector identifies which chains exist; emitting a
-- non-trivial lemma needs synthetic action facts on the source
-- and sink rules, which is a follow-up commit. The framework is
-- in place so that follow-up is local.
module Clementine.Sources
  ( OpenChain(..)
  , detectOpenChains
  , makeAutoSourcesLemma
  ) where

import qualified Data.Set         as Set
import qualified Data.Text        as T

import           Clementine.AST

--------------------------------------------------------------------------------
-- Open chain detection
--------------------------------------------------------------------------------

-- | A detected open chain. We record the originating fresh name,
-- the principal that generated it, and the principal that later
-- receives it inside a cryptographic shell different from the one
-- it was sent in.
data OpenChain = OpenChain
  { ocFreshName    :: !T.Text
  , ocOriginRole   :: !T.Text
  , ocReceiverRole :: !T.Text
  , ocSendShell    :: !ShellPath
  , ocReceiveShell :: !ShellPath
  } deriving (Show, Eq)

-- | A path of cryptographic constructors from the root of an
-- expression to the position of a tracked fresh name. The current
-- v0.4 implementation tracks only the outermost shell — for the
-- ISO-DH \/ NSL fixture set this is sufficient because the
-- problematic chains are one shell deep.
data ShellPath
  = ShellNone               -- ^ leaf, no enclosing shell
  | ShellAEnc               -- ^ inside @aenc(_, _)@
  | ShellSEnc               -- ^ inside @senc(_, _)@
  | ShellSign               -- ^ inside @sign(_, _)@
  | ShellHash               -- ^ inside @h(_)@
  | ShellDH                 -- ^ inside @_^_@
  deriving (Show, Eq, Ord)

-- | Walk a 'Protocol' and identify all open chains per design
-- step 5 §5.2 (the algorithm in this commit is the simplified
-- "outermost shell" version; the full position-aware tracker
-- arrives in a follow-up).
--
-- The pipeline:
--
--   1. Collect every @new n@ across all step bodies, paired with
--      the principal that generates it (\"origin\").
--
--   2. For each fresh, find every @SSend@ in the protocol that
--      mentions the fresh inside an opaque shell — record the
--      shell.
--
--   3. For each receive of the same fresh on a /different/
--      principal, compare the receive shell to the send shells.
--      If they differ, that's an open chain.
detectOpenChains :: Protocol -> [OpenChain]
detectOpenChains p = concatMap forFresh allFreshes
  where
    -- Every (principal, fresh) pair declared via `new n`.
    allFreshes :: [(T.Text, T.Text)]
    allFreshes =
      [ (stepFrom s, n)
      | s <- protoSteps p
      , SNew n _ <- stepBody s
      ]

    -- For a given fresh, look at all sends that mention it and
    -- all receives of the same fresh on the OTHER side. If a
    -- send/receive pair has different outermost shells, it's an
    -- open chain.
    forFresh :: (T.Text, T.Text) -> [OpenChain]
    forFresh (origin, n) =
      let sends = [ (s, shell) | s <- protoSteps p
                   , stepFrom s == origin
                   , SSend e _ <- stepBody s
                   , let shell = outerShellOf n e
                   , freshOccursIn n e
                   ]
          receives =
            [ (s, shellAt) | s <- protoSteps p
            , stepFrom s /= origin
            , SSend e _ <- stepBody s
            , let shellAt = outerShellOf n e
            , freshOccursIn n e
            ]
      in  [ OpenChain
              { ocFreshName    = n
              , ocOriginRole   = origin
              , ocReceiverRole = stepFrom rs
              , ocSendShell    = ssShell
              , ocReceiveShell = rsShell
              }
          | (_, ssShell) <- sends
          , (rs, rsShell) <- receives
          , ssShell /= rsShell
          ]

-- | The outermost cryptographic shell containing a particular
-- fresh-name reference inside an expression. Returns 'ShellNone'
-- if the fresh doesn't appear, or if it appears at the top level
-- with no enclosing shell.
outerShellOf :: T.Text -> Expr -> ShellPath
outerShellOf n e
  | not (freshOccursIn n e) = ShellNone
  | otherwise = case e of
      EApp OpAEnc _ _ -> ShellAEnc
      EApp OpEnc  _ _ -> ShellSEnc
      EApp OpSign _ _ -> ShellSign
      EApp OpH    _ _ -> ShellHash
      EExp _ _ _      -> ShellDH
      ETup xs _       ->
        case Set.toList (Set.fromList (map (outerShellOf n) (filter (freshOccursIn n) xs))) of
          [s] -> s
          _   -> ShellNone
      _               -> ShellNone

-- | Whether a fresh-name identifier appears anywhere in an
-- expression's free-variable set.
freshOccursIn :: T.Text -> Expr -> Bool
freshOccursIn n = go
  where
    go (EVar v _)       = v == n
    go (EConst _ _)     = False
    go (ETup xs _)      = any go xs
    go (EApp _ xs _)    = any go xs
    go (EExp a b _)     = go a || go b

--------------------------------------------------------------------------------
-- Lemma synthesis
--------------------------------------------------------------------------------

-- | Build the @auto_sources@ lemma for a protocol. The body asserts
-- that any value bound at a 'ChainSnk' event was either learned by
-- the adversary (@KU@) or originated from a matching 'ChainSrc' on
-- the sender's side.
--
-- This is the §5 sources lemma in its general form: a single
-- universally-quantified conjunct that covers every (tag, term)
-- pair the protocol emits ChainSrc/ChainSnk for. The chain events
-- are injected by 'Clementine.LowerSapic.computeChainEvents'.
--
-- The lemma is returned as a parsable @.spthy@ source string so
-- the caller can hand it to @parseLemmaWithMacros@ alongside the
-- other Clementine-generated lemmas. We always emit the lemma
-- when the protocol has at least one principal that does both
-- @new n@ and @send <_, n, _>@ in the same step — i.e. whenever
-- 'computeChainEvents' would have something to say. The
-- 'detectOpenChains' check is kept around as documentation but
-- the lemma fires unconditionally when chain events exist.
makeAutoSourcesLemma :: Protocol -> Maybe String
makeAutoSourcesLemma p
  | hasAnyChain p = Just sourcesLemmaSrc
  | otherwise     = Nothing
  where
    -- A protocol has chain events whenever any step does both
    -- a `new n` and a `send` mentioning `n`. This is the same
    -- condition Clementine.LowerSapic.computeChainEvents uses.
    hasAnyChain proto =
      any stepHasChain (protoSteps proto)

    stepHasChain s =
      let body     = stepBody s
          freshes  = [ n | SNew n _ <- body ]
          sentVars = foldr (\stmt acc -> case stmt of
                              SSend e _ -> collectVarsExpr e <> acc
                              _         -> acc)
                           []
                           body
      in  any (`elem` sentVars) freshes

    sourcesLemmaSrc = unlines
      [ "// Auto-generated sources lemma (Clementine §5)."
      , "//"
      , "// Asserts that every wire message bound at a ChainSnk"
      , "// event was either learned by the adversary (via KU) or"
      , "// originated from a matching ChainSrc earlier in the"
      , "// trace. The whole-message form (rather than per-variable)"
      , "// lets Tamarin's matcher unify the wire term directly,"
      , "// which incidentally connects the sender-side fresh and"
      , "// the receiver-side pat-bound name (they end up at the"
      , "// same position inside the unified term)."
      , "//"
      , "// This is the same pattern as Tamarin's hand-written NSL"
      , "// sources lemma in examples/classic/NSLPK3.spthy:103-118."
      , "lemma auto_sources [sources]:"
      , "  all-traces"
      , "  \"All m #i. ChainSnk(m) @ i ==>"
      , "     (Ex #j. KU(m) @ j & j < i)"
      , "   | (Ex #j. ChainSrc(m) @ j & j < i)\""
      ]

-- | Local helper duplicated from 'Clementine.LowerSapic' to avoid
-- a circular dependency between Sources and LowerSapic. Walks an
-- 'Expr' and returns the list of free variable names.
collectVarsExpr :: Expr -> [T.Text]
collectVarsExpr e = case e of
  EVar n _    -> [n]
  EConst _ _  -> []
  ETup xs _   -> concatMap collectVarsExpr xs
  EApp _ xs _ -> concatMap collectVarsExpr xs
  EExp a b _  -> collectVarsExpr a ++ collectVarsExpr b
