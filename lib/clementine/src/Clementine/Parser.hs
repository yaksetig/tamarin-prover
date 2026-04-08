-- |
-- Module      : Clementine.Parser
-- Copyright   : (c) 2026 Clementine contributors
-- License     : GPL v3 (see LICENSE)
--
-- Parser for Clementine surface syntax (.clem files).
--
-- This is the v0.0 cut: it handles enough of the language to parse the
-- ISO-DH worked example from design step 4. It uses parsec directly
-- (matching Sapic's choice of parser library) with a hand-rolled
-- lexeme layer rather than 'Text.Parsec.Token'.
module Clementine.Parser
  ( parseProtocol
  , parseProtocolFile
  , ParseError
  ) where

import           Control.Monad      (void)
import           Data.Functor       (($>))
import           Data.Text          (Text)
import qualified Data.Text          as T
import qualified Data.Text.IO       as T

import           Text.Parsec        hiding (ParseError)
import qualified Text.Parsec        as P
import           Text.Parsec.Text   (Parser)

import           Clementine.AST

-- | Parse errors are re-exported as a stable type so callers do not
-- have to depend on parsec directly.
type ParseError = P.ParseError

-- | Parse a complete .clem file from disk.
parseProtocolFile :: FilePath -> IO (Either ParseError Protocol)
parseProtocolFile fp = do
  src <- T.readFile fp
  pure $ parseProtocol fp src

-- | Parse a Clementine protocol from a 'Text' source.
parseProtocol :: FilePath -> Text -> Either ParseError Protocol
parseProtocol = parse (whiteSpace *> protocolP <* eof)

--------------------------------------------------------------------------------
-- Whitespace and lexemes
--------------------------------------------------------------------------------

-- | Skip whitespace and line/block comments.
whiteSpace :: Parser ()
whiteSpace = skipMany (skipMany1 (oneOf " \t\r\n") <|> lineComment <|> blockComment)
  where
    lineComment  = try (string "//") *> skipMany (noneOf "\n") $> ()
    blockComment = try (string "/*") *> manyTill anyChar (try (string "*/")) $> ()

lexeme :: Parser a -> Parser a
lexeme p = p <* whiteSpace

symbol :: String -> Parser String
symbol s = lexeme (try (string s))

-- | A reserved keyword: a literal that is not part of an identifier.
keyword :: String -> Parser ()
keyword s = lexeme . try $ string s *> notFollowedBy idChar

-- Punctuation helpers
lparen, rparen, lbrace, rbrace, langle, rangle, comma, semi, equalsP, colon :: Parser ()
lparen  = void (symbol "(")
rparen  = void (symbol ")")
lbrace  = void (symbol "{")
rbrace  = void (symbol "}")
langle  = void (symbol "<")
rangle  = void (symbol ">")
comma   = void (symbol ",")
semi    = void (symbol ";")
equalsP = void (symbol "=")
colon   = void (symbol ":")

--------------------------------------------------------------------------------
-- Identifiers
--------------------------------------------------------------------------------

idStart, idChar :: Parser Char
idStart = letter   <|> char '_'
idChar  = alphaNum <|> char '_'

-- The reserved word set. We keep this small; identifier collisions
-- with primops are caught by the expression parser.
reserved :: [String]
reserved =
  [ "protocol", "builtins"
  , "principal", "generates", "knows", "public", "private"
  , "step", "local"
  , "new", "let", "require", "send", "claim", "secret"
  , "verify"
  , "executable", "secrecy", "forward_secrecy"
  , "injective_agreement", "non_injective_agreement", "authentication"
  ]

ident :: Parser Text
ident = lexeme . try $ do
  c <- idStart
  cs <- many idChar
  let s = c : cs
  if s `elem` reserved
    then unexpected ("reserved word " ++ show s)
    else pure (T.pack s)

-- An "uppercase" identifier (principal/role name). For v0.0 we do not
-- enforce the case distinction; this is just a synonym.
upperIdent :: Parser Text
upperIdent = ident

--------------------------------------------------------------------------------
-- Source position helper
--------------------------------------------------------------------------------

withPos :: Parser (SrcPos -> a) -> Parser a
withPos p = do
  pos <- getPosition
  let sp = SrcPos
        { spFile = sourceName pos
        , spLine = sourceLine pos
        , spCol  = sourceColumn pos
        }
  ($ sp) <$> p

--------------------------------------------------------------------------------
-- Top-level protocol
--------------------------------------------------------------------------------

protocolP :: Parser Protocol
protocolP = withPos $ do
  keyword "protocol"
  name <- ident
  lbrace
  bs <- option [] (try builtinsP)
  ps <- many (try principalP)
  ss <- many (try stepP)
  vs <- option [] (try verifyP)
  rbrace
  pure $ \pos -> Protocol
    { protoName       = name
    , protoBuiltins   = bs
    , protoPrincipals = ps
    , protoSteps      = ss
    , protoVerify     = vs
    , protoPos        = pos
    }

--------------------------------------------------------------------------------
-- Builtins
--------------------------------------------------------------------------------

builtinsP :: Parser [Builtin]
builtinsP = do
  keyword "builtins"
  lbrace
  bs <- builtinName `sepBy` comma
  rbrace
  pure bs
  where
    builtinName = choice
      [ symbol "diffie_hellman"        $> BIDH
      , symbol "signing"               $> BISigning
      , symbol "hashing"               $> BIHashing
      , symbol "symmetric_encryption"  $> BISymEnc
      , symbol "asymmetric_encryption" $> BIAsymEnc
      ]

--------------------------------------------------------------------------------
-- Principal blocks
--------------------------------------------------------------------------------

principalP :: Parser Principal
principalP = withPos $ do
  keyword "principal"
  name <- upperIdent
  lbrace
  ks <- many knowledgeP
  rbrace
  pure $ \pos -> Principal
    { prinName  = name
    , prinKnows = ks
    , prinPos   = pos
    }

knowledgeP :: Parser Knowledge
knowledgeP = choice
  [ try generatesK
  , try knowsPublicK
  , try knowsPrivateK
  ]
  where
    generatesK = withPos $ do
      keyword "generates"
      n <- ident
      pure (KGenerates n)

    knowsPublicK = withPos $ do
      keyword "knows"
      keyword "public"
      n <- ident
      mEq <- optionMaybe (equalsP *> exprP)
      pure (KKnowsPublic n mEq)

    knowsPrivateK = withPos $ do
      keyword "knows"
      keyword "private"
      n <- ident
      pure (KKnowsPrivate n)

--------------------------------------------------------------------------------
-- Steps
--------------------------------------------------------------------------------

stepP :: Parser Step
stepP = withPos $ do
  keyword "step"
  lbl <- ident
  colon
  from <- upperIdent
  kind <- stepKindP
  lbrace
  body <- many stepStmtP
  rbrace
  pure $ \pos -> Step
    { stepLabel = lbl
    , stepFrom  = from
    , stepKind  = kind
    , stepBody  = body
    , stepPos   = pos
    }

stepKindP :: Parser StepKind
stepKindP = choice
  [ try (keyword "local" $> StepLocal)
  , networkArrow
  ]
  where
    networkArrow = do
      ck <- choice
        [ try (symbol "->") $> ChNet
        , try (symbol "~>") $> ChAuth
        , try (symbol "=>") $> ChConf
        , try (symbol ":>") $> ChSecure
        ]
      target <- upperIdent
      pure (StepNetwork target ck)

stepStmtP :: Parser StepStmt
stepStmtP = (choice
    [ try newStmt
    , try letStmt
    , try requireStmt
    , try sendStmt
    , try claimStmt
    ]) <* optional semi
  where
    newStmt = withPos $ do
      keyword "new"
      n <- ident
      pure (SNew n)

    letStmt = withPos $ do
      keyword "let"
      n <- ident
      equalsP
      e <- exprP
      pure (SLet n e)

    requireStmt = withPos $ do
      keyword "require"
      e <- exprP
      pure (SRequire e)

    sendStmt = withPos $ do
      keyword "send"
      e <- exprP
      pure (SSend e)

    claimStmt = withPos $ do
      keyword "claim"
      keyword "secret"
      lparen
      n <- ident
      rparen
      pure (SClaim (ClaimSecret n))

--------------------------------------------------------------------------------
-- Expressions
--
-- Grammar:
--     expr     ::= expExpr
--     expExpr  ::= atom ('^' expExpr)?
--     atom     ::= primCall | tuple | const | ident
--     primCall ::= UPPERID '(' expr (',' expr)* ')'
--     tuple    ::= '<' expr (',' expr)* '>'
--     const    ::= "'" [^']* "'"
--
-- DH exponentiation is right-associative; we don't need anything fancier
-- for v0.0.
--------------------------------------------------------------------------------

exprP :: Parser Expr
exprP = expExprP

expExprP :: Parser Expr
expExprP = do
  pos <- mkPos
  base <- atomP
  rest <- optionMaybe (symbol "^" *> expExprP)
  pure $ case rest of
    Nothing -> base
    Just e2 -> EExp base e2 pos

atomP :: Parser Expr
atomP = choice
  [ try primCallP
  , try tupleP
  , try constP
  , try varP
  ]

primCallP :: Parser Expr
primCallP = do
  pos <- mkPos
  op <- primOpP
  lparen
  args <- exprP `sepBy1` comma
  rparen
  pure (EApp op args pos)

primOpP :: Parser PrimOp
primOpP = lexeme . try $ do
  s <- many1 upper
  case s of
    "ENC"    -> pure OpEnc
    "DEC"    -> pure OpDec
    "AENC"   -> pure OpAEnc
    "ADEC"   -> pure OpADec
    "PK"     -> pure OpPK
    "SIGN"   -> pure OpSign
    "VERIFY" -> pure OpVerify
    "H"      -> pure OpH
    "MAC"    -> pure OpMAC
    other    -> unexpected ("unknown primitive " ++ other)

tupleP :: Parser Expr
tupleP = do
  pos <- mkPos
  langle
  es <- exprP `sepBy1` comma
  rangle
  pure (ETup es pos)

constP :: Parser Expr
constP = do
  pos <- mkPos
  _ <- char '\''
  cs <- many (noneOf "'")
  _ <- char '\''
  whiteSpace
  pure (EConst (T.pack cs) pos)

varP :: Parser Expr
varP = do
  pos <- mkPos
  n <- ident
  pure (EVar n pos)

mkPos :: Parser SrcPos
mkPos = do
  p <- getPosition
  pure SrcPos
    { spFile = sourceName p
    , spLine = sourceLine p
    , spCol  = sourceColumn p
    }

--------------------------------------------------------------------------------
-- Verify block
--------------------------------------------------------------------------------

verifyP :: Parser [Query]
verifyP = do
  keyword "verify"
  lbrace
  qs <- many (queryP <* optional semi)
  rbrace
  pure qs

queryP :: Parser Query
queryP = choice
  [ try executableQ
  , try secrecyQ
  , try forwardSecrecyQ
  , try injAgreeQ
  , try nonInjAgreeQ
  , try authenticationQ
  ]
  where
    executableQ = withPos $ keyword "executable" $> QExecutable

    secrecyQ = withPos $ do
      keyword "secrecy"
      lparen
      t <- termRefP
      rparen
      pure (QSecrecy t)

    forwardSecrecyQ = withPos $ do
      keyword "forward_secrecy"
      lparen
      t <- termRefP
      rparen
      pure (QForwardSecrecy t)

    injAgreeQ = withPos $ do
      keyword "injective_agreement"
      lparen
      a <- upperIdent
      comma
      b <- upperIdent
      comma
      ts <- between (symbol "[") (symbol "]") (termRefP `sepBy1` comma)
      rparen
      pure (QInjAgreement a b ts)

    nonInjAgreeQ = withPos $ do
      keyword "non_injective_agreement"
      lparen
      a <- upperIdent
      comma
      b <- upperIdent
      comma
      ts <- between (symbol "[") (symbol "]") (termRefP `sepBy1` comma)
      rparen
      pure (QNonInjAgreement a b ts)

    authenticationQ = withPos $ do
      keyword "authentication"
      lparen
      a <- upperIdent
      comma
      b <- upperIdent
      rparen
      pure (QAuthentication a b)

termRefP :: Parser TermRef
termRefP = withPos $ do
  -- For v0.0 we only accept the bare form `var`. Qualified forms
  -- (step.var, principal@step.var) are accepted by the grammar but
  -- the principal/step fields stay Nothing.
  n <- ident
  pure (TermRef Nothing Nothing n)
