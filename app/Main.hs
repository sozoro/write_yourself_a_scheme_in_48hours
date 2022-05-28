{-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE BlockArguments #-}
-- {-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Applicative (Alternative,(<|>),empty)
-- import Control.Arrow (first,second)
import Control.Monad (MonadPlus,mzero,mplus)
-- import Control.Monad.Except
import Control.Monad.IO.Class (MonadIO,liftIO)
import Control.Monad.Trans
import Control.Monad.State.Strict (StateT,evalStateT,modify,get)
import Data.Bifunctor (first,second)
import Data.Complex
import Data.Functor (void)
import Data.Functor.Identity
import qualified Data.List.NonEmpty as NE
import Data.Maybe (listToMaybe)
import Data.Void (Void)
import Data.Ratio (Ratio,(%),numerator,denominator)
import System.Environment (getArgs)
import System.IO (hFlush,stdout)

import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer         as L
import qualified Control.Monad.Combinators.NonEmpty as NE

{-
-- generalized (catMaybes :: [Maybe a] -> [a])
mcatFoldables :: (MonadPlus m, Foldable f) => m (f a) -> m a
mcatFoldables = (>>= foldr (mplus . return) mzero)
-}

data RC = R | C deriving (Show,Eq)

data CanBeComplex :: RC -> * -> * where
  CBReal :: a         -> CanBeComplex 'R a
  CBComp :: Complex a -> CanBeComplex 'C a

deriving instance Show a => Show (CanBeComplex rc a)
deriving instance Eq   a => Eq   (CanBeComplex rc a)
deriving instance Functor (CanBeComplex rc)

data Number :: RC -> * where
  Integer  :: CanBeComplex rc Integer  -> Number rc
  Rational :: CanBeComplex rc Rational -> Number rc
  Float    :: CanBeComplex rc Float    -> Number rc
  Double   :: CanBeComplex rc Double   -> Number rc

deriving instance Show (Number rc)
deriving instance Eq   (Number rc)

conversionOrder :: Number rc -> Int
conversionOrder (Integer  _) = 0
conversionOrder (Rational _) = 1
conversionOrder (Float    _) = 2
conversionOrder (Double   _) = 3

upcast :: Int -> Number rc -> Number rc
upcast to num | let from = conversionOrder num in from == to = num
upcast 1 (Integer  i) = Rational $ fromIntegral <$> i
upcast 2 (Integer  i) = Float    $ fromIntegral <$> i
upcast 3 (Integer  i) = Double   $ fromIntegral <$> i
upcast 2 (Rational r) = Float    $ realToFrac   <$> r
upcast 3 (Rational r) = Double   $ realToFrac   <$> r
upcast 3 (Float    f) = Double   $ realToFrac   <$> f
upcast _ _            = error "upcast: down casting"

binOpNumR :: forall rc. (forall a. Num a => a -> a -> CanBeComplex rc a)
          -> Number 'R -> Number 'R -> Number rc
binOpNumR op a b = match (upcast upper a) (upcast upper b)
  where
    upper = max (conversionOrder a) (conversionOrder b)
    match :: Number 'R -> Number 'R -> Number rc
    match (Integer  (CBReal x)) (Integer  (CBReal y)) = Integer  $ x `op` y
    match (Rational (CBReal x)) (Rational (CBReal y)) = Rational $ x `op` y
    match (Float    (CBReal x)) (Float    (CBReal y)) = Float    $ x `op` y
    match (Double   (CBReal x)) (Double   (CBReal y)) = Double   $ x `op` y
    match _ _ = error "binOpNumR: match: upcast is broken"

binOpNumC :: forall rc. (forall a. Num a => Complex a -> Complex a -> CanBeComplex rc a)
          -> Number 'C -> Number 'C -> Number rc
binOpNumC op a b = match (upcast upper a) (upcast upper b)
  where
    upper = max (conversionOrder a) (conversionOrder b)
    match :: Number 'C -> Number 'C -> Number rc
    match (Integer  (CBComp x)) (Integer  (CBComp y)) = Integer  $ x `op` y
    match (Rational (CBComp x)) (Rational (CBComp y)) = Rational $ x `op` y
    match (Float    (CBComp x)) (Float    (CBComp y)) = Float    $ x `op` y
    match (Double   (CBComp x)) (Double   (CBComp y)) = Double   $ x `op` y
    match _ _ = error "binOpNumR: match: upcast is broken"

data LispVal = Atom       String
             | List       [LispVal]
             | DottedList [LispVal] LispVal
             | Real       (Number 'R)
             | Complex    (Number 'C)
             | Character  Char
             | String     String
             | Bool       Bool
             deriving (Show,Eq)

newtype PrettyLispVal = PrettyLispVal { unPrettyLispVal :: LispVal } deriving Eq

unwordsList :: [LispVal] -> String
unwordsList = unwords . fmap (show . PrettyLispVal)

instance Show PrettyLispVal where
  show = showVal . unPrettyLispVal
    where
      showVal :: LispVal -> String
      showVal (Atom       name)  = name
      showVal (String     str)   = "\"" ++ str ++ "\""
      showVal (Real       r)     = showReal r
      showVal (Complex    c)     = show c -- TODO
      showVal (Bool       True)  = "#t"
      showVal (Bool       False) = "#f"
      showVal (List       ls)    = "(" ++ unwordsList ls ++ ")"
      showVal (DottedList hd tl) = "(" ++ unwordsList hd ++ " . " ++ showVal tl ++ ")"

      showReal :: Number 'R -> String
      showReal (Integer  (CBReal i)) = show i
      showReal (Rational (CBReal r)) = show (numerator r) ++ "/" ++ show (denominator r)
      showReal (Float    (CBReal f)) = show f
      showReal (Double   (CBReal d)) = show d

maybeReal :: LispVal -> Maybe (Number 'R)
maybeReal (Real r) = Just r
maybeReal _        = Nothing

integer :: Integer -> LispVal
integer = Real . Integer . CBReal

rational :: Rational -> LispVal
rational = Real . Rational . CBReal

float :: Float -> LispVal
float = Real . Float . CBReal

double :: Double -> LispVal
double = Real . Double . CBReal

type Parser      = ParsecT Void String Identity
type ParserError = ParseErrorBundle String Void

skipLineComment :: Parser ()
skipLineComment = L.skipLineComment ";"

skipBlockComment :: Parser ()
skipBlockComment = L.skipBlockComment "#|" "|#"

sc :: Parser ()
sc = L.space space1 skipLineComment skipBlockComment

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

signed :: Num a => Parser a -> Parser a
signed = L.signed sc

lispSymbolChar :: Parser Char
lispSymbolChar = label "lisp symbol" $ oneOf "!#$%&|*+-/:<=>?@^_~"

atomHeadChar :: Parser Char
atomHeadChar = letterChar <|> lispSymbolChar

atomTailChar :: Parser Char
atomTailChar = alphaNumChar <|> lispSymbolChar

parseString :: Parser String
parseString = char '\"' *> manyTill L.charLiteral (char '\"')

parseAtomTail :: Parser String
parseAtomTail = many atomTailChar

parseAtom :: Parser String
parseAtom = letterChar <|> lispSymbolChar >>= \he -> (he :) <$> parseAtomTail

parseHashPrefix :: Parser LispVal
parseHashPrefix = do
  char '#'
  choice $ (\(c, m) -> char c >> m) <$>
    [ ('t' , return $ Bool True)
    , ('f' , return $ Bool False)
    , ('b' , integer  <$> signed L.binary)
    , ('o' , integer  <$> signed L.octal)
    , ('d' , integer  <$> signed L.decimal)
    , ('x' , integer  <$> signed L.hexadecimal)
    , ('\\', Character <$> anySingle)
    ]

type PendingParser = StateT String Parser

appendToState :: (Monad m, Monoid a) => a -> StateT a m ()
appendToState a = modify $ (<> a) -- lazy

signedDigitsString :: Parser String
signedDigitsString = do
  sign <- Just <$> char '-' <|> return Nothing
  void (char '+') <|> return ()
  maybe id (:) sign <$> some digitChar

parseExponentPart :: (Fractional r, Read r) => (r -> LispVal) -> PendingParser LispVal
parseExponentPart defaultReal = do
  precision     <- lift $ oneOf "fde"
  exponentPart  <- lift $ signedDigitsString
  appendToState $ 'e' : exponentPart
  floatingPoint <- get
  return $ case precision of
    'f' -> float        $ read floatingPoint
    'd' -> double       $ read floatingPoint
    'e' -> defaultReal  $ read floatingPoint

parseFractional :: (Fractional r, Read r) => (r -> LispVal) -> PendingParser LispVal
parseFractional defaultReal = parseExponentPart defaultReal
  <|> do
      lift $ char '.'
      fractionalPart <- lift $ some digitChar
      appendToState $ '.' : fractionalPart
      fractional <- get
      parseExponentPart defaultReal <|> return (defaultReal $ read fractional)

parseRational :: PendingParser LispVal
parseRational = do
  lift $ char '/'
  denominator <- lift $ some digitChar
  appendToState $ '%' : denominator
  ratio <- get
  return $ rational $ read ratio

parseReal :: (Fractional r, Read r) => (r -> LispVal) -> Parser LispVal
parseReal defaultReal = signedDigitsString >>= \signedDigits ->
  choice $ flip evalStateT signedDigits <$>
    [ parseFractional defaultReal
    , parseRational
    , get >>= return . integer . read
    ]

-- TODO: parse dot-start fractional ".4e-1"

parseComplex :: (Fractional r, Read r) => (r -> LispVal) -> Parser LispVal
parseComplex defaultReal = parseReal defaultReal >>= \real -> do
      imag <- parseReal defaultReal
      char 'i'
      maybe empty return $ do
        r <- maybeReal real
        i <- maybeReal imag
        return $ Complex $ binOpNumR (\r' i' -> CBComp $ r' :+ i') r i
  <|> return real

parseInfNan :: (Fractional r, Read r) => (r -> LispVal) -> Parser LispVal
parseInfNan defaultReal = defaultReal <$> choice
  [ string "+inf.0" >> return ( 1 / 0)
  , string "-inf.0" >> return (-1 / 0)
  , string "+nan.0" >> return ( 0 / 0)
  ]

whileNotAtom :: Parser a -> Parser a
whileNotAtom parser = try $ parser <* notFollowedBy atomTailChar

parseList :: Parser LispVal
parseList = between (symbol "(") (char ')') $ sepEndBy parseExpr space1 >>= \head -> do
      char '.' >> space1
      tail <- parseExpr
      return (DottedList head tail)
  <|> return (List head)

appFuncToParsedExpr :: String -> Parser LispVal
appFuncToParsedExpr f = List . (Atom f :) . pure <$> parseExpr

parseQuoted :: Parser LispVal
parseQuoted = char '\'' >> appFuncToParsedExpr "quote"

parseQuasiquoted :: Parser LispVal
parseQuasiquoted = char '`' >> appFuncToParsedExpr "quasiquote"

parseUnquoted :: Parser LispVal
parseUnquoted = char ',' >> do
      char '@' >> appFuncToParsedExpr "unquote-splicing"
  <|> appFuncToParsedExpr "unquote"

parseExpr :: Parser LispVal
parseExpr = choice
  [ whileNotAtom $ parseHashPrefix
  , whileNotAtom $ parseComplex defaultReal
  , whileNotAtom $ parseInfNan  defaultReal
  , Atom   <$> parseAtom
  , String <$> parseString
  , parseQuoted
  , parseQuasiquoted
  , parseUnquoted
  , parseList
  ]
  where
    defaultReal = double

withRem :: MonadParsec e s m => m a -> m (a, s)
withRem parser = (,) <$> parser <*> getInput

data LispError = NumArgs String Integer [LispVal]
               | TypeMismatch String String LispVal
               | Parser ParserError
               | BadSpecialForm String LispVal
               | NotFunction String String
               | UnboundVar String String
               | Default String

instance Show LispError where
  show (UnboundVar message varname)  = message ++ ": " ++ varname
  show (BadSpecialForm message form) = message ++ ": " ++ show (PrettyLispVal form)
  show (NotFunction message func)    = message ++ ": " ++ show func
  show (NumArgs func expected found) = "Function "               ++ show func
                                    ++ " expects "               ++ show expected
                                    ++ " args; but applied to: " ++ unwordsList found
  show (TypeMismatch fnc expctd fnd) = "Invalid type in "  ++ show fnc
                                    ++ "; expected "       ++ expctd
                                    ++ ", but found arg: " ++ show (PrettyLispVal fnd)
  show (Parser parserErr)            = "Parse error:\n" ++ errorBundlePretty parserErr

type LispErrOrVal = Either LispError LispVal

readExpr :: String -> LispErrOrVal
readExpr input =
  first Parser $ runIdentity $ runParserT (parseExpr <* (sc >> eof)) "" input

eval :: LispErrOrVal -> LispErrOrVal
eval ev = ev >>= eval'
  where
    eval' :: LispVal -> LispErrOrVal
    eval' (List [Atom "quote"     , val]) = return val
    eval' (List [Atom "quasiquote", val]) = return val
    eval' (List (Atom func : args))       = traverse eval' args >>= apply func
    eval' (Atom name)                     = return $ String $ "Atom: " ++ name
    eval' val                             = return val

apply :: String -> [LispVal] -> LispErrOrVal
apply func args = maybe (Left $ NotFunction "Unrecognized primitive function " func)
                        ($ args)
                        $ lookup func primitives

primitives :: [(String, [LispVal] -> LispErrOrVal)]
primitives = (\(name, func) -> (name, func name)) <$>
  [ ("boolean?"      , isLispBool)
  , ("string?"       , isLispString)
  , ("char?"         , isLispCharacter)
  , ("list?"         , isLispList)
  , ("pair?"         , isLispDottedList)
  , ("symbol?"       , isLispSymbol)
  , ("not"           , notLispBool)
  , ("null?"         , isNullLispList)
  , ("symbol->string", symbol2String)
  , ("string->symbol", string2Symbol)
  , ("+"             , realBinOp (+) 0)
  , ("-"             , realBinOp (-) 0)
  , ("*"             , realBinOp (*) 1)
  ]

type LispFunction = String -> [LispVal] -> LispErrOrVal

isLispBool :: LispFunction
isLispBool _    [Bool _] = return $ Bool True
isLispBool _    [_]      = return $ Bool False
isLispBool name args     = Left   $ NumArgs name 1 args

isLispString :: LispFunction
isLispString _    [String _] = return $ Bool True
isLispString _    [_]        = return $ Bool False
isLispString name args       = Left   $ NumArgs name 1 args

isLispCharacter :: LispFunction
isLispCharacter _    [Character _] = return $ Bool True
isLispCharacter _    [_]           = return $ Bool False
isLispCharacter name args          = Left   $ NumArgs name 1 args

isLispList :: LispFunction
isLispList _    [List _] = return $ Bool True
isLispList _    [_]      = return $ Bool False
isLispList name args     = Left   $ NumArgs name 1 args

isLispDottedList :: LispFunction
isLispDottedList _    [DottedList _ _] = return $ Bool True
isLispDottedList _    [_]              = return $ Bool False
isLispDottedList name args             = Left   $ NumArgs name 1 args

isLispSymbol :: LispFunction
isLispSymbol _    [Atom _] = return $ Bool True
isLispSymbol _    [_]      = return $ Bool False
isLispSymbol name args     = Left   $ NumArgs name 1 args

notLispBool :: LispFunction
notLispBool _    [Bool True ] = return $ Bool False
notLispBool _    [Bool False] = return $ Bool True
notLispBool name [_]          = return $ Bool False
notLispBool name args         = Left   $ NumArgs name 1 args

isNullLispList :: LispFunction
isNullLispList _    [List []] = return $ Bool True
isNullLispList name [_]       = return $ Bool False
isNullLispList name args      = Left   $ NumArgs name 1 args

symbol2String :: LispFunction
symbol2String _    [Atom name] = return $ String name
symbol2String name [arg]       = Left   $ TypeMismatch name "symbol" arg
symbol2String name args        = Left   $ NumArgs name 1 args

string2Symbol :: LispFunction
string2Symbol _    [String str] = return $ Atom str
string2Symbol name [arg]        = Left   $ TypeMismatch name "string" arg
string2Symbol name args         = Left   $ NumArgs name 1 args

realBinOp :: forall rc. (forall a. Num a => a -> a -> a) -> Integer -> LispFunction
realBinOp op init name args =
  Real . foldl (binOpNumR $ \x y -> CBReal $ x `op` y) (Integer $ CBReal init)
  <$> traverse (unpackReal name) args

unpackReal :: String -> LispVal -> Either LispError (Number 'R)
unpackReal _    (Real r) = return r
unpackReal func arg      = Left $ TypeMismatch func "real number" arg
{- Dynamic
unpackReal (String str)  = either (const $ Integer $ CBReal 0) unpackReal $ readExpr str
unpackReal (Character c) = either (const $ Integer $ CBReal 0) unpackReal $ readExpr [c]
unpackReal (List [val])  = unpackReal val
unpackReal _             = Integer $ CBReal 0
-}

printLispErrOrVal :: LispErrOrVal -> IO ()
printLispErrOrVal = putStrLn . either show (show . PrettyLispVal)

repl :: IO ()
repl = do
  putStrLn "~~~ Scheme REPL ~~~"
  loop
  where
    loop = do
      val  <- readExpr          <$> (putStr "> " >> hFlush stdout >> getLine)
      val' <- eval              <$> return val
      _    <- printLispErrOrVal  $  val'
      loop

main :: IO ()
main = listToMaybe <$> getArgs >>= maybe repl (printLispErrOrVal . eval . readExpr)

-- main = undefined
