-- {-# LANGUAGE LambdaCase #-}
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
import Control.Monad (MonadPlus,mzero,mplus)
import Control.Monad.Trans
import Control.Monad.State.Strict (StateT,evalStateT,modify,get)
import Data.Complex
import Data.Functor (void)
import Data.Functor.Identity
import qualified Data.List.NonEmpty as NE
import Data.Void (Void)
import Data.Ratio (Ratio,(%))
import System.Environment (getArgs)

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

binNumOpR :: forall rc. (forall a. Num a => a -> a -> CanBeComplex rc a)
          -> Number 'R -> Number 'R -> Number rc
binNumOpR op a b = match (upcast upper a) (upcast upper b)
  where
    upper = max (conversionOrder a) (conversionOrder b)
    match :: Number 'R -> Number 'R -> Number rc
    match (Integer  (CBReal x)) (Integer  (CBReal y)) = Integer  $ x `op` y
    match (Rational (CBReal x)) (Rational (CBReal y)) = Rational $ x `op` y
    match (Float    (CBReal x)) (Float    (CBReal y)) = Float    $ x `op` y
    match (Double   (CBReal x)) (Double   (CBReal y)) = Double   $ x `op` y
    match _ _ = error "binNumOpR: match: upcast is broken"

binNumOpC :: forall rc. (forall a. Num a => Complex a -> Complex a -> CanBeComplex rc a)
          -> Number 'C -> Number 'C -> Number rc
binNumOpC op a b = match (upcast upper a) (upcast upper b)
  where
    upper = max (conversionOrder a) (conversionOrder b)
    match :: Number 'C -> Number 'C -> Number rc
    match (Integer  (CBComp x)) (Integer  (CBComp y)) = Integer  $ x `op` y
    match (Rational (CBComp x)) (Rational (CBComp y)) = Rational $ x `op` y
    match (Float    (CBComp x)) (Float    (CBComp y)) = Float    $ x `op` y
    match (Double   (CBComp x)) (Double   (CBComp y)) = Double   $ x `op` y
    match _ _ = error "binNumOpR: match: upcast is broken"

data LispVal = Atom       String
             | List       [LispVal]
             | DottedList [LispVal] LispVal
             | Real       (Number 'R)
             | Complex    (Number 'C)
             | Character  Char
             | String     String
             | Bool       Bool
             deriving (Show,Eq)

maybeReal :: LispVal -> Maybe (Number 'R)
maybeReal (Real r) = Just r
maybeReal _        = Nothing

integral :: Integer -> LispVal
integral = Real . Integer . CBReal

rational :: Rational -> LispVal
rational = Real . Rational . CBReal

float :: Float -> LispVal
float = Real . Float . CBReal

double :: Double -> LispVal
double = Real . Double . CBReal

type Parser = ParsecT Void String Identity

sc :: Parser ()
sc = L.space space1 (L.skipLineComment ";") (L.skipBlockComment "#|" "|#")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

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
    , ('b' , integral  <$> signed L.binary)
    , ('o' , integral  <$> signed L.octal)
    , ('d' , integral  <$> signed L.decimal)
    , ('x' , integral  <$> signed L.hexadecimal)
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
    , get >>= return . integral . read
    ]

parseComplex :: (Fractional r, Read r) => (r -> LispVal) -> Parser LispVal
parseComplex defaultReal = parseReal defaultReal >>= \real -> do
      imag <- parseReal defaultReal
      char 'i'
      maybe empty return $ do
        r <- maybeReal real
        i <- maybeReal imag
        return $ Complex $ binNumOpR (\r' i' -> CBComp $ r' :+ i') r i
  <|> return real

parseInfNan :: (Fractional r, Read r) => (r -> LispVal) -> Parser LispVal
parseInfNan defaultReal = defaultReal <$> choice
  [ string "+inf.0" >> return ( 1 / 0)
  , string "-inf.0" >> return (-1 / 0)
  , string "+nan.0" >> return ( 0 / 0)
  ]

whileNotAtom :: Parser a -> Parser a
whileNotAtom parser = try $ parser <* notFollowedBy atomTailChar

parseExpr :: Parser LispVal
parseExpr = choice
  [ whileNotAtom $ parseHashPrefix
  , whileNotAtom $ parseComplex defaultReal
  , whileNotAtom $ parseInfNan  defaultReal
  , String <$> parseString
  , Atom   <$> parseAtom
  ]
  where
    defaultReal = double

withRem :: MonadParsec e s m => m a -> m (a, s)
withRem parser = (,) <$> parser <*> getInput

readExpr :: String -> String
readExpr input =
  case runIdentity (runParserT (withRem @Void parseExpr) "lisp" input) of
    Left err  -> "No match in "  ++ errorBundlePretty err
    Right val -> "Found value: " ++ show val

main :: IO ()
main = do
  (expr:_) <- getArgs
  putStrLn $ readExpr expr

-- main = undefined
