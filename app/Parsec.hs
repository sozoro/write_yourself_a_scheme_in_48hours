{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}

module Main where

import GHC.Base (Alternative,(<|>),many,empty)
-- import Control.Applicative ((<|>),many,empty)
-- import Control.Monad
import Control.Monad.Cont
-- import Control.Monad.Error (throwError)
-- import Control.Monad.State.Strict
-- import Control.Monad.Trans.Writer.CPS
import Data.Char (ord)
import Data.Functor (void)
import Data.Functor.Identity
-- import Data.Ratio ((%))
import Numeric -- (readOct,readHex)
import System.Environment (getArgs)
import Text.Parsec (Parsec,ParsecT(..),runParserT,Stream,modifyState)
-- import Text.Parsec.Prim (Parsec,ParsecT(..))
import Text.ParserCombinators.Parsec hiding (spaces,(<|>),many)
import Text.ParserCombinators.ReadP (readP_to_S)
import Text.Read.Lex (readIntP)

data LispVal = Atom       String
             | List       [LispVal]
             | DottedList [LispVal] LispVal
             | Number     Integer
             | Float      Float
             | Double     Double
             | Rational   Rational
             | Character  Char
             | String     String
             | Bool       Bool
             deriving (Show,Eq)

{-
-- generalized (catMaybes :: [Maybe a] -> [a])
mcatFoldables :: (MonadPlus m, Foldable f) => m (f a) -> m a
mcatFoldables = (>>= foldr (mplus . return) mzero)
-}

cantConsumeMore :: Stream s m a => ParsecT s u m a -> ParsecT s u m ()
cantConsumeMore more = join $ (lookAhead more >> return empty) <|> return (pure ())

symbol :: Monad m => ParsecT String u m Char
symbol = oneOf "!#$%&|*+-/:<=>?@^_~"

atomHeadChar :: Monad m => ParsecT String u m Char
atomHeadChar = letter <|> symbol

atomTailChar :: Monad m => ParsecT String u m Char
atomTailChar = letter <|> symbol <|> digit

spaces :: Monad m => ParsecT String u m ()
spaces = skipMany1 space

parseString :: Monad m => ParsecT String u m String
parseString = char '\"' >> parseString'
  where
    parseString' :: Monad m => ParsecT String u m String
    parseString' = do
      str <- many $ noneOf "\"\\"
      anyChar >>= \case
        '\"' -> return str
        '\\' -> do
          let f (c, c') = char c >> (str ++) . (c' :) <$> parseString'
          foldr (\a b -> f a <|> b) empty
            [ ('\"', '\"')
            , ('\'', '\'')
            , ('\\', '\\')
            , ('a' , '\a')
            , ('b' , '\b')
            , ('n' , '\n')
            , ('r' , '\r')
            , ('f' , '\f')
            , ('t' , '\t')
            , ('v' , '\v')
            ]

readBin :: (Eq a, Num a) => ReadS a
readBin = readP_to_S $ readIntP 2 isDigit valDigit
  where
    isDigit  = maybe False (const True) . valDig2
    valDigit = maybe 0     id           . valDig2
    valDig2 c | '0' <= c && c <= '1' = Just (ord c - ord '0')
              | otherwise            = Nothing

parseBinNumber :: Monad m => ParsecT String u m Integer
parseBinNumber = fmap (fst . head . readBin) $ many1 $ oneOf ['0'..'1']

parseOctNumber :: Monad m => ParsecT String u m Integer
parseOctNumber = fmap (fst . head . readOct) $ many1 $ oneOf ['0'..'7']

getDecString :: Monad m => ParsecT String u m String
getDecString = do
  sign <- Just <$> char '-' <|> return Nothing
  void (char '+') <|> return ()
  maybe id (:) sign <$> many1 digit

parseDecNumber :: Monad m => ParsecT String u m Integer
parseDecNumber = read <$> getDecString

parseHexNumber :: Monad m => ParsecT String u m Integer
parseHexNumber = fmap (fst . head . readHex) $ many1 $ digit <|> oneOf ['a'..'f']
                                                             <|> oneOf ['A'..'F']

parseAtomTail :: Monad m => ParsecT String u m String
parseAtomTail = many atomTailChar

parseHashPrefix :: Monad m => ParsecT String u m LispVal
parseHashPrefix = char '#' >> (letter <|> symbol <|> digit) >>= \case
  't'  -> return $ Bool True
  'f'  -> return $ Bool False
  'b'  -> Number    <$> parseBinNumber
  'o'  -> Number    <$> parseOctNumber
  'd'  -> Number    <$> parseDecNumber
  'x'  -> Number    <$> parseHexNumber
  '\\' -> Character <$> anyChar
  c    -> Atom . (['#', c] ++) <$> parseAtomTail

parseAtom :: Monad m => ParsecT String u m String
parseAtom = atomHeadChar >>= \he -> (he :) <$> parseAtomTail

parseAsAtom :: String -> Parser LispVal
parseAsAtom pre = atomTailChar >>= \he ->
                  Atom . (pre ++) . (he :) <$> parseAtomTail

{-
parseExponentPart :: (Monad m, Fractional r, Read r)
                  => (r -> LispVal) -> PendingParser m LispVal
parseExponentPart defaultReal = do
  precision     <- lift $ oneOf "fde"
  exponentPart  <- lift $ getDecString
  appendToState $ 'e' : exponentPart
  floatingPoint <- getState
  return $ case precision of
    'f' -> Float       $ read floatingPoint
    'd' -> Double      $ read floatingPoint
    'e' -> defaultReal $ read floatingPoint

parseReal :: (Monad m, Fractional r, Read r)
          => (r -> LispVal) -> PendingParser m LispVal
parseReal defaultReal =
      parseExponentPart defaultReal
  <|> do
      char '.'
      fractionalPart <- many1 digit
      appendToState $ '.' : fractionalPart
      real <- getState
      choice
        [ parseExponentPart defaultReal
        , return $ defaultReal $ read real
        ]

parseRational :: Monad m => PendingParser m LispVal
parseRational = do
  char '/'
  denominator <- many1 digit
  appendToState $ '%' : denominator
  ratio <- getState
  return $ Rational $ read ratio

parseNumeric :: (Monad m, Fractional r, Read r)
             => (r -> LispVal) -> ParsecT String () m LispVal
parseNumeric defaultReal = getDecString >>= \decimal -> do
  initPendingParser
  choice
  [ parseReal defaultReal decimal
  , parseRational decimal
  , return $ Number $ read decimal
  ]

parseInfNan :: (Fractional r, Read r) => (r -> LispVal) -> Parser LispVal
parseInfNan defaultReal = fmap defaultReal $ choice $ try <$>
  [ string "+inf.0" >> return (1 / 0)
  , string "-inf.0" >> return (-1 / 0)
  , string "+nan.0" >> return (0 / 0)
  ]

parseExpr :: Monad m => ParsecT String u m LispVal
parseExpr = choice
  [ try parseHashPrefix
  , String <$> parseString
  , parseNumeric defaultReal
  , parseInfNan  defaultReal
  , Atom   <$> parseAtom
  ]
  where
    defaultReal = Double
-}

{-
testParser :: ParsecT String u (Cont r) String
testParser = do
  callCC $ \cc -> do
    char 'a'
    return ""
    cc ""
  char 'b' >> return "ok"
-}

{-
testParser :: ParsecT String u Identity String
testParser = flip runContT return testParser'
  where
    testParser' :: ContT r (ParsecT String u Identity) String
    testParser' = do
      callCC $ \cc -> do
        lift $ char 'a'
        lift $ char 'b'
        when True $ cc ""
        return "ab"
      lift $ char 'a' >> return "ok"
      -- lift $  (char 'a' >> char 'b' >> return "ab")
      --     <|> fmap ("many: " ++) (many letter)
-}

testParser :: ParsecT String u Identity String
testParser = try (matchAB <* cantConsumeMore letter) <|> matchLetters
  where
    matchAB      = char 'a' >> char 'b' >> return "ab"
    matchLetters = fmap ("many: " ++) (many letter)

withStatus :: Monad m => ParsecT s u m a -> ParsecT s u m (SourcePos, s, a)
withStatus parser = do
  a <- parser
  p <- getPosition
  i <- getInput
  return (p, i, a)

withRem :: Monad m => ParsecT s u m a -> ParsecT s u m (a, s)
withRem parser = (,) <$> parser <*> getInput

readExpr :: String -> String
--readExpr input = case runCont (runParserT (withRem testParser) () "lisp" input) id of
readExpr input = case runIdentity (runParserT (withRem testParser) () "lisp" input) of
  Left err  -> "No match in "  ++ show err
  Right val -> "Found value: " ++ show val

main :: IO ()
main = do
  (expr:_) <- getArgs
  putStrLn $ readExpr expr
  -- parseTest parseExpr expr

-- main = undefined
