{-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- {-# LANGUAGE ConstraintKinds #-}

module Main where

import Control.Applicative (Alternative,(<|>),empty)
-- import Control.Arrow (first,second)
import Control.Monad -- (MonadPlus,mzero,mplus)
import qualified Control.Monad.Except as E
import Control.Monad.IO.Class (MonadIO,liftIO)
import Control.Monad.Trans
import Control.Monad.State.Strict -- (StateT,evalStateT,modify,get,MonadState)
import Data.Bifunctor (first,second)
import Data.Complex
import Data.Either (isLeft)
import Data.Functor (void)
import Data.Functor.Identity
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict     as Map
import qualified Data.List.NonEmpty  as NE
import Data.Maybe (listToMaybe,fromMaybe)
import Data.Void (Void)
import Data.Ratio (Ratio,(%),numerator,denominator)
import qualified Debug.Trace as T
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

newtype Primitive = Primitive
  { appPrim :: forall m. E.MonadError LispError m => [LispVal] -> m LispVal }

instance Show Primitive where
  show (Primitive _) = "<primitive>"

data LispVal = Atom          String
             | List          [LispVal]
             | DottedList    [LispVal] LispVal
             | Real          (Number 'R)
             | Complex       (Number 'C)
             | Character     Char
             | String        String
             | Bool          Bool
             | PrimitiveFunc Primitive
             | Func { params    :: [String]
                    , listParam :: Maybe String
                    , body      :: NE.NonEmpty LispVal
                    , closure   :: LispEnv
                    }
             deriving Show

newtype PrettyLispVal = PrettyLispVal { unPrettyLispVal :: LispVal }

unwordsList :: [LispVal] -> String
unwordsList = unwords . fmap (show . PrettyLispVal)

unpackPrimitiveFunc :: LispVal -> Either LispVal Primitive
unpackPrimitiveFunc (PrimitiveFunc prim) = return prim
unpackPrimitiveFunc val                  = Left   val

withoutPrimitive :: LispEnv -> LispEnv
withoutPrimitive = HM.filter (isLeft . unpackPrimitiveFunc)

showLispEnv :: LispEnv -> String
showLispEnv = show . fmap PrettyLispVal . withoutPrimitive

instance Show PrettyLispVal where
  show = showVal . unPrettyLispVal
    where
      showVal :: LispVal -> String
      showVal (Atom       name)    = name
      showVal (String     str)     = "\"" ++ str ++ "\""
      showVal (Real       r)       = showReal r
      showVal (Complex    c)       = show c -- TODO
      showVal (Bool       True)    = "#t"
      showVal (Bool       False)   = "#f"
      showVal (List       ls)      = "(" ++ unwordsList ls ++ ")"
      showVal (DottedList hd tl)   = "(" ++ unwordsList hd ++ " . " ++ showVal tl ++ ")"
      showVal (PrimitiveFunc prim) = show prim
      showVal (Func ps lp bd clsr) = "(lambda (" ++ unwords (show <$> ps)
                                  ++ maybe "" (" . " ++) lp ++ ") ...) "
                                  ++ show (PrettyLispVal <$> withoutPrimitive clsr)

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
parseString = single '\"' *> manyTill L.charLiteral (single '\"')

parseAtomTail :: Parser String
parseAtomTail = many atomTailChar

parseAtom :: Parser String
parseAtom = letterChar <|> lispSymbolChar >>= \he -> (he :) <$> parseAtomTail

parseHashPrefix :: Parser LispVal
parseHashPrefix = do
  single '#'
  choice $ (\(c, m) -> single c >> m) <$>
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
  sign <- Just <$> single '-' <|> return Nothing
  void (single '+') <|> return ()
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
      lift $ single '.'
      fractionalPart <- lift $ some digitChar
      appendToState $ '.' : fractionalPart
      fractional <- get
      parseExponentPart defaultReal <|> return (defaultReal $ read fractional)

parseRational :: PendingParser LispVal
parseRational = do
  lift $ single '/'
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
      single 'i'
      maybe empty return $ do
        r <- maybeReal real
        i <- maybeReal imag
        return $ Complex $ binOpNumR (\r' i' -> CBComp $ r' :+ i') r i
  <|> return real

parseInfNan :: (Fractional r, Read r) => (r -> LispVal) -> Parser LispVal
parseInfNan defaultReal = defaultReal <$> choice
  [ chunk "+inf.0" >> return ( 1 / 0)
  , chunk "-inf.0" >> return (-1 / 0)
  , chunk "+nan.0" >> return ( 0 / 0)
  ]

whileNotAtom :: Parser a -> Parser a
whileNotAtom parser = try $ parser <* notFollowedBy atomTailChar

parseList :: Parser LispVal
parseList = between (symbol "(") (single ')') $ sepEndBy parseExpr space1 >>= \head -> do
      single '.' >> space1
      tail <- parseExpr
      return (DottedList head tail)
  <|> return (List head)

appFuncToParsedExpr :: String -> Parser LispVal
appFuncToParsedExpr f = List . (Atom f :) . pure <$> parseExpr

parseQuoted :: Parser LispVal
parseQuoted = single '\'' >> appFuncToParsedExpr "quote"

parseQuasiquoted :: Parser LispVal
parseQuasiquoted = single '`' >> appFuncToParsedExpr "quasiquote"

parseUnquoted :: Parser LispVal
parseUnquoted = single ',' >> do
      single '@' >> appFuncToParsedExpr "unquote-splicing"
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

data LispError = NumArgs (Maybe String) Integer [LispVal]
               | TypeMismatch String String LispVal
               | Parser ParserError
               | BadSpecialForm String LispVal
               | NotFunction String String
               | UnboundVar String String
               | Default String
               | NonSymbolParam (Maybe String) LispVal

funcName :: Maybe String -> String
funcName = maybe "" (\func -> show func ++ " ")

instance Show LispError where
  show (UnboundVar message varname)  = message ++ ": " ++ varname
  show (BadSpecialForm message form) = message ++ ": " ++ show (PrettyLispVal form)
  show (NotFunction message func)    = message ++ ": " ++ show func
  show (NumArgs func expected found) = "Function " ++ funcName func
                                    ++ "expects " ++ show expected
                                    ++ " args; but applied to: " ++ unwordsList found
  show (TypeMismatch fnc expctd fnd) = "Invalid type in "  ++ show fnc
                                    ++ "; expected "       ++ expctd
                                    ++ ", but found arg: " ++ show (PrettyLispVal fnd)
  show (Parser parserErr)            = "Parse error:\n" ++ errorBundlePretty parserErr
  show (NonSymbolParam func param)   = "Defining function " ++ funcName func
                                    ++ "with non symbol parameter: " ++ show param
  show (Default message)             = message

type WithLispErr a = Either LispError a
type LispErrOrVal  = WithLispErr LispVal

readExpr :: E.MonadError LispError m => String -> m LispVal
readExpr input = either (E.throwError . Parser) return
               $ runParser (parseExpr <* (sc >> eof)) "" input

type LispEnv = HM.HashMap String LispVal

isBound :: MonadState LispEnv m => String -> m Bool
isBound var = HM.member var <$> get

getVar :: (E.MonadError LispError m, MonadState LispEnv m)
       => String -> m LispVal
getVar var = HM.lookup var <$> get >>=
               maybe (E.throwError $ UnboundVar "Getting an unbound variable" var) return

setVar :: (E.MonadError LispError m, MonadState LispEnv m)
       => String -> LispVal -> m LispVal
setVar var val = do
  env <- get
  if HM.member var env then put (HM.insert var val env) >> return val
                       else E.throwError $ UnboundVar "Setting an unbound variable" var

defineVar :: MonadState LispEnv m => String -> LispVal -> m LispVal
defineVar var val = modify (HM.insert var val) >> return val

bindVars :: MonadState LispEnv m => LispEnv -> m ()
-- bindVars closure = modify $ \env -> HM.unionWith (\v _ -> v) env closure
bindVars closure = modify $ \env -> HM.unionWith (\_ v -> v) env closure
-- bindVars ls = modify $ \orig ->
--                 foldr (\(k,v) hm -> HM.alter (Just . fromMaybe v) k hm) orig ls

unpackAtom :: LispVal -> Either LispVal String
unpackAtom (Atom atom) = return atom
unpackAtom val         = Left   val

makeFunc :: (E.MonadError LispError m, MonadState LispEnv m)
         => Maybe String -> [LispVal] -> Maybe LispVal -> NE.NonEmpty LispVal
         -> m LispVal
makeFunc mVar paramVals mListParamVal body = do
  params     <- unpackParams paramVals
  mListParam <- unpackParams mListParamVal
  closure    <- get
  return $ Func params mListParam body closure
  where
    unpackParams :: (E.MonadError LispError m, Traversable t)
                 => t LispVal -> m (t String)
    unpackParams paramVals = either (E.throwError . NonSymbolParam mVar) return
                           $ traverse unpackAtom paramVals

eval :: (E.MonadError LispError m, MonadState LispEnv m) => LispVal -> m LispVal
eval (Atom var)                            = getVar var
eval (List [Atom "quote"     , val])       = return val
eval (List [Atom "quasiquote", val])       = return val
eval (List [Atom "set!"  , Atom var, val]) = eval val >>= setVar    var
eval (List [Atom "define", Atom var, val]) = eval val >>= defineVar var
eval (List [Atom "if", pred, conseq, alt]) = eval pred >>= \case
                                               Bool False -> eval alt
                                               _          -> eval conseq
eval (List (Atom "define" : List         (Atom var : pVals)     : bodyHd : bodyTl)) =
  makeFunc (Just var) pVals Nothing      (bodyHd NE.:| bodyTl) >>= defineVar var
eval (List (Atom "define" : DottedList (Atom var : pVals) lpVal : bodyHd : bodyTl)) =
  makeFunc (Just var) pVals (Just lpVal) (bodyHd NE.:| bodyTl) >>= defineVar var
eval (List (Atom "lambda" : List       pVals       : bodyHd : bodyTl)) =
  makeFunc Nothing    pVals Nothing      (bodyHd NE.:| bodyTl)
eval (List (Atom "lambda" : DottedList pVals lpVal : bodyHd : bodyTl)) =
  makeFunc Nothing    pVals (Just lpVal) (bodyHd NE.:| bodyTl)
eval (List (Atom "lambda" : lpVal@(Atom _)         : bodyHd : bodyTl)) =
  makeFunc Nothing    []    (Just lpVal) (bodyHd NE.:| bodyTl)
eval (List (function : args))              = do
                                               func    <- eval function
                                               argVals <- traverse eval args
                                               func `apply` argVals
eval val                                   = return val

-- return remaining list
zipWith' :: (a -> b -> c) -> [a] -> [b] -> ([c], Either [a] [b])
zipWith' _ [] bs         = ([], Right bs)
zipWith' _ as []         = ([], Left  as)
zipWith' f (a:as) (b:bs) = first (f a b :) $ zipWith' f as bs

zip' :: [a] -> [b] -> ([(a, b)], Either [a] [b])
zip' = zipWith' (,)

onException :: E.MonadError e m => m a -> m b -> m a
onException ma what = ma `E.catchError` \e -> what >> E.throwError e

finally :: E.MonadError e m => m a -> m b -> m a
finally ma sequel = (ma `onException` sequel) <* sequel

-- withTmpState :: (E.MonadError e m, MonadState s m) => s -> m a -> m a
-- withTmpState s ma = do
--   orig <- get
--   put s
--   ma `finally` put orig

apply :: (E.MonadError LispError m, MonadState LispEnv m)
      => LispVal -> [LispVal] -> m LispVal
apply (PrimitiveFunc prim) args = prim `appPrim` args
apply (Func ps lp bd clsr) args = do
  let numArgsErr = E.throwError $ NumArgs Nothing (toInteger $ length ps) args
  varArgs <- case zip' ps args of
               (_  , Left   _)            -> numArgsErr
               (pas, Right listArg@[])    -> maybe (return pas)
                 (\listParam -> return $ (listParam, List listArg) : pas) lp
               (pas, Right listArg@(_:_)) -> maybe numArgsErr
                 (\listParam -> return $ (listParam, List listArg) : pas) lp
  (val, clsr') <- flip runStateT clsr $ do
    bindVars $ HM.fromList varArgs
    NE.last <$> traverse eval bd
  return val
  -- modify (HM.union clsr)
  -- get >>= T.traceM . ("before bindClosure: " ++) . showLispEnv
  -- bindVars clsr
  -- get >>= T.traceM . ("after bindClosure : " ++) . showLispEnv
  -- bindVars $ HM.fromList varArgs
  -- get >>= T.traceM . ("after bindVars    : " ++) . showLispEnv
  -- NE.last <$> traverse eval bd
  --
  -- withTmpState clsr $ do
  --   bindVars varArgs
  --   NE.last <$> traverse eval bd

primitives :: [(String, Primitive)]
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
  , ("-"             , realBinOp (-) 0) -- TODO: broken
  , ("*"             , realBinOp (*) 1)
  ]

isLispBool :: String -> Primitive
isLispBool name = Primitive $ \case
  [Bool _] -> return       $ Bool True
  [_]      -> return       $ Bool False
  args     -> E.throwError $ NumArgs (Just name) 1 args

isLispString :: String -> Primitive
isLispString name = Primitive $ \case
  [String _] -> return       $ Bool True
  [_]        -> return       $ Bool False
  args       -> E.throwError $ NumArgs (Just name) 1 args

isLispCharacter :: String -> Primitive
isLispCharacter name = Primitive $ \case
  [Character _] -> return       $ Bool True
  [_]           -> return       $ Bool False
  args          -> E.throwError $ NumArgs (Just name) 1 args

isLispList :: String -> Primitive
isLispList name = Primitive $ \case
  [List _] -> return       $ Bool True
  [_]      -> return       $ Bool False
  args     -> E.throwError $ NumArgs (Just name) 1 args

isLispDottedList :: String -> Primitive
isLispDottedList name = Primitive $ \case
  [DottedList _ _] -> return       $ Bool True
  [_]              -> return       $ Bool False
  args             -> E.throwError $ NumArgs (Just name) 1 args

isLispSymbol :: String -> Primitive
isLispSymbol name = Primitive $ \case
  [Atom _] -> return       $ Bool True
  [_]      -> return       $ Bool False
  args     -> E.throwError $ NumArgs (Just name) 1 args

notLispBool :: String -> Primitive
notLispBool name = Primitive $ \case
  [Bool True ] -> return       $ Bool False
  [Bool False] -> return       $ Bool True
  [_]          -> return       $ Bool False
  args         -> E.throwError $ NumArgs (Just name) 1 args

isNullLispList :: String -> Primitive
isNullLispList name = Primitive $ \case
  [List []] -> return       $ Bool True
  [_]       -> return       $ Bool False
  args      -> E.throwError $ NumArgs (Just name) 1 args

symbol2String :: String -> Primitive
symbol2String name = Primitive $ \case
  [Atom name] -> return       $ String name
  [arg]       -> E.throwError $ TypeMismatch name "symbol" arg
  args        -> E.throwError $ NumArgs (Just name) 1 args

string2Symbol :: String -> Primitive
string2Symbol name = Primitive $ \case
  [String str] -> return       $ Atom str
  [arg]        -> E.throwError $ TypeMismatch name "string" arg
  args         -> E.throwError $ NumArgs (Just name) 1 args

realBinOp :: forall rc. (forall a. Num a => a -> a -> a) -> Integer
          -> String -> Primitive
realBinOp op init name = Primitive $ \args ->
  Real . foldl (binOpNumR $ \x y -> CBReal $ x `op` y) (Integer $ CBReal init)
  <$> traverse (unpackReal name) args

unpackReal :: E.MonadError LispError m => String -> LispVal -> m (Number 'R)
unpackReal _    (Real r) = return r
unpackReal func arg      = E.throwError $ TypeMismatch func "real number" arg
{- Dynamic
unpackReal (String str)  = either (const $ Integer $ CBReal 0) unpackReal $ readExpr str
unpackReal (Character c) = either (const $ Integer $ CBReal 0) unpackReal $ readExpr [c]
unpackReal (List [val])  = unpackReal val
unpackReal _             = Integer $ CBReal 0
-}

printLispErrOrVal :: LispErrOrVal -> IO ()
printLispErrOrVal = putStrLn . either show (show . PrettyLispVal)

prompt :: String -> IO String
prompt prmpt = putStr prmpt >> hFlush stdout >> getLine

rep :: String -> StateT LispEnv IO ()
rep expr = do
  errOrVal <- E.runExceptT $ do
    val <- readExpr expr
    eval val
  liftIO $ printLispErrOrVal errOrVal

repl :: StateT LispEnv IO ()
repl = do
  liftIO $ putStrLn "~~~ Scheme REPL ~~~"
  forever $ liftIO (prompt "> ") >>= rep

main :: IO ()
main = listToMaybe <$> getArgs >>= flip evalStateT env . maybe repl rep
  where
    env = HM.fromList $ second PrimitiveFunc <$> primitives

-- main = undefined
