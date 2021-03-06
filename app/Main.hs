{-# LANGUAGE LambdaCase #-}
-- {-# LANGUAGE BlockArguments #-}
{-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ConstraintKinds #-}

module Main where

import Control.Applicative (Alternative,(<|>),empty,liftA2)
-- import Control.Arrow (first,second)
import Control.Monad -- (MonadPlus,mzero,mplus)
import qualified Control.Monad.Except as E
import Control.Monad.IO.Class (MonadIO,liftIO)
import Control.Monad.Trans
import Control.Monad.Reader -- (MonadReader,ask)
import Control.Monad.State.Strict -- (StateT,evalStateT,modify,get,MonadState)
import Data.Bifunctor (first,second)
import Data.Complex
import Data.Either (isLeft)
import Data.Functor (void)
import Data.Functor.Identity
import Data.IORef
import qualified Data.HashMap.Strict as HM
import qualified Data.Map.Strict     as Map
import qualified Data.List.NonEmpty  as NE
import Data.Maybe (listToMaybe,fromMaybe)
import Data.Void (Void)
import Data.Ratio (Ratio,(%),numerator,denominator)
import qualified Debug.Trace as T
import System.Environment (getArgs)
import qualified System.IO   as IO

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

data Primitive = Primitive
  { primName :: String
  , appPrim  :: forall m. E.MonadError LispError m => [LispVal] -> m LispVal
  }

instance Show Primitive where
  show prim = "<primitive: " ++ primName prim ++ ">"

instance Eq Primitive where
  prim1 == prim2 = primName prim1 == primName prim2

data IOPrimitive = IOPrimitive
  { ioPrimName :: String
  , appIOPrim  :: forall m. (E.MonadError LispError m, MonadIO m)
               => [LispVal] -> m LispVal
  }

instance Show IOPrimitive where
  show ioPrim = "<IO primitive: " ++ ioPrimName ioPrim ++ ">"

instance Eq IOPrimitive where
  ioPrim1 == ioPrim2 = ioPrimName ioPrim1 == ioPrimName ioPrim2

data LispVal = Atom          String
             | List          [LispVal]
             | DottedList    [LispVal] LispVal
             | Real          (Number 'R)
             | Complex       (Number 'C)
             | Character     Char
             | String        String
             | Bool          Bool
             | Port          IO.Handle
             | PrimitiveFunc Primitive
             | IOFunc        IOPrimitive
             | Func { params    :: [String]
                    , listParam :: Maybe String
                    , body      :: NE.NonEmpty LispVal
                    , closure   :: IORef LispEnv
                    }
             deriving Eq
             -- deriving Show -- TODO

newtype PrettyLispVal = PrettyLispVal { unPrettyLispVal :: LispVal }

unwordsList :: [LispVal] -> String
unwordsList = unwords . fmap (show . PrettyLispVal)

unpackPrimitiveFunc :: LispVal -> Either LispVal Primitive
unpackPrimitiveFunc (PrimitiveFunc prim) = return prim
unpackPrimitiveFunc val                  = Left   val

unpackIOFunc :: LispVal -> Either LispVal IOPrimitive
unpackIOFunc (IOFunc ioPrim) = return ioPrim
unpackIOFunc val             = Left   val

freezeLispEnv :: LispEnv -> IO FrozenLispEnv
freezeLispEnv = traverse readIORef

withoutPrimitives :: FrozenLispEnv -> FrozenLispEnv
withoutPrimitives = HM.filter $ liftA2 (&&) (isLeft . unpackPrimitiveFunc)
                                            (isLeft . unpackIOFunc)

showLispEnv :: IORef LispEnv -> IO String
showLispEnv envRef = do
  env  <- readIORef envRef
  fEnv <- freezeLispEnv env
  return $ show $ PrettyLispVal <$> withoutPrimitives fEnv

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
      showVal (Port       _)       = "<IO port>"
      showVal (PrimitiveFunc prim) = show prim
      showVal (IOFunc        prim) = show prim
      showVal (Func ps lp bd clsr) = "(lambda (" ++ unwords (show <$> ps)
                                  ++ maybe "" (" . " ++) lp ++ ") ...) "
                                  -- ++ show (PrettyLispVal <$> withoutPrimitive clsr)
                                  -- TODO

      showReal :: Number 'R -> String
      showReal (Integer  (CBReal i)) = show i
      showReal (Rational (CBReal r)) = show (numerator r) ++ "/" ++ show (denominator r)
      showReal (Float    (CBReal f)) = show f
      showReal (Double   (CBReal d)) = show d

showValIO :: MonadIO m => LispVal -> m String
showValIO val@(Func ps lp bd clsr) = do
  str <- liftIO $ showLispEnv clsr
  return $ show (PrettyLispVal val) ++ " " ++ str
showValIO val = return $ show $ PrettyLispVal val

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
appendToState a = modify (<> a) -- lazy

signedDigitsString :: Parser String
signedDigitsString = do
  sign <- Just <$> single '-' <|> return Nothing
  void (single '+') <|> return ()
  maybe id (:) sign <$> some digitChar

parseExponentPart :: (Fractional r, Read r) => (r -> LispVal) -> PendingParser LispVal
parseExponentPart defaultReal = do
  precision     <- lift $ oneOf "fde"
  exponentPart  <- lift signedDigitsString
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
  rational . read <$> get

parseReal :: (Fractional r, Read r) => (r -> LispVal) -> Parser LispVal
parseReal defaultReal = signedDigitsString >>= \signedDigits ->
  choice $ flip evalStateT signedDigits <$>
    [ parseFractional defaultReal
    , parseRational
    , integer . read <$> get
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
      DottedList head <$> parseExpr
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
  [ whileNotAtom   parseHashPrefix
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

data ArgNum = ArgNumOr (NE.NonEmpty Integer)
            | MoreThan Integer
            deriving Eq

instance Show ArgNum where
  show (ArgNumOr ne1) = case NE.uncons $ NE.reverse ne1 of
    (an1, Nothing            ) -> show an1
    (an1, Just (an2 NE.:| ls)) -> foldr (\a b -> b ++ show a ++ ", ") "" ls
                               ++ show an2 ++ " or " ++ show an1
  show (MoreThan an) = "more than " ++ show an

argNum :: [Integer] -> ArgNum
argNum = ArgNumOr . NE.fromList

data LispError = NumArgs (Maybe String) ArgNum [LispVal]
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
  show (Parser parserErr)            = "[Parse error]\n"
                                    ++ errorBundlePretty parserErr
  show (NonSymbolParam func param)   = "Defining function " ++ funcName func
                                    ++ "with non symbol parameter: "
                                    ++ show (PrettyLispVal param)
  show (Default message)             = message

type WithLispErr a = Either LispError a
type LispErrOrVal  = WithLispErr LispVal

readOrThrow :: E.MonadError LispError m => String -> Parser a -> String -> m a
readOrThrow file parser input = either (E.throwError . Parser) return
                              $ runParser parser file input

readExpr :: E.MonadError LispError m => String -> String -> m LispVal
readExpr file = readOrThrow file $ parseExpr <* (sc >> eof)

readExprList :: E.MonadError LispError m => String -> String -> m [LispVal]
readExprList file = readOrThrow file $ endBy parseExpr sc <* eof

type LispEnv            = HM.HashMap String (IORef LispVal)
type FrozenLispEnv      = HM.HashMap String LispVal
type MonadWithLispEnv m = (MonadReader (IORef LispEnv) m, MonadIO m)

getLispEnv :: MonadWithLispEnv m => m LispEnv
getLispEnv = ask >>= liftIO . readIORef

putLispEnv :: MonadWithLispEnv m => LispEnv -> m ()
putLispEnv env = ask >>= liftIO . flip writeIORef env

modifyLispEnv :: MonadWithLispEnv m => (LispEnv -> LispEnv) -> m ()
modifyLispEnv f = ask >>= liftIO . flip modifyIORef' f

getVar :: (E.MonadError LispError m, MonadWithLispEnv m) => String -> m LispVal
getVar var = getLispEnv >>=
               maybe (E.throwError $ UnboundVar "Getting an unbound variable" var)
                     (liftIO . readIORef)
               . HM.lookup var

setVar' :: (MonadWithLispEnv m) => LispVal -> IORef LispVal -> m ()
setVar' val valRef = liftIO (writeIORef valRef val)

setVar :: (E.MonadError LispError m, MonadWithLispEnv m) => String -> LispVal -> m LispVal
setVar var val = do
  env <- getLispEnv
  maybe (E.throwError $ UnboundVar "Setting an unbound variable" var) (setVar' val)
        $ HM.lookup var env
  return val

defineVar :: MonadWithLispEnv m => String -> LispVal -> m LispVal
defineVar var val = do
  env <- getLispEnv
  maybe (liftIO (newIORef val) >>= \valRef -> putLispEnv (HM.insert var valRef env))
        (setVar' val)
        $ HM.lookup var env
  return val

makeLispEnv :: MonadIO m => FrozenLispEnv -> m LispEnv
makeLispEnv = liftIO . traverse newIORef

bindVars :: MonadIO m => IORef LispEnv -> LispEnv -> m (IORef LispEnv)
bindVars envRef bindings = do
  env <- liftIO $ readIORef envRef
  liftIO $ newIORef $ HM.unionWith const bindings env

unpackAtom :: LispVal -> Either LispVal String
unpackAtom (Atom atom) = return atom
unpackAtom val         = Left   val

makeFunc :: (E.MonadError LispError m, MonadWithLispEnv m)
         => Maybe String -> [LispVal] -> Maybe LispVal -> NE.NonEmpty LispVal
         -> m LispVal
makeFunc mVar paramVals mListParamVal body = do
  params     <- unpackParams paramVals
  mListParam <- unpackParams mListParamVal
  asks $ Func params mListParam body
  where
    unpackParams :: (E.MonadError LispError m, Traversable t)
                 => t LispVal -> m (t String)
    unpackParams paramVals = either (E.throwError . NonSymbolParam mVar) return
                           $ traverse unpackAtom paramVals

load :: (E.MonadError LispError m, MonadIO m) => String -> m [LispVal]
load filePath = liftIO (readFile filePath) >>= readExprList filePath

eval :: (E.MonadError LispError m, MonadWithLispEnv m) => LispVal -> m LispVal
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
eval (List [Atom "load", String filePath])
  = load filePath >>= fmap (foldr const (Bool False) . reverse) . traverse eval
eval (List [Atom "eval", val]) = eval val >>= eval
eval (List (function : args)) = do
                                  func    <- eval function
                                  argVals <- traverse eval args
                                  func `apply` argVals
eval val = return val
-- eval val = E.throwError $ BadSpecialForm "Unrecognized special form" val

-- return remaining list
zipWith' :: (a -> b -> c) -> [a] -> [b] -> ([c], Either [a] [b])
zipWith' _ [] bs         = ([], Right bs)
zipWith' _ as []         = ([], Left  as)
zipWith' f (a:as) (b:bs) = first (f a b :) $ zipWith' f as bs

zip' :: [a] -> [b] -> ([(a, b)], Either [a] [b])
zip' = zipWith' (,)

apply :: (E.MonadError LispError m, MonadIO m)
      => LispVal -> [LispVal] -> m LispVal
apply (PrimitiveFunc prim) args = prim `appPrim`   args
apply (IOFunc        prim) args = prim `appIOPrim` args
apply (Func ps lp bd clsr) args = do
  let numArgsErr = E.throwError $ NumArgs Nothing (argNum [toInteger $ length ps]) args
  varArgs <- case zip' ps args of
               (_  , Left   _)            -> numArgsErr
               (pas, Right listArg@[])    -> maybe (return pas)
                 (\listParam -> return $ (listParam, List listArg) : pas) lp
               (pas, Right listArg@(_:_)) -> maybe numArgsErr
                 (\listParam -> return $ (listParam, List listArg) : pas) lp
  env <- makeLispEnv (HM.fromList varArgs) >>= bindVars clsr
  flip runReaderT env $ do
    NE.last <$> traverse eval bd
apply func _ = E.throwError $ NotFunction "Not function" $ show $ PrettyLispVal func

primitives :: FrozenLispEnv
primitives = HM.fromList $ (\(name, func) -> (name, PrimitiveFunc $ func name)) <$>
  [ ("boolean?"      , isLispBool)
  , ("string?"       , isLispString)
  , ("char?"         , isLispCharacter)
  , ("list?"         , isLispList)
  , ("pair?"         , isLispDottedList)
  , ("symbol?"       , isLispSymbol)
  , ("symbol->string", symbol2String)
  , ("string->symbol", string2Symbol)
  , ("car"           , lispCar)
  , ("cdr"           , lispCdr)
  , ("cons"          , lispCons)
  , ("eq?"           , eqv)
  , ("eqv?"          , eqv)
  , ("+"             , realBinOp (+) 0)
  , ("-"             , realBinOp (-) 0) -- TODO: broken
  , ("*"             , realBinOp (*) 1)
  ]

primitive :: (String -> forall m. E.MonadError LispError m => [LispVal] -> m LispVal)
          -> String -> Primitive
primitive f name = Primitive name (f name)
-- primitive f name = (Primitive <*> f) name -- error

isLispBool :: String -> Primitive
isLispBool = primitive $ \name -> \case
  [Bool _] -> return       $ Bool True
  [_]      -> return       $ Bool False
  args     -> E.throwError $ NumArgs (Just name) (argNum [1]) args

isLispString :: String -> Primitive
isLispString = primitive $ \name -> \case
  [String _] -> return       $ Bool True
  [_]        -> return       $ Bool False
  args     -> E.throwError $ NumArgs (Just name) (argNum [1]) args

isLispCharacter :: String -> Primitive
isLispCharacter = primitive $ \name -> \case
  [Character _] -> return       $ Bool True
  [_]           -> return       $ Bool False
  args     -> E.throwError $ NumArgs (Just name) (argNum [1]) args

isLispList :: String -> Primitive
isLispList = primitive $ \name -> \case
  [List _] -> return       $ Bool True
  [_]      -> return       $ Bool False
  args     -> E.throwError $ NumArgs (Just name) (argNum [1]) args

isLispDottedList :: String -> Primitive
isLispDottedList = primitive $ \name -> \case
  [DottedList _ _] -> return       $ Bool True
  [_]              -> return       $ Bool False
  args             -> E.throwError $ NumArgs (Just name) (argNum [1]) args

isLispSymbol :: String -> Primitive
isLispSymbol = primitive $ \name -> \case
  [Atom _] -> return       $ Bool True
  [_]      -> return       $ Bool False
  args     -> E.throwError $ NumArgs (Just name) (argNum [1]) args

symbol2String :: String -> Primitive
symbol2String = primitive $ \name -> \case
  [Atom name] -> return       $ String name
  [arg]       -> E.throwError $ TypeMismatch name "symbol" arg
  args        -> E.throwError $ NumArgs (Just name) (argNum [1]) args

string2Symbol :: String -> Primitive
string2Symbol = primitive $ \name -> \case
  [String str] -> return       $ Atom str
  [arg]        -> E.throwError $ TypeMismatch name "string" arg
  args         -> E.throwError $ NumArgs (Just name) (argNum [1]) args

lispCar :: String -> Primitive
lispCar = primitive $ \name -> \case
  [List       (x : _)  ] -> return x
  [DottedList (x : _) _] -> return x
  [arg]                  -> E.throwError $ TypeMismatch name "pair" arg
  args                   -> E.throwError $ NumArgs (Just name) (argNum [1]) args

lispCdr :: String -> Primitive
lispCdr = primitive $ \name -> \case
  [List       (_ : xs)  ] -> return $ List xs
  [DottedList [_]      l] -> return l
  [DottedList (_ : xs) l] -> return $ DottedList xs l
  [arg]                   -> E.throwError $ TypeMismatch name "pair" arg
  args                    -> E.throwError $ NumArgs (Just name) (argNum [1]) args

lispCons :: String -> Primitive
lispCons = primitive $ \name -> \case
  [x, List       xs  ] -> return $ List (x : xs)
  [x, DottedList xs l] -> return $ DottedList (x : xs) l
  [x, y]               -> return $ DottedList [x]      y
  args                 -> E.throwError $ NumArgs (Just name) (argNum [1]) args

eqv :: String -> Primitive
eqv = primitive $ \name -> \case
  [x, y] -> return $ Bool $ x == y
  args   -> E.throwError $ NumArgs (Just name) (argNum [2]) args

realBinOp :: forall rc. (forall a. Num a => a -> a -> a) -> Integer
          -> String -> Primitive
realBinOp op init = primitive $ \name args ->
  Real . foldl (binOpNumR $ \x y -> CBReal $ x `op` y) (Integer $ CBReal init)
  <$> traverse (unpackReal name) args

unpackReal :: E.MonadError LispError m => String -> LispVal -> m (Number 'R)
unpackReal _    (Real r) = return r
unpackReal func arg      = E.throwError $ TypeMismatch func "real number" arg

ioPrimitives :: FrozenLispEnv
ioPrimitives = HM.fromList $ (\(name, func) -> (name, IOFunc $ func name)) <$>
  [ ("apply"            , applyProc)
  , ("open-input-file"  , makePort IO.ReadMode)
  , ("open-output-file" , makePort IO.WriteMode)
  , ("close-input-file" , closePort)
  , ("close-output-file", closePort)
  , ("read"             , readProc)
  , ("write"            , writeProc)
  , ("read-contents"    , readContents)
  ]

ioPrimitive :: (String -> forall m. (E.MonadError LispError m, MonadIO m)
                       => [LispVal] -> m LispVal)
            -> String -> IOPrimitive
ioPrimitive f name = IOPrimitive name (f name)

applyProc :: String -> IOPrimitive
applyProc = ioPrimitive $ \name -> \case
  [func, List args] -> apply func args
  (func : args)     -> apply func args
  args              -> E.throwError $ NumArgs (Just name) (MoreThan 2) args

makePort :: IO.IOMode -> String -> IOPrimitive
makePort mode = ioPrimitive $ \name -> \case
  [String filePath] -> Port <$> liftIO (IO.openFile filePath mode)
  [arg]             -> E.throwError $ TypeMismatch name "string" arg
  args              -> E.throwError $ NumArgs (Just name) (argNum [1]) args

closePort :: String -> IOPrimitive
closePort = ioPrimitive $ \name -> \case
  [Port port] -> liftIO $ IO.hClose port >> return (Bool True)
  [arg]       -> E.throwError $ TypeMismatch name "port" arg
  args        -> E.throwError $ NumArgs (Just name) (argNum [1]) args

readProc :: String -> IOPrimitive
readProc = ioPrimitive $ \name -> \case
  []          -> readProc name `appIOPrim` [Port IO.stdin]
  [Port port] -> liftIO (IO.hGetLine port) >>= readExpr (show port)
  [arg]       -> E.throwError $ TypeMismatch name "port" arg
  args        -> E.throwError $ NumArgs (Just name) (argNum [0,1]) args

writeProc :: String -> IOPrimitive
writeProc = ioPrimitive $ \name -> \case
  [val]            -> writeProc name `appIOPrim` [val, Port IO.stdout]
  [val, Port port] -> liftIO $ IO.hPrint port (PrettyLispVal val) >> return (Bool True)
  [_  , arg      ] -> E.throwError $ TypeMismatch name "port" arg
  args             -> E.throwError $ NumArgs (Just name) (argNum [1,2]) args

readContents :: String -> IOPrimitive
readContents = ioPrimitive $ \name -> \case
  [String filePath] -> String <$> liftIO (IO.readFile filePath)
  [arg]             -> E.throwError $ TypeMismatch name "string" arg
  args              -> E.throwError $ NumArgs (Just name) (argNum [1]) args

readAll :: String -> IOPrimitive
readAll = ioPrimitive $ \name -> \case
  [String filePath] -> List <$> load filePath

showLispErrOrVal :: LispErrOrVal -> IO String
showLispErrOrVal = either (return . show) showValIO
-- showLispErrOrVal = return . either show (show . PrettyLispVal)

printLispErrOrVal :: LispErrOrVal -> IO ()
printLispErrOrVal eov  = putStrLn =<< showLispErrOrVal eov

prompt :: String -> IO String
prompt prmpt = putStr prmpt >> IO.hFlush IO.stdout >> getLine

type WithLispEnv = ReaderT (IORef LispEnv)

rep :: String -> WithLispEnv IO ()
rep expr = do
  errOrVal <- E.runExceptT $ do
    val <- readExpr "" expr
    eval val
  liftIO $ printLispErrOrVal errOrVal

repl :: WithLispEnv IO ()
repl = do
  liftIO $ putStrLn "~~~ Scheme REPL ~~~"
  forever $ liftIO (prompt "> ") >>= rep

runOne :: NE.NonEmpty String -> WithLispEnv IO ()
runOne (filePath NE.:| args) = do
  bindings <- makeLispEnv $ HM.fromList [("args", List $ String <$> args)]
  modifyLispEnv $ \env -> HM.unionWith const bindings env
  errOrVal <- E.runExceptT (eval $ List [Atom "load", String filePath])
  liftIO $ showLispErrOrVal errOrVal >>= IO.hPutStrLn IO.stderr

main :: IO ()
main = do
  env    <- makeLispEnv $ primitives <> ioPrimitives
  global <- newIORef env
  getArgs >>= flip runReaderT global . maybe repl runOne . NE.nonEmpty

-- main = undefined
