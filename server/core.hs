{-# LANGUAGE ExtendedDefaultRules #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}
{-# OPTIONS_GHC -Wno-deferred-type-errors #-}
import qualified Control.Monad                  as Monad      (MonadPlus(mzero))
import qualified Data.Map.Strict                as Map        (assocs, elems, empty, fromList, insert, keysSet, lookup, mapEither, mapKeys, null, union, Map)
import qualified Data.Set                       as Set        (delete, empty, insert, singleton, union, Set)
import qualified Data.List                      as List       (intercalate)
import qualified Data.ByteString.Lazy.Internal  as ByteString (unpackChars, packChars)
import qualified Data.Vector                    as Vector     (toList)
import qualified System.Environment             as SysEnv     (getArgs)
import Data.Aeson                                             (decode, encode, (.:), object, FromJSON(parseJSON), Value(Object), KeyValue((.=)), ToJSON(toJSON))
import Data.Aeson.Types                                       (Parser)
import Data.Aeson.Text                                        (encodeToLazyText, encodeToTextBuilder)

---------------------------------------------------
--------------------- BASICS ----------------------
---------------------------------------------------

replace :: Eq b => b -> b -> [b] -> [b]
replace a b = map $ \c -> if c == a then b else c

main :: IO ()
main = do
  args' <- SysEnv.getArgs
  let arg = head args'
  let arg' = replace '~' (head "\"") arg
  print (commandHandler arg')

-- |Defining variable name
type Var = String

---------------------- Type -----------------------

-- |Defining type 
data Type =
    Product (Type, Type)
  | Function Type Type
  | Nat

-- |Equivalence function for type
equivalentType :: Type -> Type -> Bool
equivalentType Nat Nat =                                            True
equivalentType (Product (tau1, sigma1)) (Product (tau2, sigma2)) =  equivalentType tau1 tau2 && equivalentType sigma1 sigma2
equivalentType (Function tau1 sigma1) (Function tau2 sigma2) =      equivalentType tau1 tau2 && equivalentType sigma1 sigma2
equivalentType _ _ =                                                False

-- |Instantiating said type equivalence (see above) 
instance Eq Type where
  (==) = equivalentType

-- |Representation function for types
prettyType ::  Type -> String
prettyType Nat = "N"
prettyType (Function tau sigma) = s ++ " -> " ++ t
  where
    s = if sizeType tau > 1 then "(" ++ prettyType tau ++ ")"  else prettyType tau
    t = if sizeType sigma > 1 then "(" ++ prettyType sigma ++ ")"  else prettyType sigma
prettyType (Product (tau, sigma))
  | tau == natb' && sigma == natb' = "N^b"
  | otherwise = s ++ " >< " ++ t
  where
    s = if sizeType tau > 1 then "(" ++ prettyType tau ++ ")"  else prettyType tau
    t = if sizeType sigma > 1 then "(" ++ prettyType sigma ++ ")"  else prettyType sigma

-- |Instantiating said type representation (see above) 
instance Show Type where
  show = prettyType

instance ToJSON Type where
  toJSON Nat =                          object ["category" .= "NAT"]
  
  toJSON (Function tau sigma) =         object ["category" .=  "FUNCTION" , "dom" .= toJSON tau, "cod" .= toJSON sigma]
  toJSON (Product (tau, sigma)) 
    | tau == natb' && sigma == natb' =  object ["category" .= "NATB"]
    | otherwise =                       object ["category" .=  "PRODUCT" , "left" .= toJSON tau, "right" .= toJSON sigma]

parseType :: Value -> Parser Type
parseType (Object o) = do
  c <- o .:  "category"
  case c of
    "NAT"      -> return Nat;
    "FUNCTION" -> Function  <$> o .: "dom" <*> o .: "cod";
    "PRODUCT"  -> Product   <$> o .: "left" <> o .: "right";
parseType _ = Monad.mzero

instance FromJSON Type where
  parseJSON = parseType

------------------- TypeError ---------------------

-- |Defining a type error
data TypeError
  = VarNotFoundError String Var
 |  ApplyError String Term Term Type Type
 |  MaxError String Term Term
 |  ValueError String Term
 |  ModulusError String Term
 |  BTranslationTermError String Term
 |  BTranslationTypeError String (Type, Type)
 |  KleisliError String Type
 |  ModulusOfContinuityError String Type
 |  ChainError1 String Integer TypeError
 |  ChainError2 String Integer TypeError TypeError
 |  ChainErrorMultiple String Integer [TypeError]

-- |Representation function for typeErrors
prettyTypeError :: Int -> TypeError -> String
prettyTypeError i (VarNotFoundError message var) =                concat (replicate i "\t" ++ ["var not found error error: ", var, " (", message, ")"])
prettyTypeError i (ApplyError message m n tau sigma) =            concat (replicate i "\t" ++ ["application error: [", show m, ": ", show tau, "], [",  show n, ": ", show sigma, "] (", message, ")"])
prettyTypeError i (MaxError message m n) =                        concat (replicate i "\t"++  ["max error: ", show m, ", ", show n, " (", message, ")"])
prettyTypeError i (ValueError message m) =                        concat (replicate i "\t" ++ ["value error: ", show m, " (", message, ")"])
prettyTypeError i (ModulusError message m) =                      concat (replicate i "\t" ++ ["modulus error: ", show m, " (", message, ")"])
prettyTypeError i (BTranslationTermError message m) =             concat (replicate i "\t" ++ ["b-translation (term) error: ", show m, " (", message, ")"])
prettyTypeError i (BTranslationTypeError message (tau, sigma)) =  concat (replicate i "\t" ++ ["b-translation (type) error: ", show tau, ", ", show sigma, " (", message, ")"])
prettyTypeError i (KleisliError message tau) =                    concat (replicate i "\t" ++ ["kleisli error: ", show tau, " (", message, ")"])
prettyTypeError i (ModulusOfContinuityError message tau) =        concat (replicate i "\t" ++ ["modulus of continuity error: ", show tau, " (", message , ")"])
prettyTypeError i (ChainError1 message code te) =                 concat (replicate i "\t" ++ [message, ": ", show code, "\n", prettyTypeError (i + 1) te])
prettyTypeError i (ChainError2 message code te1 te2) =            concat (replicate i "\t" ++ [message, ": ", show code, "\n", prettyTypeError (i + 1)  te1, "\n", prettyTypeError (i + 1) te2])
prettyTypeError i (ChainErrorMultiple message code errors) =      concat (replicate i "\t" ++ [message, ": ", show code, "\n"]) ++  unlines (map (prettyTypeError (i + 1))  errors)

-- |Representation function for typeErrors
instance Show TypeError where
  show = prettyTypeError 0

instance ToJSON TypeError where
  toJSON (VarNotFoundError message var) =               object ["category" .= "VARNOTFOUNDERROR", "var" .= var] -- can occur using user input
  toJSON (ApplyError message m n tau sigma) =           object ["category" .= "APPLYERROR", "m" .= toJSON m, "n" .= toJSON n, "tau" .= toJSON tau, "sigma" .= toJSON sigma]
  toJSON (MaxError message m n) =                       object ["category" .= "MAXERROR", "m" .= toJSON m, "n" .= toJSON n] -- can occur using user input
  toJSON (ValueError message m) =                       object ["category" .= "VALUEERROR", "m" .= toJSON m]
  toJSON (ModulusError message m) =                     object ["category" .= "MODULUSERROR", "m" .= toJSON m]
  toJSON (BTranslationTermError message m) =            object ["category" .= "BTRANSLATIONTYPEERROR", "m" .= toJSON m] 
  toJSON (BTranslationTypeError message (tau, sigma)) = object ["category" .= "BTRANSLATIONTERMERROR", "tau" .= toJSON tau, "sigma" .= toJSON sigma]
  toJSON (KleisliError message tau) =                   object ["category" .= "KLEISLIERROR", "tau" .= toJSON tau]
  toJSON (ModulusOfContinuityError message tau) =       object ["category" .= "MODULUSOFCONTINUITYERROR", "tau" .= toJSON tau] -- can occur using user input
  toJSON (ChainError1 message code te) =                object ["category" .= "CHAINERROR1", "message" .=  message, "te" .= toJSON te] -- can occur using user input
  toJSON (ChainError2 message code te1 te2) =           object ["category" .= "CHAINERROR2", "message" .=  message, "te1" .= toJSON te1, "te1" .= toJSON te2] -- can occur using user input
  toJSON (ChainErrorMultiple message code errors) =     object ["category" .= "CHAINERRORMANY", "message" .=  message, "errors" .= toJSON errors] -- can occur using user input

---------------------- Term -----------------------

-- |Defining term 
data Term =
    Variable Var
  | Abstract (Var, Type) Term
  | Apply Term Term
  | Zero
  | Succ
  | Rec Type
  | Pair (Term, Term)
  | Max Term Term
  | Value Term
  | Modulus Term

-- |Representation function for terms
prettyTerm :: Term -> String
prettyTerm Zero = "0"
prettyTerm m
  | isNumeral m = prettyNumeral m
  | otherwise   = prettyTermHelper m

prettyNumeral :: Term -> String
prettyNumeral = prettyNumeralHelper 0
  where
    prettyNumeralHelper :: Integer -> Term -> String
    prettyNumeralHelper n (Apply Succ m)  = prettyNumeralHelper (n + 1) m
    prettyNumeralHelper n Zero            = "numeral " ++  show n
    prettyNumeralHelper _ _               = error "won't happen"

-- |Helper representation function for terms
prettyTermHelper ::  Term -> String
prettyTermHelper (Variable x) = x
prettyTermHelper (Abstract (x, rho) m) =  "\\(" ++ denote (x, rho)  ++ "). " ++ (if sizeTerm m > 1 then "(" ++ s ++ ")" else s)
  where s = prettyTerm m
prettyTermHelper (Apply m n) =            s ++ " " ++ t
  where
    s = if sizeTerm m > 1 then "(" ++ prettyTerm m ++ ")"  else prettyTerm m
    t = if sizeTerm n > 1 then "(" ++ prettyTerm n ++ ")"  else prettyTerm n
prettyTermHelper Succ =                   "succ"
prettyTermHelper Zero =                   "0"
prettyTermHelper (Pair (m, n))  =         "<" ++  prettyTerm m ++ "; " ++ prettyTerm n ++ ">"
prettyTermHelper (Value m) =              if sizeTerm m > 1 then "V_{" ++ s ++ "}" else "V_" ++ s where s = show m
prettyTermHelper (Modulus m) =            if sizeTerm m > 1 then "M_{" ++ s ++ "}" else "M_" ++ s where s = show m
prettyTermHelper (Max m n) =              "max(" ++ prettyTerm m ++ ", " ++ prettyTerm n ++ ")"
prettyTermHelper (Rec rho) =              "rec[" ++ show rho ++ "]"

-- |Instantiating said term representation (see above) 
instance Show Term where
  show = prettyTerm

-- |Equivalence function for term
equivalentTerm :: Term -> Term -> Bool
equivalentTerm (Variable x) (Variable y) =                      x == y
equivalentTerm (Abstract (x, tau) m) (Abstract (y, sigma) n) =  tau == sigma && rename (x, y) m == n && rename (y, x) n == m
equivalentTerm (Apply m n) (Apply u v) =                        m == u && n == v
equivalentTerm Zero Zero =                                      True
equivalentTerm Succ Succ =                                      True
equivalentTerm (Rec tau) (Rec sigma) =                          tau == sigma
equivalentTerm (Pair (m, n)) (Pair (u, v)) =                    m == u && n == v
equivalentTerm (Max m n) (Max u v) =                            m == u && n == v || m == v && n == u
equivalentTerm (Value m) (Value n) =                            m == n
equivalentTerm (Modulus m) (Modulus n) =                        m == n
equivalentTerm _ _ =                                            False

-- instantiating said type equivalence (see above) 
instance Eq Term where
  (==) = equivalentTerm

instance ToJSON Term where
  toJSON Zero =                   object ["category" .= "ZERO"]
  toJSON Succ =                   object ["category" .= "SUCC"]
  toJSON (Rec rho) =              object ["category" .= "REC", "rectype" .= toJSON rho]
  toJSON (Apply m n) =            object ["category" .=  "APPLY" , "left" .= toJSON m, "right" .= toJSON n]
  toJSON (Pair (m, n)) =          object ["category" .=  "PAIR" , "left" .= toJSON m, "right" .= toJSON n]
  toJSON (Abstract (x, tau) m) =  object ["category" .=  "ABSTRACT" , "abvar" .= x,"abtype" .= toJSON tau, "body" .= toJSON m]
  toJSON (Variable x) =           object ["category" .=  "VARIABLE" , "var" .= x]
  toJSON (Max m n) =              object ["category" .=  "MAX" , "left" .= toJSON m, "right" .= toJSON n]
  toJSON (Value m) =              object ["category" .=  "VALUE" , "content" .= toJSON m]
  toJSON (Modulus m) =            object ["category" .=  "MODULUS" , "content" .= toJSON m]

parseTerm :: Value -> Parser Term
parseTerm (Object o)  = do
  c <- o .:  "category";
  case c of
    "VARIABLE" -> Variable <$> o .: "var";
    "APPLY"    -> Apply <$> o .: "left" <*> o .: "right";
    "ZERO"     -> return Zero;
    "SUCC"     -> return Succ;
    "REC"      -> Rec   <$> o .: "rectype";
    "PAIR"     -> Pair  <$> o .: "left" <> o .: "right"
    "ABSTRACT" -> fixAbstract <$> o .: "abvar" <*> o .: "abtype"  <*> o .: "body"
    where 
      fixAbstract :: String -> Type -> Term -> Term
      fixAbstract x tau = Abstract (x, tau)
parseTerm _           = Monad.mzero

instance FromJSON Term where
  parseJSON = parseTerm

---------------------- Context -----------------------

-- |Defining context 
newtype Context = Context (Map.Map Var Type)

-- |Denotes a pair of a variable name and type, in the format 
denote :: (Var, Type) -> String
denote (m, tau) = m ++ ": " ++ show tau

-- |Denotes the content of a context, with commas (no comma at end)
denoteAll :: [(Var, Type)] -> String
denoteAll = List.intercalate ", " . map denote

prettyContext :: Context -> String
prettyContext (Context gamma)
  | Map.null gamma = "//"
  | otherwise      = "{" ++ denoteAll (Map.assocs gamma) ++ "}"

-- |Instantiates said context representation (see above) 
instance Show Context where
  show = prettyContext

data    Declaration'  = Declaration'  Var Type
newtype Declaration   = Declaration   (Var, Type)
newtype DecList       = DecList       [Declaration]

prettyDecList :: DecList -> String
prettyDecList (DecList decs) = show decs

parseDeclaration :: Value -> Parser Declaration
parseDeclaration o = transformDeclaration <$> parseJSON o
  where
    transformDeclaration :: Declaration' -> Declaration
    transformDeclaration  (Declaration' vn t) = Declaration (vn, t)

parseDeclaration' :: Value -> Parser Declaration'
parseDeclaration' (Object o) = Declaration' <$> o .: "vn" <*> o .: "t"
parseDeclaration' _ = Monad.mzero

instance FromJSON Declaration' where
  parseJSON = parseDeclaration'

instance FromJSON Declaration where
  parseJSON = parseDeclaration

instance Show DecList where
  show = prettyDecList
instance Show Declaration where
  show = prettyDeclartation
instance Show Declaration' where
  show = prettyDeclartation'

prettyDeclartation' :: Declaration' -> String
prettyDeclartation' (Declaration' vn t) = vn  ++ ": "  ++ show t

prettyDeclartation :: Declaration -> String
prettyDeclartation (Declaration (vn, t)) = vn  ++ ": "  ++ show t

instance FromJSON DecList where
    parseJSON (Object o) =  do
        pts <- o .: "declarations"
        ptsList <- mapM parseJSON $ Vector.toList pts
        return $ DecList ptsList
    parseJSON _ =           Monad.mzero

parseDecList :: Value -> Parser DecList
parseDecList (Object o) = do
  pts <- o .: "declarations"
  DecList <$> parseJSON pts
parseDecList _          = Monad.mzero

parseContext :: Value -> Parser Context
parseContext v = Context . Map.fromList . map unpackDeclaration . (\(DecList dl) -> dl) <$> parseDecList v
  where
    unpackDeclaration :: Declaration -> (Var, Type)
    unpackDeclaration (Declaration (vn, t))  = (vn, t)

instance FromJSON Context where
  parseJSON = parseContext

---------------- Input Structure ----------------

data InputStructure = InputStructure String Context Term

parseInputStructure :: Value -> Parser InputStructure
parseInputStructure (Object o) = InputStructure <$> o .: "command" <*> o .: "context" <*> o .: "term"
parseInputStructure _ = Monad.mzero

instance FromJSON InputStructure where
  parseJSON = parseInputStructure

-- |Representation function for types
prettyInputStructure ::  InputStructure -> String
prettyInputStructure (InputStructure comand context term) = show context ++ "\n" ++ show term

instance Show InputStructure where
  show = prettyInputStructure

---------------- Output Structure ----------------

data OutputStructure = Ok (Either Type Term) | Err TypeError

instance ToJSON OutputStructure where
  toJSON (Ok (Right term)) =  object ["category" .= "OKAY", "ok" .= term]
  toJSON (Ok (Left tau)) =    object ["category" .= "OKAY", "ok" .= tau]
  toJSON (Err te) =           object ["category" .=  "ERROR" , "err" .= te]

-- |Representation function for types
prettyOutputStructure ::  OutputStructure -> String
prettyOutputStructure (Ok (Right term)) = show term
prettyOutputStructure (Ok (Left tau)) =   show tau
prettyOutputStructure (Err te) =          show te

instance Show OutputStructure where
  show = prettyOutputStructure


------------- ADDITIONAL FUNCTIONS --------------

-- |Splits an type into its curried domain and codomain
splitType :: Type -> Maybe (Type, Type)
splitType (Function tau sigma) = Just (tau, sigma)
splitType _ = Nothing

-- |Finds the type of a term given its context
{-handles bound variables by isnerting the (variable name, type) pair in the context
overwriting any pair (variable name, type') pair, so different branches can proceed independently -}
typeCheck ::  Context -> Term -> Either TypeError Type
typeCheck (Context gamma) (Variable x) = fix ft
  where
    fix :: Maybe Type -> Either TypeError Type
    fix Nothing = Left (VarNotFoundError "variable missing from context" x)
    fix (Just rho) = Right rho
    ft :: Maybe Type
    ft = Map.lookup x gamma
typeCheck (Context gamma) (Abstract (x, tau) m) = fix tc
  where
    tc :: Either TypeError Type
    tc =  typeCheck (Context (Map.insert x tau gamma)) m
    fix :: Either TypeError Type -> Either TypeError Type
    fix (Right sigma) = Right (Function tau sigma)
    fix (Left te) =     Left (ChainError1 "occurred in type check, abstraction" 2 te)
typeCheck context (Pair (m, n)) = fix tau' sigma'
  where
    tau' ::  Either TypeError Type
    tau' = typeCheck context m
    sigma' ::  Either TypeError Type
    sigma' = typeCheck context n
    fix :: Either TypeError Type -> Either TypeError Type -> Either TypeError Type
    fix (Right tau'') (Right sigma'') = Right (Product (tau'', sigma''))
    fix (Right _) (Left te) =           Left (ChainError1 "occurred in type check, pair / right" 3 te)
    fix (Left te) (Right _) =           Left (ChainError1 "occurred in type check, pair / left" 4 te)
    fix (Left te1) (Left te2) =         Left (ChainError2 "occurred in type check, pair / both" 5 te1 te2)
typeCheck context (Max m n) = fix tc1 tc2
  where
    tc1 :: Either TypeError Type
    tc1 = typeCheck context m
    tc2 :: Either TypeError Type
    tc2 = typeCheck context n
    fix :: Either TypeError Type -> Either TypeError Type -> Either TypeError Type
    fix (Right Nat) (Right Nat) = Right Nat
    fix (Right _) (Right _) =     Left (MaxError "occurred in type check, max" m n)
    fix (Left te1) (Right _) =    Left (ChainError1 "occurred in type check, max / left" 6 te1)
    fix (Right _) (Left te2) =    Left (ChainError1 "occurred in type check, max / right" 7 te2)
    fix (Left te1) (Left te2) =   Left (ChainError2 "occurred in type check, max / both" 8 te1 te2)
typeCheck context (Apply m n) =   fix2 tc1 tc2
  where
    tc1 = typeCheck context m
    tc2 = typeCheck context n
    fix1 :: Type -> Type -> Maybe (Type, Type)  -> Either TypeError Type
    fix1 tau' sigma' Nothing  = Left (ApplyError "occurred in type check, apply" m n tau' sigma')
    fix1 tau' sigma' (Just (tau, sigma))
      | sigma' == tau = Right sigma
      | otherwise =     Left (ApplyError "occurred in type check, apply" m n tau' sigma')
    fix2 :: Either TypeError Type -> Either TypeError Type -> Either TypeError Type
    fix2 (Right tau) (Right sigma) =  fix1 tau sigma (splitType tau)
    fix2 (Left te1) (Right _) =       Left (ChainError1 "occurred in type check, apply / left" 9 te1)
    fix2 (Right _) (Left te2) =       Left (ChainError1 "occurred in type check, apply / right" 10 te2)
    fix2 (Left te1) (Left te2) =      Left (ChainError2 "occurred in type check, apply / both" 11 te1 te2)
typeCheck _ Succ = Right (Function Nat Nat)
typeCheck _ Zero = Right Nat
typeCheck _ (Rec rho) = Right (Function rho (Function (Function Nat (Function rho rho)) (Function Nat rho)))
typeCheck context (Value m) = fix tc
  where
    tc :: Either TypeError Type
    tc = typeCheck context m
    fix ::Either TypeError Type -> Either TypeError Type
    fix (Right tau)
      | tau == natb = Right natb'
      | otherwise = Left (ValueError "occurred in type check, value" m)
    fix (Left te) = Left (ChainError1 "occurred in type check, value" 12 te)
typeCheck context (Modulus m) = fix tc
  where
    tc :: Either TypeError Type
    tc = typeCheck context m
    fix ::Either TypeError Type -> Either TypeError Type
    fix (Right tau)
      | tau == natb = Right natb'
      | otherwise = Left (ModulusError "occurred in type check, modulus" m)
    fix (Left te) = Left (ChainError1 "occurred in type check, modulus" 13 te)

--------------- USEFUL FUNCTIONS ----------------

-- |Whether or not a term can be produced 
isNumeral :: Term -> Bool
isNumeral (Apply Succ m) = isNumeral m
isNumeral Zero = True
isNumeral _ = False

-- |Computes the number of symbols in a type
sizeType :: Type -> Int
sizeType Nat = 1
sizeType (Function _ _) = 2
sizeType (Product (tau, sigma))
  | tau == natb' && sigma == natb' = 1
  | otherwise = 2
sizeTerm :: Term -> Int
sizeTerm m
  | isNumeral m = 1
  | otherwise = sizeTermHelper m

-- |Computes the number of symbols in a term
sizeTermHelper :: Term -> Int
sizeTermHelper (Apply _ _) = 2
sizeTermHelper (Abstract _ _) = 3
sizeTermHelper (Value _) = 2
sizeTermHelper (Modulus _) = 2
sizeTermHelper _ = 1

-- |Computes a list of free variable names of a term
freeNames :: Term -> Set.Set Var
freeNames (Variable x) = Set.singleton x
freeNames (Apply m n) = Set.union (freeNames m) (freeNames n)
freeNames (Pair (m, n)) = Set.union (freeNames m) (freeNames n)
freeNames (Max m n) = Set.union (freeNames m) (freeNames n)
freeNames (Abstract (x, _) m) = Set.delete x (freeNames m)
freeNames (Value m) = freeNames m
freeNames (Modulus m) = freeNames m
freeNames _ = Set.empty

-- |Computes the number of bound variables of a term
boundNum :: Term -> Int
boundNum (Apply m n) = boundNum m + boundNum n
boundNum (Abstract (_, _) m) = 1 + boundNum m
boundNum (Pair (m, n)) = boundNum m + boundNum n
boundNum (Max m n) = boundNum m + boundNum n
boundNum (Value m) = boundNum m
boundNum (Modulus m) = boundNum m
boundNum _ = 0

-- |Computes a list of bound variable names of a term
boundNames :: Term -> Set.Set Var
boundNames (Apply m n) = Set.union (boundNames m) (boundNames n)
boundNames (Abstract (x, _) m) = Set.insert x (boundNames m)
boundNames (Pair (m, n)) = Set.union (boundNames m) (boundNames n)
boundNames (Max m n) = Set.union (boundNames m) (boundNames n)
boundNames (Value m) = boundNames m
boundNames (Modulus m) = boundNames m
boundNames _ = Set.empty

-- |Renames occurrences of x to y in a term
rename :: (Var, Var) -> Term -> Term
rename (x, y) (Variable z)
  | x == z = Variable y
  | otherwise = Variable z
rename (x, y) (Abstract (z, tau) m)
  | x == z = Abstract (z, tau) m
  | otherwise = Abstract (z, tau) (rename (x, y) m)
rename (x, y) (Apply m n) = Apply (rename (x, y) m) (rename (x,y) n)
rename (x, y) (Max m n) = Max (rename (x, y) m) (rename (x, y) n)
rename (x, y) (Pair (m, n)) = Pair (rename (x, y) m, rename (x,y) n)
rename (x, y) (Value m) = Value (rename (x, y) m)
rename (x, y) (Modulus m) = Modulus (rename (x, y) m)
rename (_, _) m = m

-- |Substitutes m for x in a
substitute :: (Var, Term) -> Term -> Term
substitute (x, m) (Variable y)
  | x == y =                      m
  | otherwise =                   Variable y
substitute (x, m) (Abstract (z, tau) n)
  | x == z =                      Abstract (z, tau) n
  | otherwise =                   Abstract (z, tau) (substitute (x, m) n)
substitute (x, l) (Apply m n) =   Apply (substitute (x, l) m) (substitute (x, l) n)
substitute (x, l) (Pair (m, n)) = Pair (substitute (x, l) m, substitute (x, l) n)
substitute (x, l) (Max m n) =     Max (substitute (x, l) m) (substitute (x, l) n)
substitute (x, m) (Value n) =     Value (substitute (x, m) n)
substitute (x, m) (Modulus n) =   Modulus (substitute (x, m) n)
substitute (_, _) m =             m

-- |List of all standard names
allNames :: [Var]
allNames = map (:[]) ['a'..'z'] ++ [ x : show i | i <- [o..] , x <- ['a'..'z'] ]
 where
   o :: Integer
   o = 1

-- |Computes a set of all names in a context, term
usedNames :: Context -> Term -> Set.Set Var
usedNames (Context gamma) m = Set.union (Map.keysSet gamma) (boundNames m)

-- |Filters used names from a infinite list of standard names
freshNames :: Context -> Term -> [Var]
freshNames context m = filter (`notElem` usedNames context m) allNames

-- |Helper function to reassign names
reassign :: Context -> Term -> Term
reassign context m' = reassignHelper (freshNames context m') m'
  where
    reassignHelper :: [Var] -> Term -> Term
    reassignHelper (x:xs) (Abstract (y, tau) m) = Abstract (x, tau) (reassignHelper xs (rename (y, x) m))
    reassignHelper xs (Apply m n) = Apply (reassignHelper xs m) (reassignHelper (drop (boundNum m) xs) n)
    reassignHelper xs (Pair (m, n)) = Pair (reassignHelper xs m, reassignHelper (drop (boundNum m) xs) n)
    reassignHelper xs (Max m n) = Max (reassignHelper xs m) (reassignHelper (drop (boundNum m) xs) n)
    reassignHelper xs (Value m) = Value (reassignHelper xs m)
    reassignHelper xs (Modulus m) = Modulus (reassignHelper xs m)
    reassignHelper [] _ = error "won't happen"
    reassignHelper _ m = m

---------------------------------------------------
-------------------- REDUCTION --------------------
---------------------------------------------------

-- |Recurses until it reaches a redex or a simplifiable term, and reduces it
reduce :: Term -> Term
reduce (Abstract (v, tau) (Apply w (Variable v')))
 | v' == v =  reduce w -- eta reduction
 | otherwise = Abstract (v, tau) (Apply (reduce w) (Variable v'))
reduce (Apply (Abstract (x, _) l) m) = reduce (substitute (x, m) l) -- beta reduction
reduce (Apply (Apply (Apply (Rec rho) a) f) (Apply Succ n)) = Apply (Apply f n) (Apply (Apply (Apply (Rec rho) a) f) n)
reduce (Apply (Apply (Apply (Rec _) a) _) Zero) = a
reduce (Max (Apply Succ m) (Apply Succ n)) = Apply Succ (Max (reduce m) (reduce n))
reduce (Value (Pair (m, _))) = reduce m
reduce (Modulus (Pair (_, n))) = reduce n
reduce (Max m Zero) = reduce m
reduce (Max Zero n) = reduce n
reduce (Max m n)
  | m == n = reduce m
  | otherwise = Max (reduce m) (reduce n)
reduce (Apply m n) = Apply (reduce m) (reduce n)
reduce (Abstract (y, tau) m) = Abstract (y, tau) (reduce m)
reduce (Pair (m, n)) = Pair (reduce m, reduce n)
reduce (Value m) = Value (reduce m)
reduce (Modulus m) = Modulus (reduce m)
reduce m = m

-- |Performs reductions until there are no redexes left
reduceAll :: Term -> Term
reduceAll m = reduceAllHelper m (reduce m)
  where
    reduceAllHelper :: Term  -> Term -> Term
    reduceAllHelper prev curr
      | prev == curr = curr
      | otherwise    = reduceAllHelper curr (reduce curr)

-- |Normalizes a term
normalize :: Context -> Term -> Either TypeError Term
normalize context m = normalizeHelper (typeCheck context m) (reassign context m)
  where
    normalizeHelper :: Either TypeError Type -> Term ->  Either TypeError Term
    normalizeHelper (Left te) _ = Left te
    normalizeHelper (Right _) m' = Right (reduceAll m')

structureTermOutput :: Either TypeError Term -> OutputStructure
structureTermOutput (Right m) = Ok (Right m)
structureTermOutput (Left te) = Err te

structureTypeOutput :: Either TypeError Type -> OutputStructure
structureTypeOutput (Right m) = Ok (Left m)
structureTypeOutput (Left te) = Err te

commandContainer :: InputStructure -> OutputStructure
commandContainer (InputStructure "E"  context term) = echoHandler (typeCheck context term) term
   where
    echoHandler :: Either TypeError Type -> Term -> OutputStructure
    echoHandler (Right _) term =  Ok (Right term)
    echoHandler (Left te) _ = Err te
commandContainer (InputStructure "N" context term) = structureTermOutput $ normalize context term
commandContainer (InputStructure "M"  context term) = structureTermOutput $ modulusOfContinuity context term
commandContainer (InputStructure "T"  context term) = structureTypeOutput $ typeCheck context term
commandContainer InputStructure {} = error "won't happen"

decode'' :: FromJSON a => String -> Maybe a
decode'' = decode . ByteString.packChars

encode'' :: ToJSON a => a -> String
encode'' = ByteString.unpackChars . encode

commandHandler :: String -> String
commandHandler inputText = process decoded
  where
    decoded :: Maybe InputStructure
    decoded = (decode'' :: String -> Maybe InputStructure) inputText
    process :: Maybe InputStructure -> String
    process Nothing   = "{\"category\":\"ERROR\",\"err\":{\"category\":\"CONTAINERERROR\"}}"
    process (Just a)  = encode'' (commandContainer a)

---------------------------------------------------
------------------ b-TRANSLATION ------------------
---------------------------------------------------

-- |Determines whether a type is encodable
encodableType :: Type -> Bool
encodableType Nat  = True
encodableType (Function tau sigma) = encodableType tau && encodableType sigma
encodableType (Product (_,_)) = False

-- |Determines whether a term is encodable
encodableTerm :: Term -> Bool
encodableTerm (Abstract (_, tau) m) = encodableTerm m && encodableType tau
encodableTerm (Apply m n) =           encodableTerm m && encodableTerm n
encodableTerm (Variable _) =          True
encodableTerm Zero =                  True
encodableTerm Succ =                  True
encodableTerm (Rec rho) =             encodableType rho
encodableTerm _ = False

numeral :: Integer -> Term
numeral n
  | n > 0 = Apply Succ (numeral (n - 1))
  | otherwise = Zero

-- |Computes the maximum  of two terms
max' :: Context -> Term -> Term -> Either TypeError Term
max' context m' n' = fix tau sigma
  where
    tau :: Either TypeError Type
    tau = typeCheck context m'
    sigma :: Either TypeError Type
    sigma = typeCheck context n'
    fix (Right _) (Left te) =       Left (ChainError1 "occured in max / right" 14 te)
    fix (Left te) (Right _) =       Left (ChainError1 "occured in max / left" 15 te)
    fix (Left te1) (Left te2) =     Left (ChainError2 "occured in max / both" 16 te1 te2)
    fix (Right Nat) (Right Nat) =   Right (maxHelper m' n')
      where
        maxHelper :: Term -> Term -> Term
        maxHelper (Apply Succ m) (Apply Succ n) = Apply Succ (maxHelper m n)
        maxHelper Zero n = n
        maxHelper m Zero = m
        maxHelper m n
          | m == n = m
          | otherwise = Max m n
    fix (Right _) (Right _) =       Left (MaxError "occured in max / incorrect type(s)" m' n')

-- |x ~> x^b
bTranslationVar :: Var -> Var
bTranslationVar x = x ++ "^b"

-- |Single component of N^b 
natb' :: Type
natb' =  Function (Function Nat Nat) Nat

-- |N^b
natb :: Type
natb =  Product (natb', natb')

-- |rho ~> rho^b
bTranslationType :: Type -> Either TypeError Type
bTranslationType Nat = Right natb
bTranslationType (Function sigma tau) = fix sigma' tau'
  where
    sigma' :: Either TypeError Type
    sigma' = bTranslationType sigma
    tau' :: Either TypeError Type
    tau' = bTranslationType tau
    fix :: Either TypeError Type -> Either TypeError Type -> Either TypeError Type
    fix (Right sigma'') (Right tau'') = Right (Function sigma''  tau'')
    fix (Right _) (Left te) = Left (ChainError1 "occurred in b-translation (type) / right" 17 te)
    fix (Left te) (Right _) = Left (ChainError1 "occurred in b-translation (type) / left" 18 te)
    fix (Left te1) (Left te2) = Left (ChainError2 "occurred in b-translation (type) / both" 19 te1 te2)
bTranslationType (Product (sigma, tau)) = Left (BTranslationTypeError "occured in b-translation for type" (sigma, tau))

-- |Performs b-translation on every (variable name, type) pair in a context
bTranslationContext :: Context -> Either TypeError Context
bTranslationContext (Context gamma)
  | Map.null errors = Right (Context (Map.mapKeys bTranslationVar types))
  | otherwise = Left (ChainErrorMultiple "occcurred in b-translation context" 100 (Map.elems errors))
  where
    errors :: Map.Map Var TypeError
    types :: Map.Map Var Type
    (errors, types) = Map.mapEither bTranslationType gamma

-- |w ~> V_w
value :: Context -> Term -> Either TypeError Term
value context' m' = fix (normalize context' m')
  where
    fix (Right n''') =  valueHelper context' n'''
    fix (Left te) = Left te
    valueHelper :: Context -> Term -> Either TypeError Term
    valueHelper context (Pair (m, n)) = fix' tc1 tc2
      where
        tc1 :: Either TypeError Type
        tc1 = typeCheck context m
        tc2 :: Either TypeError Type
        tc2 = typeCheck context n
        fix' :: Either TypeError Type -> Either TypeError Type -> Either TypeError Term
        fix' (Right tau) (Right sigma)
          | tau == natb' && sigma == natb' = Right m
          | otherwise = Left (ValueError "occurred in value" (Pair (m, n)))
        fix' (Left te1) (Right _) = Left (ChainError1 "occurred in value (pair) / left" 21 te1)
        fix' (Right _) (Left te2) = Left (ChainError1 "occurred in value (pair) / right" 22 te2)
        fix' (Left te1) (Left te2) = Left (ChainError2 "occurred in value (pair) / both" 23 te1 te2)
    valueHelper context m = fix' tc
      where
        tc :: Either TypeError Type
        tc = typeCheck context m
        fix' :: Either TypeError Type -> Either TypeError Term
        fix' (Right tau)
          | tau == natb = Right (Value m)
          | otherwise = Left (ValueError "occurred in value" m)
        fix' (Left te1)  = Left (ChainError1 "occurred in value" 24 te1)

-- |w ~> M_w
modulus :: Context -> Term -> Either TypeError Term
modulus context' m' = fix (normalize context' m')
  where
    fix (Right n''') =  modulusHelper context' n'''
    fix (Left te) = Left te
    modulusHelper :: Context -> Term -> Either TypeError Term
    modulusHelper context (Pair (m, n)) = fix' tc1 tc2
      where
        tc1 :: Either TypeError Type
        tc1 = typeCheck context m
        tc2 :: Either TypeError Type
        tc2 = typeCheck context n
        fix' :: Either TypeError Type -> Either TypeError Type -> Either TypeError Term
        fix' (Right tau) (Right sigma)
          | tau == natb' && sigma == natb' = Right n
          | otherwise = Left (ModulusError "occurred in modulus" (Pair (m, n)))
        fix' (Left te1) (Right _) = Left (ChainError1 "occurred in modulus (pair) / left" 25 te1)
        fix' (Right _) (Left te2) = Left (ChainError1 "occurred in modulus (pair) / right" 26 te2)
        fix' (Left te1) (Left te2) = Left (ChainError2 "occurred in modulus (pair) / both" 27 te1 te2)
    modulusHelper context m = fix' tc
      where
        tc :: Either TypeError Type
        tc = typeCheck context m
        fix' (Right tau)
          | tau == natb = Right (Modulus m)
          | otherwise = Left (ModulusError "occurred in modulus" m)
        fix' (Left te1)  = Left (ChainError1 "occurred in modulus" 28 te1)

-- |Kleisli extension
ke :: Context -> Type -> Term -> Term -> Either TypeError Term
ke context''' tau''''' g f = keHelper (tc1, tc2) context''' tau''''' g f
  where
    tc1 :: Either TypeError Type
    tc1 = typeCheck context''' g
    tc2 :: Either TypeError Type
    tc2 = typeCheck context''' f
    keHelper :: (Either TypeError Type, Either TypeError Type) -> Context -> Type -> Term -> Term -> Either TypeError Term
    keHelper (Right _, Left _) _ tau _ _ = Left (KleisliError "basic type check failed ~ 1" tau)
    keHelper (Left _, Right _) _ tau _ _ = Left (KleisliError "basic type check failed ~ 2" tau)
    keHelper (Left _, Left _) _ tau _ _ = Left (KleisliError "basic type check failed ~ 3" tau)
    keHelper (Right _, Right _) context tau' g' f'
      | keTypeCheck context tau' g' f' = keHelperHelper 0 context tau' g' f'
      | otherwise = Left (KleisliError "complex type check failed" tau')
      where
        keTypeCheck :: Context -> Type -> Term -> Term -> Bool
        keTypeCheck context''''' rho' g''''' f''''' = fix2 tau sigma
          where
            tau = typeCheck context''''' g'''''
            sigma = typeCheck context''''' f'''''
            fix1 :: Maybe (Type, Type) -> Type -> Either TypeError Type -> Bool
            fix1 Nothing _ (Left _) = False
            fix1 (Just (_, _))  _ (Left _) = False
            fix1 Nothing _ (Right _) = False
            fix1 (Just (tau1, tau2)) sigma' (Right rhob'')
              | tau1 == Nat && sigma' == natb && tau2 == rhob'' = True
              | otherwise = False
            fix2 :: Either TypeError Type -> Either TypeError Type -> Bool
            fix2 (Left _) (Right _) = False
            fix2 (Right _) (Left _) = False
            fix2 (Right tau'') (Right sigma') = fix1 (splitType tau'')  sigma' (bTranslationType rho')
            fix2 (Left _) (Left _) = False
        keHelperHelper :: Integer ->  Context -> Type -> Term -> Term -> Either TypeError Term
        keHelperHelper version (Context gamma) (Function sigma tau) g f = ke'''
          where
            fixK :: Either TypeError Type -> Either TypeError Term
            fixK (Right rho') = keHelperHelper (version + 1) (Context (Map.insert ("x" ++ show version) rho' gamma)) tau m f
            fixK (Left te) = Left (ChainError1 "occurred in ke, b-translation (type) of type sub-script (1)" 29 te)
            k :: Either TypeError Term
            k = fixK (bTranslationType sigma)
            fix :: Either TypeError Term -> Either TypeError Type -> Either TypeError Term
            fix (Right k') (Right rho') = Right (Abstract ("x" ++ show version, rho') k')
            fix (Left te) (Right _) = Left (ChainError1 "occurred in ke, ke recursion" 30 te)
            fix (Right _) (Left te) = Left (ChainError1 "occurred in ke, b-translation (type) of type sub-script (2)" 31 te)
            fix (Left te1) (Left te2)= Left (ChainError2 "occurred in ke, both" 32 te1 te2)
            ke''' :: Either TypeError Term
            ke''' = fix k (bTranslationType sigma)
            m :: Term
            m = Abstract ("k", Nat) (Apply (Apply g (Variable "k")) (Variable ("x" ++ show version) ))
        keHelperHelper _ _ (Product (tau, sigma)) _ _ = Left (KleisliError "invalid type" (Product (tau, sigma)))
        keHelperHelper _ (Context gamma) Nat g f'''''' = fixPair v'' max''
          where
            context' = Context (Map.insert "&alpha;" (Function Nat Nat) gamma)
            mf :: Either TypeError Term
            mf = modulus context' f'''''' -- mf
            vf :: Either TypeError Term
            vf = value context' f'''''' -- vf 
            fixVFA ::  Either TypeError Term -> Either TypeError Term
            fixVFA (Right vf') = Right (Apply vf' (Variable "&alpha;"))
            fixVFA (Left te) = Left (ChainError1 "occurred in computing short" 33 te)
            vfa :: Either TypeError Term
            vfa = fixVFA vf -- vf alpha
            fixV'' :: Either TypeError Term -> Either TypeError Term
            fixV'' (Right vfa') = value context' (Apply g vfa')
            fixV'' (Left te) = Left (ChainError1 "occurred in computing v''" 34 te)
            v'' ::  Either TypeError Term
            v'' = fixV'' vfa -- v(g(vf alpha))
            fixM'' :: Either TypeError Term -> Either TypeError Term
            fixM'' (Right vfa') = modulus context' (Apply g vfa')
            fixM'' (Left te) = Left (ChainError1 "occurred in computing m''" 35 te)
            m'' :: Either TypeError Term
            m'' = fixM'' vfa -- m(g(vf alpha))
            fixMax'' :: Either TypeError Term -> Either TypeError Term -> Either TypeError Term
            fixMax'' (Right p) (Right q) = max' context' (Apply p (Variable "&alpha;")) (Apply q (Variable "&alpha;"))
            fixMax'' (Left te) (Right _) = Left (ChainError1 "occured in computing b-translation (term), max / left" 36 te)
            fixMax'' (Right _) (Left te) = Left (ChainError1 "occured in computing b-translation (term), max / right" 37 te)
            fixMax'' (Left te1) (Left te2) = Left (ChainError2 "occured in computing b-translation (term), max / both" 38 te1 te2)
            max'' :: Either TypeError Term
            max'' = fixMax'' m'' mf -- max (m(g(vf &alpha;)) &alpha;, mf &alpha;)
            fixPair :: Either TypeError Term -> Either TypeError Term -> Either TypeError Term
            fixPair (Right p) (Right q) = Right (Pair (Abstract ("&alpha;", Function Nat Nat) (Apply p (Variable "&alpha;")), Abstract ("&alpha;", Function Nat Nat) q))
            fixPair (Left te) (Right _) = Left (ChainError1 "occured in computing b-translation (term), pair / left" 39 te)
            fixPair (Right _) (Left te) = Left (ChainError1 "occured in computing b-translation (term), pair / right" 40 te)
            fixPair (Left te1) (Left te2) = Left (ChainError2 "occured in computing b-translation (term), pair / both" 41 te1 te2)

-- |Unpacks a result assuming it is not an error type
unpack :: Either a b -> b
unpack (Right r') = r'
unpack (Left _) = error "unpack error"

-- |t ~> t^b
bTranslationTerm ::  Context -> Term -> Either TypeError Term
bTranslationTerm context' m' = bTranslationTermHelper (encodableTerm m') (typeCheck context' m') context' m'
  where
    bTranslationTermHelper :: Bool -> Either TypeError Type -> Context -> Term -> Either TypeError Term
    bTranslationTermHelper False (Right _) _ m = Left (BTranslationTermError "unencodable term" m)
    bTranslationTermHelper True (Left te) _ _ = Left (ChainError1 "occurred in b-translation (early) (fails type check)"  0 te)
    bTranslationTermHelper False (Left te) _ _ = Left (ChainError1 "occurred in b-translation (early) (unencodable, fails type check)"  0 te)
    bTranslationTermHelper True (Right _) context m = bTranslationTermHelperHelper context m
      where
        bTranslationTermHelperHelper :: Context -> Term -> Either TypeError Term
        bTranslationTermHelperHelper _ (Variable x) = Right (Variable (bTranslationVar x))
        bTranslationTermHelperHelper (Context gamma) (Abstract (x, tau) m'''') = fix x m''' tau'
          where
            m''' :: Either TypeError Term
            m''' = bTranslationTermHelperHelper (Context (Map.insert x tau gamma)) m''''
            tau' ::  Either TypeError Type
            tau' = bTranslationType tau
            fix :: Var -> Either TypeError Term -> Either TypeError Type -> Either TypeError Term
            fix x' (Right m'') (Right tau'') = Right (Abstract (bTranslationVar x', tau'') m'')
            fix _ (Left te) (Right _) = Left (ChainError1 "occurred in b-translation (term), abstraction / body" 42 te)
            fix _ (Right _)  (Left te) = Left (ChainError1 "occurred in b-translation (term), abstraction / abstracted var type" 43 te)
            fix _ (Left te1)  (Left te2) = Left (ChainError2 "occurred in b-translation (term), abstraction / both" 44 te1 te2)
        bTranslationTermHelperHelper context'' (Apply m'''' n'''') =  fix m''' n'''
          where
            m''' :: Either TypeError Term
            m''' = bTranslationTermHelperHelper context'' m''''
            n''' :: Either TypeError Term
            n''' = bTranslationTermHelperHelper context'' n''''
            fix :: Either TypeError Term -> Either TypeError Term -> Either TypeError Term
            fix (Right m'') (Right n'') = Right (Apply m'' n'')
            fix (Left te) (Right _) = Left (ChainError1 "occurred in b-translation (term), application / right" 45 te)
            fix (Right _) (Left te) = Left (ChainError1 "occurred in b-translation (term) application / left" 46 te)
            fix (Left te1) (Left te2) = Left (ChainError2 "occurred in b-translation (term) application / both" 47 te1 te2)
        bTranslationTermHelperHelper _ Zero = Right (Pair (Abstract ("&alpha;", Function Nat Nat) Zero, Abstract ("&alpha;", Function Nat Nat) Zero))
        bTranslationTermHelperHelper _ Succ = Right (Abstract ("x", natb) (Pair (Abstract ("&alpha;", Function Nat Nat) (Apply Succ (Apply val (Variable "&alpha;"))), Abstract ("&alpha;", Function Nat Nat) (Apply mod' (Variable "&alpha;")))))
          where
            val = Value (Variable "x")
            mod' = Modulus (Variable "x")
        bTranslationTermHelperHelper (Context _) (Rec rho) = fix tau ke'
          where
            tau :: Either TypeError Type
            tau = bTranslationType rho
            fixContext ::  Either TypeError Type ->  Either TypeError Context
            fixContext (Right sigma) =  Right (Context (Map.fromList [("a", sigma), ("&alpha;", Function Nat Nat), ("k", Nat), ("h", natb), ("f",  Function natb (Function sigma sigma))]))
            fixContext (Left te) = Left (ChainError1 "occurred in computing the context" 48 te)
            context'' :: Either TypeError Context
            context'' = fixContext tau
            fix' :: Either TypeError Type -> Either TypeError Term
            fix' (Right sigma) = Right (Apply (Apply (Rec sigma) (Variable "a"))  (Abstract ("k", Nat) (Apply (Variable "f") (Pair (p1, p2)))))
            fix' (Left te) = Left (ChainError1 "occurred in computing first argument for ke extension" 49 te)
            g :: Either TypeError Term
            g = fix' tau
            f :: Term
            f = Variable "h"
            p1 :: Term
            p1 = Abstract ("&alpha;", Function Nat Nat) (Variable "k")
            p2 :: Term
            p2 = Abstract ("&alpha;", Function Nat Nat) Zero
            fixKe :: Either TypeError Term -> Either TypeError Context -> Either TypeError Term
            fixKe (Right g') (Right context''') = ke context''' rho g' f
            fixKe (Left te) (Right _) = Left (ChainError1 "occurred in computing ke / context" 50 te)
            fixKe (Right _) (Left te) = Left (ChainError1 "occurred in computing ke / rho^b" 51 te)
            fixKe (Left te1) (Left te2) = Left (ChainError2 "occurred in computing ke / both" 52 te1 te2)
            ke' :: Either TypeError Term
            ke' = fixKe g context''
            fix :: Either TypeError Type -> Either TypeError Term -> Either TypeError Term
            fix (Right sigma) (Right ke'') =  Right (Abstract ("a", sigma)  (Abstract ("f", Function natb (Function sigma sigma)) (Abstract ("h", natb) ke'')))
            fix (Right _) (Left te) = Left (ChainError1 "occurred in b-translation (term), rec / ke" 53 te)
            fix (Left te) (Right _) = Left (ChainError1 "occurred in b-translation (term), rec / rho^b" 54 te)
            fix (Left te1) (Left te2) = Left (ChainError2 "occurred in b-translation (term), rec" 55 te1 te2)
        bTranslationTermHelperHelper context'' m'' = fix tc
          where
            tc :: Either TypeError Type
            tc = typeCheck context'' m''
            fix :: Either TypeError Type -> Either TypeError Term
            fix (Left te) = Left (ChainError1 "occurred in b-translation (term), unencodable term" 56 te)
            fix (Right _) = Left (BTranslationTermError "unencodable term for b-translation" m)

bTranslationTermNormal :: Context -> Term -> Either TypeError Term
bTranslationTermNormal context term = fix context' original
  where
    context' :: Either TypeError Context 
    context' = bTranslationContext context
    original :: Either TypeError Term
    original = bTranslationTerm context term
    fix :: Either TypeError Context  -> Either TypeError Term -> Either TypeError Term
    fix (Left te1) (Left te2) = Left (ChainError2 "occurred in b-translation (term, normal) / both" 1001 te1 te2)
    fix (Right _) (Left te)   = Left (ChainError1 "occurred in b-translation (term, normal) / context" 1002 te)
    fix (Left te) (Right _)   = Left (ChainError1 "occurred in b-translation (term, normal) / term" 1003 te)
    fix (Right context'') (Right m) = normalize context'' m

modulusOfContinuity :: Context -> Term -> Either TypeError Term
modulusOfContinuity context term = modulusOfContinuityHelper (typeCheck context term) context term
  where
    modulusOfContinuityHelper :: Either TypeError Type ->  Context -> Term -> Either TypeError Term
    modulusOfContinuityHelper (Left te) context term =  Left te
    modulusOfContinuityHelper (Right tau) context term
      | tau == Function (Function Nat Nat) Nat = modulusOfContinuityHelperHelper context term
      | otherwise  = Left (ModulusOfContinuityError "occurred in modulus of continuity" tau)
      where
        modulusOfContinuityHelperHelper :: Context -> Term -> Either TypeError Term
        modulusOfContinuityHelperHelper context term = fix context' original
          where
            omega :: Term
            omega = Abstract ("f", natb) (Pair (pLeft, pRight))
            pLeft :: Term
            pLeft = Abstract ("&alpha;", Function Nat Nat) (Apply (Variable "&alpha;") (Apply  (Value (Variable "f")) (Variable "&alpha;")))
            mLeft :: Term
            mLeft = Apply (Modulus (Variable "f")) (Variable "&alpha;") 
            mRight :: Term 
            mRight = Apply Succ (Apply (Value (Variable "f")) (Variable "&alpha;"))
            pRight :: Term
            pRight = Abstract ("&alpha;", Function Nat Nat) (Max mLeft mRight)
            context' :: Either TypeError Context
            context' = bTranslationContext context
            original :: Either TypeError Term
            original = bTranslationTerm context term
            fix :: Either TypeError Context -> Either TypeError Term -> Either TypeError Term
            fix (Left te1) (Left te2) = Left (ChainError2 "occurred in modulus of continuity / both" 2001 te1 te2)
            fix (Right _) (Left te) = Left (ChainError1 "occurred in modulus of continuity / context" 2002 te)
            fix (Left te) (Right _) = Left (ChainError1 "occurred in modulus of continuity / term" 2003 te)
            fix (Right context'') (Right m) = normalize context'' (Modulus (Apply m omega))

---------------------------------------------------
-------------------- EXAMPLES ---------------------
---------------------------------------------------

-- |Empty context (used for closed terms)
empty :: Context
empty = Context Map.empty

-- |Addition example
term00 :: Term
term00 = Abstract ("x" , Nat) $ Abstract ("y", Nat)  $ Apply (Apply (Apply (Rec Nat) $ Variable "x") sub) $ Variable "y"
  where
    sub :: Term
    sub = Abstract ("u", Nat) $ Abstract ("v", Nat) $ Apply Succ $ Variable "v"
context00 :: Context
context00 = empty
r :: Term
r =  term00


-- |Example 01
term01 :: Term
term01 = Apply (Abstract ("x", Function Nat Nat) $ Variable "x") $ Variable "z"
context01 :: Context
context01 = Context (Map.fromList [("z", Function Nat Nat)])

-- |Example 02
term02 :: Term
term02 = Apply (Abstract ("x", Function Nat Nat) (Variable "x")) (Abstract ("x", Nat) (Variable "x"))
context02 :: Context
context02 = empty

-- |Example 03 (numeral 3)
term03 :: Term
term03 = numeral 3
context03 :: Context
context03 = empty

-- |Example 04
term04 :: Term
term04 = Rec Nat
context04 :: Context
context04 = empty

-- |Example 05
term05 :: Term
term05 = Apply (Abstract ("x", Nat) (Pair (Variable "x", Variable "x"))) (Variable "z")
context05 :: Context
context05 = empty

-- |Example 06
term06 :: Term
term06 = Apply (Apply (Apply (Rec Nat) (Apply Succ Zero)) (Variable "h")) Zero
context06 :: Context
context06 = Context (Map.fromList [("h", Function Nat (Function Nat Nat))])

-- |Example 07 (reduces to numeral (c + d)), 
c :: Integer
d :: Integer
(c, d) = (3, 10) -- as it appears in the slides
term07 :: Term
term07 = Apply (Apply r (numeral c)) (numeral d)
context07 :: Context
context07 = empty

-- |Example 08
term08 :: Term
term08 = Max t s
  where
    t = Apply (Abstract ("x", Nat) (Variable "x")) (Variable "b")
    s = Variable "b"
context08 :: Context
context08 = Context (Map.fromList [("b", Nat)])

-- |Example 09
term09 :: Term
term09 = Apply (Variable "b") (Apply (Variable "b") (Apply (Variable "b") (Apply (Variable "a") (Variable "b"))))
context09 :: Context
context09 = Context (Map.fromList [("b", Function Nat Nat), ("a", Nat)])

-- |Example 10
term10 :: Term
term10 = Rec (Function Nat (Function Nat Nat))
context10 :: Context
context10 = Context (Map.fromList [("b", Function Nat Nat), ("a", Nat)])

-- |Example 11
term11 :: Term
term11 = Abstract ("h", Nat) (Apply (Apply r (Variable "h")) (numeral 5))
context11 :: Context
context11 = empty

-- |Addition example
term12 :: Term
term12 = Abstract ("x" , Nat) $ Abstract ("y", Nat)  $ Apply (Apply (Apply (Rec Nat) $ Variable "x") sub) $ Variable "y"
  where
    sub :: Term
    sub = Abstract ("u", Nat) $ Abstract ("v", Nat) $ Apply (Apply r $ Variable "v") $ Variable "u"
context12 :: Context
context12 = empty

term13 :: Term
term13 = Apply (Apply term12 $ numeral c) $ numeral d
context13 :: Context
context13 = empty

term14 :: Term
term14 = Abstract ("a", Function Nat Nat) Zero
context14 :: Context
context14 = empty

inputStructure01 :: InputStructure
inputStructure01 = InputStructure "E" context01 term01

testString01 :: String
testString01 = "{\"category\":\"INPUTSTRUCTURE\",\"command\":\"E\",\"term\":{\"category\":\"ABSTRACT\",\"abvar\":\"c\",\"abtype\":{\"category\":\"NAT\"},\"body\":{\"category\":\"ZERO\"}},\"context\":{\"declarations\":[]}}"

aesonTestType01 :: Maybe Type
aesonTestType01 = decode "{\"category\":\"NAT\"}" :: Maybe Type

aesonTestTerm01 :: Maybe Term
aesonTestTerm01 = decode "{\"category\":\"ZERO\"}" :: Maybe Term

aesonTestDeclaration02 :: Maybe Context
aesonTestDeclaration02 = decode "{\"declarations\":[{\"vn\":\"a\",\"t\":{\"category\":\"NAT\"}}]}"
