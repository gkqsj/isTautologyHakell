import Data.List
data Prop = Const Bool | Var Char | Not Prop | And Prop Prop | Or Prop Prop | Implies Prop Prop | Iff Prop Prop deriving (Eq,Show,Read)

type Subst = [(Char,Bool)]

eval :: Subst -> Prop -> Bool
eval _   (Const const)                           = const
eval sub (Var varchar)                           = troca sub varchar
eval sub (Not notprop)                           = not (eval sub notprop)
eval sub (And (andprop1) (andprop2))             = (eval sub andprop1) && (eval sub andprop2)
eval sub (Or (orprop1) (orprop2))                = (eval sub orprop1) || (eval sub orprop2)
eval sub (Implies (impliesprop1) (impliesprop2)) = (not(eval sub impliesprop1) || eval sub impliesprop2)
eval sub (Iff (iffprop1) (iffprop2))             = (eval sub iffprop1 == eval sub iffprop2)

troca :: Subst -> Char -> Bool
troca (x:xs) char
 |fst x == char = snd x
 |otherwise = troca xs char

vars :: Prop -> [Char]
vars (Const const)                           = []
vars (Var varchar)                           = [varchar]
vars (Not notprop)                           = vars notprop
vars (And (andprop1) (andprop2))             = (vars andprop1) ++ (vars andprop2)
vars (Or (orprop1) (orprop2))                = (vars orprop1) ++ (vars orprop2)
vars (Implies (impliesprop1) (impliesprop2)) = (vars impliesprop1) ++ (vars impliesprop2)
vars (Iff (iffprop1) (iffprop2))             = (vars iffprop1) ++ (vars iffprop2)

int2bin :: Int -> [Int]
int2bin 0 = [0]
int2bin 1 = [1]
int2bin n 
 | n `mod` 2 == 1 = int2bin (n `div` 2) ++ [1]
 | n `mod` 2 == 0 = int2bin (n `div` 2) ++ [0]

bin2int :: [Int] -> Int
bin2int [] = 0
bin2int (x:xs) = (x*2^(length xs)) + (bin2int xs)

checkSize :: Int -> [Int] -> [Int]
checkSize x lista
 |x == length lista = lista
 |otherwise         = checkSize x ([0] ++ lista)

decrement :: Int -> [Int] -> [Int]  
decrement x lista = checkSize x (int2bin ((bin2int lista) - 1))

generateBase :: Int -> [Bool]
generateBase 0 = []
generateBase x = [False] ++ generateBase (x-1)

generateCase :: [Int] -> [Bool]
generateCase [] = []
generateCase lista
 |head lista == 1 = [True]  ++ generateCase (tail lista)
 |head lista == 0 = [False] ++ generateCase (tail lista)


bools :: Int -> [[Bool]]
bools x = boolsAux x (int2bin ((2^x) - 1))

boolsAux :: Int -> [Int] -> [[Bool]]
boolsAux x lista
 |(foldr (+) 0 lista) == 0 = [generateBase x]
 |otherwise                = [(generateCase lista)] ++ boolsAux x (decrement x lista)

substs :: Prop -> [Subst]
substs props = placeVars (nub (vars props)) (bools (length (nub (vars props))))

placeVars :: [Char] -> [[Bool]] -> [Subst]
placeVars _ [] = []
placeVars chars lista = [addVar chars (head lista)] ++ placeVars chars (tail lista)

addVar :: [Char] -> [Bool] -> Subst
addVar _ [] = []
addVar [] _ = []
addVar char bool = [((head char),(head bool))] ++ (addVar (tail char) (tail bool))

isTaut :: Prop -> Bool
isTaut props = isTautAux (substs props) props

isTautAux :: [Subst] -> Prop -> Bool
isTautAux [] _ = True
isTautAux dic props
 |(eval (head dic) props) == False = False
 |otherwise                        = isTautAux (tail dic) props