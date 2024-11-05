module Prueba where

import Prelude hiding (head)

num :: Integer
num = 2 + 6

square :: Integer -> Integer
square x = x * x

exOr :: Bool -> Bool -> Bool
exOr x y = (x || y) && not (x && y)

{- pattern matching -}
exOr2 :: Bool -> Bool -> Bool
exOr2 True y = not y
exOr2 False y = y

min :: Integer -> Integer -> Integer
min x y = if x <= y then x else y



{- 
La conversion entre los dos tipos de enteros se debe hacer en
forma explıcita a traves de las funciones: 
-}

{- 
fromInteger :: Integer -> Int
toInteger :: Int -> Integer
 -}
{- 
Ejecutamos min(toInteger numInt) num  Resultado es 8 Integer
-}

{- 
La conversion entre un caracter y su codificacion se hace a
traves de las siguientes funciones: 
-}
{- 
fromEnum :: Char -> Int
toEnum :: Int -> Char
 -}
{- 
Las funciones show y read permiten convertir entre valores de
otros tipos y String.
Por ejemplo,
show (4 + 3) ----> "7"
read "3" + 4 ---->  7 
-}

{- 
Operador de division real: /
Hay funciones de conversion hacia y desde los enteros.
ceiling :: Float -> Integer
floor :: Float -> Integer
round :: Float -> Integer
fromInteger :: Integer -> Float
fromIntegral :: Int -> Float 
-}


------------------------------------------------------------------------------------------------------------------

{- 
Funciones sobre Tuplas
Se suele usar pattern matching: 
-}
nombre :: (String, Int, Int) -> String
nombre (n, e,s) = n

{- 
Al aplicarse, los componentes del patron se matchean con los
componentes del argumento.
nombre ("Pedro", 44, 60000) ------> "Pedro" 
-}

{- 
Se pueden ignorar componentes.
edad ( , e, ) = e
sueldo ( , ,s) = s 
-}

{- 
Se pueden forzar componentes usando literales.
esPedro ("Pedro", , ) = True
esPedro ( , , ) = False 
-}

{- 
Sinonimos de Tipos
En Haskell podemos dar nombres a los tipos.
Al usar un sinonimo se tiene el mismo efecto que al usar el
tipo que representa.
Ejemplos: 
-}
type Coord = (Int, Int)


{- 
Una lista combina en un mismo objeto a un numero arbitrario
de valores, todos de un mismo tipo.
Ejemplos 
-}
listaNumeros :: [Int]
listaNumeros = [8, 2, 3, 1, 24]
{- [8, 2, 3, 1, 24] :: [Int] -}

type Empleado = (String, Int, Int)
listaEmpleados :: [Empleado]
listaEmpleados = [("Juan", 23, 60000), ("Pedro", 44, 60000)]
{- [("Juan", 23, 60000),("Pedro", 44, 60000)] :: [Empleado ] -}

{- 
En general, el tipo [t] consiste en listas de valores:
[v1, ..., vn ] donde v1 :: t, ..., vn :: t 
-}

{- 
Definimos inductivamente a las listas de tipo [t] como:
[ ] - lista vacıa
v : vs - lista con al menos un elemento, donde v :: t y vs :: [t]
-}

{- Funciones sobre Listas -}
{- 
Existe una gran cantidad de funciones sobre listas en Prelude
Ejemplos: (++), (!!), length, replicate, take, drop, reverse,
etc.
Nuevas funciones se definen combinando las anteriores o
usando pattern matching
 -}
dupList xs = xs ++ xs

null [ ] = True
null (_ : _) = False

head (x : _ ) = x

tail ( _ : xs) = xs

{- Listas por Comprension -}

{- 
Notacion que permite construir una lista a partir de una
descripcion de la misma en terminos de otra.
A partir de una lista se generan elementos, que se testean y
transforman para formar los elementos de la lista resultante
 -}

{- Un primer ejemplo: -}
result = [x | x <- [1, 2, 3, 4]] ---- > [1, 2, 3, 4]

{- 
Mas ejemplos:
[x | x ← [1, 2, 3, 4], isEven x ] -----> [2, 4]
[isEven x | x ← [1, 2, 3, 4]] ----->  [False,True, False,True ] isEven transforma primero
[(x + y) | (x, y) ← [(1, 2),(2, 3),(3, 4)]] ----->  [3, 5, 7]
[(x, y) | x ← [1, 2], y ← [3, 4]] ----->  [(1, 3),(1, 4),(2, 3),(2, 4)]
 -}

isEven :: Int -> Bool
isEven x = mod x 2 == 0

evens :: [Int] -> [Int]
evens xs = [x + 1 | x <- xs, isEven x, x > 0]


{- Tipos de Datos Algebraicos -}
{- 
Mediante la definicion de tipos de datos algebraicos
podemos introducir nuevos tipos.
Nos permiten definir:
Enumerados: 
-}
{- data Bool = False | True  -}

data PuntoCardinal = Norte | Sur | Este | Oeste
    deriving (Show, Eq)

{- Productos: -}
data TEmpleado = CEmpleado String Int Int
    deriving (Show, Eq)

esPedro' :: TEmpleado -> Bool
esPedro' (CEmpleado "Pedro" _ _) = True
esPedro' _ = False

{- Alternativas: -}
data Forma = Circulo Float
            | Rectangulo Float Float
    deriving (Show, Eq)

{- 
En general:
data T = C1 t11 ... t1k1
        ...
        | Cn tn1 ... tnkn
donde T es el nuevo tipo a introducir y cada Ci es un
constructor de dicho tipo, que toma ki parametros.
 -}


{- Funciones: area (cuadrado 9.9)  -}
area :: Forma -> Float
area (Circulo r) = 3.14 * r * r
area (Rectangulo b a) = b * a

cuadrado l = Rectangulo l l

------------------------------------------------------------------------------------------------------------------
{- Polimorfismo Parametrico -}
{- 
El polimorfismo parametrico es un mecanismo de tipado que
permite definir funciones y tipos de datos de forma parametrica de
forma tal que puedan manipular valores de distintos tipos de forma
totalmente uniforme.
Ejemplo:
head (x : xs) = x
head [1, 2, 3, 4] -----> 1
head [False,True, False ] -----> False
head [’a’, ’b’, ’c’, ’d’] -----> ’a’
El tipo de head es entonces:
head :: [a] -> a
donde a es una variable de tipo.
 -}
{- Tipo Mas General -}
{- 
head :: [a] -> a es el tipo mas general de head.
Al reemplazar las variables de tipo por tipos particulares se
obtienen instancias del tipo:
[Int] -> Int
[Bool ] -> Bool
[Char ] -> Char
No son instancias:
[Int] -> Char
Bool -> Bool
[a] -> Int
Haskell es capaz de inferir el tipo mas general de una funcion
 -}

--head :: [a] -> a
head2 (x:xs) = x

{- Algunas funciones polimorficas sobre listas -}

{- 
Las siguientes son algunas funciones polimorficas sobre listas
contenidas en el Prelude:
(:) :: a -> [a] -> [a]
(++) :: [a] -> [a] -> [a]
(!!) :: [a] -> Int -> a  -->>>> (posicion del elemento a)
last :: [a] -> a
concat :: [[a]] -> [a]
take :: Int -> [a] -> [a] toma los primeros n elementos de la lista
splitAt :: Int -> [a] -> ([a], [a]) corta la lista en dos en el numero n que diga
reverse :: [a] -> [a]  invierte el orden de los elementos
zip :: [a] -> [b] -> [(a, b)]  dada dos listas arma una lista de pares
unzip :: [(a, b)] -> ([a], [b]) corta la lista de pares en dos listas 
 -}


{- Sobrecarga -}
{- 
En Haskell se utiliza el mismo operador (==) para representar
la igualdad en mas de un tipo.
(==) :: Int -> Int -> Bool
(==) :: Char -> Char -> Bool
(==) :: Bool -> Bool -> Bool
La sobrecarga es otra forma de polimorfismo, dentro del
llamado polimorfismo ad-hoc.
Una funcion sobrecargada puede comportarse de forma
diferente (tener una definicion diferente) para cada tipo.
En Haskell, la definicion de funciones sobrecargadas se hace a
traves del concepto de clase.
El operador (==) tiene el siguiente tipo:
(==) :: Eq a => a -> a -> Bool
 -}
{- CLASES
Una clase especifica una coleccion de tipos a los que se les asocia
un conjunto de operaciones (comunmente llamados metodos).
class Eq a where
(==) :: a -> a -> Bool
(/=) :: a -> a -> Bool
x /= y = not (x == y)
x == y = not (x /= y)
 -}

{- INSTANCIAS
Para declarar que un tipo es miembro de una clase hay que definir
una instancia.
data T = A | B
instance Eq T where
A == A = True
B == B = True
_==_ = False
Para un numero restricto de clases (como Eq, Ord, Show, etc), se
puede pedir que Haskell derive la instancia de una clase en forma
automatica.
data T = A | B
deriving (Eq, Show)
La instancia de la clase Show permite visualizar los valores del tipo
 -}


data T = A | B
    deriving (Eq, Show)

{- instance Eq T where 
    A == A = True
    B == B = True
    _ == _ = False -}


{- Funciones de Alto Orden -}
{- 
Una funcion de alto orden es una funcion que toma una
funcion como parametro o retorna una funcion como
resultado.
En PF las funciones son ciudadanas de primera clase.
Ejemplos de funciones de alto orden:
map :: (a -> b) -> [a] -> [b]
filter :: (a -> Bool) -> [a] -> [a]
zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
Pero tambien take :: Int -> [a] -> [a]  -----> Pasar los dos parametros de forma saturada
es de alto orden debido a que su tipo equivale a:
take :: Int -> ([a] -> [a])  ---> Pasar los parametros de a uno y depues el otro
dado que -> asocia a la derecha.    
 -}
{- 
Ejemplo:
map (+1) [1,2,3] ------> [2,3,4]
filter (>0) [1,2,-1,3] ------> [1,2,3]
zipWith (+) [1,2,3] [4,5,6,7] ------> [5,7,9]
 -}

--zipWith :: (a -> b -> c) -> ([a] -> ([b] -> [c]))

{- Funciones Currificadas -}
{- 
Las funciones en Haskell se representan en forma currificada:
las funciones tienen solo un parametro.
Por ejemplo:
take :: Int -> ([a] -> [a])
puede ser aplicado a un entero, retornando la funcion:
take 3 :: [a] -> [a]
que luego puede ser aplicada a un lista:
(take 3) [’a’, ’b’, ’c’, ’d’, ’e’]
Los parentesis no son necesarios, porque la aplicacion asocia a
la izquierda:
take 3 [’a’, ’b’, ’c’, ’d’, ’e’]
 -}
{- 
Ejemplo:
take 3   ------>  take 3 :: [a] -> [a]
take 3 [1,2,3,4]  ------> [1,2,3]
map (take 3) [[1,2,3,4], [5,6,7], [8,9]] ------> [[1,2,3], [5,6,7], [8,9]]
 -}

{- Currificadas vs no currificadas -}


{- No currificada -}
add :: Num a => (a, a) -> a
add (x, y) = x + y

mult :: Num a => (a, a, a) -> a
mult (x, y, z) = x * y * z


{- Currificada -}
addc :: Num a => a -> a -> a
addc x y = x + y

multc :: Num a => a -> a -> a -> a
multc x y z = x * y * z

zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' f xs ys = map (uncurry f) (zip xs ys)

--zip [x1,...,xn] [y1,...,yn] = [(x1,y1),...]    uncurry f (x1,y1)
--map f [x1,...,xn] = [f x1,..., f xn]           f x1 y1
--Ejemplo: zipWith' addc [1,2,3] [4,5,6]  ------> [5,7,9]

{- 
Ejemplo:
:t addc 3  ------> addc 3 :: (Num a) => a -> a
map (addc 1) [1,2,3]  ------> [2,3,4]
zipWith addc [1,2,3] [4,5,6]  ------> [5,7,9]
 -}

{- Currificacion -}
{- 
Se puede pasar de representacion currificada a no currificada, y
viceversa, usando las siguientes funciones:

curry :: ((a, b) → c) → (a → b → c)
curry f x y = f (x, y)

uncurry :: (a → b → c) → ((a, b) → c)
uncurry f (x, y) = f x y

Ejemplo:
addc = curry add
add = uncurry addc

map (curry add 1) [1,2,3] ------> [2,3,4]
map (addc 1) [1,2,3] ------> [2,3,4]
 -}
