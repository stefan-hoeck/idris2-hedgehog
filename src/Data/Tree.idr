module Data.Tree

import Data.List
import Data.List1
import Data.String

%default total

--------------------------------------------------------------------------------
--          Finite Trees
--------------------------------------------------------------------------------

mutual

  ||| A finite rose tree
  public export
  record Tree (a : Type) where
    constructor MkTree
    value : a
    forest : Forest a

  ||| A finite forest of trees
  public export
  Forest : Type -> Type
  Forest = List . Tree

--------------------------------------------------------------------------------
--          Creating Trees
--------------------------------------------------------------------------------

public export
singleton : a -> Tree a
singleton a = MkTree a []

public export
replicate : (width : Nat) -> (depth : Nat) -> a -> Tree a
replicate _         0 x = MkTree x []
replicate width (S k) x = MkTree x $ replicate width (replicate width k x)

||| Unfold a tree up to the given depth.
public export
unfold : (depth : Nat) -> (f : s -> (a,List s)) -> s -> Tree a
unfold 0     f s = MkTree (fst $ f s) []
unfold (S k) f s = let (a,ss) = f s
                    in MkTree a (map (unfold k f) ss)

--------------------------------------------------------------------------------
--          Flattening Trees
--------------------------------------------------------------------------------

zipWithKeep : (a -> a -> a) -> List a -> List a -> List a
zipWithKeep f [] ys = ys
zipWithKeep f xs [] = xs
zipWithKeep f (x :: xs) (y :: ys) = f x y :: zipWithKeep f xs ys

public export
flatten : Tree a -> List a
flatten (MkTree v vs) = v :: flattenF vs
  where flattenF : Forest a -> List a
        flattenF []        = Nil
        flattenF (x :: xs) = flatten x ++ flattenF xs

public export
layers : Tree a -> List (List a)
layers (MkTree v vs) = [v] :: layersF vs
  where layersF : Forest a -> List (List a)
        layersF []        = Nil
        layersF (x :: xs) = zipWithKeep (++) (layers x) (layersF xs)

--------------------------------------------------------------------------------
--          Accessing Elements
--------------------------------------------------------------------------------

public export
index : List Nat -> Tree a -> Maybe a
index []        x = Just x.value
index (y :: ys) x = ix y x.forest >>= index ys
  where ix : Nat -> List b -> Maybe b
        ix _ []            = Nothing
        ix 0     (z :: _)  = Just z
        ix (S k) (_ :: zs) = ix k zs

--------------------------------------------------------------------------------
--          Functor and Monad Implementations
--------------------------------------------------------------------------------

-- All implementations are boilerplaty to satisfy the totality checker.
foldlTree : (a -> e -> a) -> a -> Tree e -> a
foldlTree f acc (MkTree v vs) = foldlF (f acc v) vs
  where foldlF : a -> Forest e -> a
        foldlF y []        = y
        foldlF y (x :: xs) = foldlF (foldlTree f y x) xs

foldrTree : (e -> a -> a) -> a -> Tree e -> a
foldrTree f acc (MkTree v vs) = f v (foldrF acc vs)
  where foldrF : a -> Forest e -> a
        foldrF y []        = y
        foldrF y (x :: xs) = foldrTree f (foldrF y xs) x

traverseTree : Applicative f => (a -> f b) -> Tree a -> f (Tree b)
traverseTree fun (MkTree v vs) = [| MkTree (fun v) (traverseF vs) |]
  where traverseF : Forest a -> f (Forest b)
        traverseF []        = pure []
        traverseF (x :: xs) = [| traverseTree fun x :: traverseF xs |]

mapTree : (a -> b) -> Tree a -> Tree b
mapTree f (MkTree v vs) = MkTree (f v) (mapF vs)
  where mapF : Forest a -> Forest b
        mapF []       = []
        mapF (h :: t) = mapTree f h :: mapF t

bindTree : Tree a -> (a -> Tree b) -> Tree b
bindTree (MkTree va tas) f =
  let MkTree vb tbs = f va
   in MkTree vb (tbs ++ bindF tas)

  where bindF : Forest a -> Forest b
        bindF []        = []
        bindF (x :: xs) = bindTree x f :: bindF xs

apTree : Tree (a -> b) -> Tree a -> Tree b
apTree tf ta = bindTree tf \f => mapTree (apply f) ta

joinTree : Tree (Tree a) -> Tree a
joinTree (MkTree (MkTree va tas) ftas) =
  MkTree va $ tas ++ joinF ftas

  where joinF : Forest (Tree a) -> Forest a
        joinF []        = []
        joinF (x :: xs) = joinTree x :: joinF xs

eqTree : Eq a => Tree a -> Tree a -> Bool
eqTree (MkTree x xs) (MkTree y ys) = x == y && eqF xs ys
  where eqF : Forest a -> Forest a -> Bool
        eqF [] []       = True
        eqF [] (_ :: _) = False
        eqF (_ :: _) [] = False
        eqF (x :: xs) (y :: ys) = eqTree x y && eqF xs ys

--------------------------------------------------------------------------------
--          Visualizing Trees
--------------------------------------------------------------------------------

export
drawTree : Tree String -> String
drawTree  = unlines . draw
  where
    drawForest : Forest String -> String
    drawForest  = unlines . map drawTree

    draw : Tree String -> List String
    draw (MkTree x ts0) = (forget $ lines x) ++ subTrees ts0
      where
        shift : String -> String -> List String -> List String
        shift first other tails =
          zipWith (++) (first :: replicate (length tails) other) tails

        subTrees : Forest String -> List String
        subTrees []      = []
        subTrees [t]     = "│" :: shift "└╼" "  " (draw t)
        subTrees (t::ts) = "│" :: shift "├╼" "│ " (draw t) ++ subTrees ts

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

public export %inline
Eq a => Eq (Tree a) where
  (==) = eqTree

public export %inline
Foldable Tree where
  foldl  = foldlTree
  foldr  = foldrTree
  null _ = False

public export %inline
Functor Tree where
  map = mapTree

public export %inline
Applicative Tree where
  pure a = MkTree a Nil
  (<*>)  = apTree

public export %inline
Monad Tree where
  (>>=) = bindTree
  join  = joinTree

public export %inline
Traversable Tree where
  traverse = traverseTree
