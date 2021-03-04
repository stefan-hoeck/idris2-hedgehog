module Data.Cotree

import Data.Colist
import Data.Maybe

%default total

--------------------------------------------------------------------------------
--          Cotrees: Potentially infinte trees
--------------------------------------------------------------------------------

mutual
  ||| A potentially infinite rose tree
  public export
  record Cotree (a : Type) where
    constructor MkCotree
    value  : a
    forest : Inf (Coforest a)

  ||| A potentially finit stream of trees
  public export
  Coforest : Type -> Type
  Coforest = Colist . Cotree

public export
singleton : a -> Cotree a
singleton a = MkCotree a Nil

public export
unfold : (f : b -> (a,Colist b)) -> b -> Cotree a
unfold f vb = let (va,bs) = f vb
                   in MkCotree va $ unfoldF bs

  where unfoldF : Colist b -> Coforest a
        unfoldF []       = []
        unfoldF (h :: t) = unfold f h :: unfoldF t

public export
iterate : (f : a -> Colist a) -> a -> Cotree a
iterate f a = unfold (\v => (v, f v)) a

public export
expand : (a -> Colist a) -> Cotree a -> Cotree a
expand f (MkCotree v vs) = let MkCotree v2 vs2 = iterate f v
                            in MkCotree v2 (run vs vs2)
  where run : Coforest a -> Coforest a -> Coforest a
        run []        ys = ys
        run (x :: xs) ys = expand f x :: run xs ys

--------------------------------------------------------------------------------
--          Functor and Applicative
--------------------------------------------------------------------------------

public export
mapCotree : (a -> b) -> Cotree a -> Cotree b
mapCotree f (MkCotree v vs) = MkCotree (f v) (mapForest vs)
  where mapForest : Coforest a -> Coforest b
        mapForest []       = []
        mapForest (h :: t) = mapCotree f h :: mapForest t

public export
interleave : Cotree (a -> b) -> Cotree a -> Cotree b
interleave tf@(MkCotree vf fs) ta@(MkCotree va as) =
  MkCotree (vf va) (interleaveFs fs)

  where interleaveAs : Coforest a -> Coforest b
        interleaveAs []       = []
        interleaveAs (h :: t) = interleave tf h :: interleaveAs t

        interleaveFs : Coforest (a -> b) -> Coforest b
        interleaveFs []       = interleaveAs as
        interleaveFs (h :: t) = interleave h ta :: interleaveFs t
                       
public export
bind : Cotree a -> (a -> Cotree b) -> Cotree b
bind (MkCotree v vs) f = let MkCotree w ws = f v
                       in MkCotree w (run vs ws)
  where run : Coforest a -> Coforest b -> Coforest b
        run []        ys = ys
        run (x :: xs) ys = bind x f :: run xs ys
                       
public export
bindMaybe : Cotree (Maybe a) -> (a -> Cotree (Maybe b)) -> Cotree (Maybe b)
bindMaybe (MkCotree mv tas) f =
  case map f mv of
       Nothing => MkCotree Nothing (run tas Nil)
       Just (MkCotree mb tbs) => MkCotree mb (run tas tbs)

  where run : Coforest (Maybe a) -> Coforest (Maybe b) -> Coforest (Maybe b)
        run [] ys        = ys
        run (x :: xs) ys = bindMaybe x f :: run xs ys

--------------------------------------------------------------------------------
--          Shrinking
--------------------------------------------------------------------------------

public export
shrink : (maxSteps : Nat) -> Cotree (Maybe a) -> List a
shrink maxSteps x = run maxSteps [x]
  where run : Nat -> Coforest (Maybe a) -> List a
        run _ Nil          = Nil
        run 0 _            = Nil
        run (S k) (h :: t) = case h.value of
                               Just a  => a :: run k h.forest
                               Nothing => run k t

public export
mapShrink : (maxSteps : Nat) -> (a -> Maybe b) -> Cotree a -> List b
mapShrink ms f = shrink ms . mapCotree f

public export
shrinkIf : (maxSteps : Nat) -> (a -> Bool) -> Cotree a -> List a
shrinkIf ms p = mapShrink ms (\a => if p a then Just a else Nothing)

||| Prunes a cotree up to the given depth and width.
public export
pruneTo : (width : Nat) -> (depth : Nat) -> Cotree a -> Cotree a
pruneTo _ 0     (MkCotree v _ ) = MkCotree v Nil
pruneTo w (S d) (MkCotree v vs) = MkCotree v $ (map (pruneTo w d) $ keep w vs)
  where keep : Nat -> Colist t -> Colist t
        keep _ [] = []
        keep 0 _  = []
        keep (S k) (x :: xs) = x :: keep k xs

||| Removes all children from a cotree
public export
prune : Cotree a -> Cotree a
prune = pruneTo 0 0

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

public export
Functor Cotree where
  map = mapCotree

public export
Applicative Cotree where
  pure  = singleton
  (<*>) = interleave

--------------------------------------------------------------------------------
--          Filtering
--------------------------------------------------------------------------------

public export
takeUntil : (a -> Bool) -> Cotree a -> Cotree a
takeUntil f (MkCotree v vs) = if f v then MkCotree v []
                                     else MkCotree v (takeUntilF vs)
  where takeUntilF : Coforest a -> Coforest a
        takeUntilF []        = vs
        takeUntilF (MkCotree x xs :: ts) =
          if f x
             then [MkCotree x []]
             else MkCotree x (takeUntilF xs) :: takeUntilF ts

public export
takeBeforeNothing : Cotree (Maybe a) -> Maybe (Cotree a)
takeBeforeNothing (MkCotree Nothing _) = Nothing
takeBeforeNothing (MkCotree (Just v) vs) = Just (MkCotree v (run vs))
  where run : Coforest (Maybe a) -> Coforest a
        run []                             = []
        run ((MkCotree Nothing _) :: _)    = []
        run ((MkCotree (Just v) vs) :: ts) = MkCotree v (run vs) :: run ts

public export
takeBefore : (a -> Bool) -> Cotree a -> Maybe (Cotree a)
takeBefore f = takeBeforeNothing . map (\a => toMaybe (f a) a)

public export %inline
takeWhile : (a -> Bool) -> Cotree a -> Maybe (Cotree a)
takeWhile f = takeBefore (not . f)

public export %inline
mapMaybe : (a -> Maybe b) -> Cotree a -> Maybe (Cotree b)
mapMaybe f = takeBeforeNothing . map f

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

halves : Int -> Cotree Int
halves = iterate (drop 1 . takeUntil (0 ==) . iterate next)
  where next : Int -> Int
        next = (`div` 2)

chars : Char -> Cotree Char
chars = iterate (drop 1 . takeUntil ('0' ==) . iterate next)
  where next : Char -> Char
        next = chr . (\x => x - 1) . ord

bools : Cotree Bool
bools = iterate next True
  where next : Bool -> Colist Bool
        next True  = [False]
        next False = []

export
triples : Cotree (Int,Char,Bool)
triples = (,,) <$> halves 10000 <*> chars 'z' <*> bools

export
crit1 : (Int,Char,Bool) -> Bool
crit1 (x, y, z) =  (isDigit y && z)
                || (x `mod` 2 == 0 && x > 3)
