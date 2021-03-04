module Hedgehog.Internal.Shrink

import Data.Colist
import Data.Cotree
import Data.Nat

import Hedgehog.Internal.Util

%default total

public export
halvesInteger : Integer -> Colist Integer
halvesInteger = iterateBefore0 (`safeDiv` 2)

public export %inline
halves : ToInteger a => a -> Colist a
halves = map fromInteger . halvesInteger . toInteger

public export
towardsInteger : (destination, val : Integer) -> Colist Integer
towardsInteger dest x =
  if dest == x then []
               else let diff = (x `safeDiv` 2) - (dest `safeDiv` 2)
                     in dest `consNub` map (x -) (halvesInteger diff)

||| Shrink an integral number by edging towards a destination.
|||
||| >>> towards 0 100
||| [0,50,75,88,94,97,99]
|||
||| >>> towards 500 1000
||| [500,750,875,938,969,985,993,997,999]
|||
||| >>> towards (-50) (-26)
||| [-50,-38,-32,-29,-27]
|||
||| Note we always try the destination first, as that is the optimal shrink.
public export
towards : ToInteger a => (destination, val : a) -> Colist a
towards dest x = map fromInteger
               $ towardsInteger (toInteger dest) (toInteger x)

public export
towardsDouble : Double -> Double -> Colist Double
towardsDouble destination x =
  if destination == x
    then []
    else let diff = x - destination
             ok = (/= x)
          in takeWhile ok .  map (x -) $ iterate (/ 2) diff

public export
removes : Nat -> List a -> Colist $ List a
removes 0     _ = []
removes (S n) x = run (S n) [] x
  where run : Nat -> List a -> List a -> Colist $ List a
        run 0     _   []       = [[]]
        run 0     xs (y :: ys) = let rest = run n [y] ys
                                  in (y :: ys) :: map (prepRev xs) rest
        run (S k) _  []        = []
        run (S k) xs (y :: ys) = run k (y :: xs) ys

||| All ways a list can be split
|||
||| Note: The first list in the triple will be in reverse order
public export
splits : (a -> b) -> List a -> List (List a, b, List a)
splits _ []        = []
splits f (x :: xs) = run [] x xs
  where run : List a -> a -> List a -> List (List a, b, List a)
        run xs x []          = [(xs,f x,[])]
        run xs x l@(y :: ys) = (xs,f x,l) :: run (x::xs) y ys

||| Shrink a list by edging towards the empty list.
|||
||| >>> list [1,2,3]
||| [[],[2,3],[1,3],[1,2]]
|||
||| >>> list "abcd"
||| ["","cd","ab","bcd","acd","abd","abc"]
|||
||| Note we always try the empty list first, as that is the optimal shrink.
public export
list : (minLength : Nat) -> List a -> Colist $ List a
list ml xs = let diff = length xs `minus` ml
              in concatMapColist (`removes` xs) (halves diff)

public export
interleave : (minLength : Nat) -> List (Cotree a) -> Cotree (List a)
interleave ml ts = MkCotree (map value ts) $ dropThenShrink (list ml ts)
  where shrinkOne :  List (List (Cotree a), Coforest a, List (Cotree a))
                  -> Coforest (List a)
        shrinkOne []                      = []
        shrinkOne ((xs,[]   ,ys) :: rest) = shrinkOne rest
        shrinkOne ((xs,t::ts,ys) :: rest) = interleave ml (prepRev xs (t::ys)) ::
                                            shrinkOne ((xs,ts,ys) :: rest)

        dropThenShrink : Colist (List $ Cotree a) -> Coforest (List a)
        dropThenShrink []        = shrinkOne (splits (\t => t.forest) ts)
        dropThenShrink (x :: xs) = interleave ml x :: dropThenShrink xs

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

HalvesFrom10 : List Int
HalvesFrom10 = take 10 $ halves 10

halvesFrom10Test : HalvesFrom10 = [10,5,2,1]
halvesFrom10Test = Refl

Towards0_100 : List Int
Towards0_100 = take 10 $ towards 0 100

Towards500_1000 : List Int
Towards500_1000 = take 10 $ towards 500 1000

Towards50_26 : List Int
Towards50_26 = take 10 $ towards (-50) (-26)

towards0_100Test : Towards0_100 = [0,50,75,88,94,97,99]
towards0_100Test = Refl

towards500_1000Test : Towards500_1000 = [500,750,875,938,969,985,993,997,999]
towards500_1000Test = Refl

towards50_26Test : Towards50_26 = [-50,-38,-32,-29,-27]
towards50_26Test = Refl

TowardsFloat0_100 : List Double
TowardsFloat0_100 = take 7 $ towardsDouble 0.0 100

TowardsFloat1_5 : List Double
TowardsFloat1_5 = take 7 $ towardsDouble 1 0.5

towardsFloat0_100Test : TowardsFloat0_100 = [0.0,50.0,75.0,87.5,93.75,96.875,98.4375]
towardsFloat0_100Test = Refl

towardsFloat1_5Test : TowardsFloat1_5 = [1.0,0.75,0.625,0.5625,0.53125,0.515625,0.5078125]
towardsFloat1_5Test = Refl

Removes2_2 : List $ List Int
Removes2_2 = take 10 $ removes 2 [1,2]

removes2_2Test : Removes2_2 = [[]]
removes2_2Test = Refl

Removes2_3 : List $ List Int
Removes2_3 = take 10 $ removes 2 [1,2,3]

removes2_3Test : Removes2_3 = [[3]]
removes2_3Test = Refl

Removes2_4 : List $ List Int
Removes2_4 = take 10 $ removes 2 [1,2,3,4]

removes2_4Test : Removes2_4 = [[3,4],[1,2]]
removes2_4Test = Refl

Removes2_5 : List $ List Int
Removes2_5 = take 10 $ removes 2 [1,2,3,4,5]

removes2_5Test : Removes2_5 = [[3,4,5],[1,2,5]]
removes2_5Test = Refl

Removes2_6 : List $ List Int
Removes2_6 = take 10 $ removes 2 [1,2,3,4,5,6]

removes2_6Test : Removes2_6 = [[3,4,5,6],[1,2,5,6],[1,2,3,4]]
removes2_6Test = Refl

Removes3_10 : List $ List Int
Removes3_10 = take 10 $ removes 3 [1,2,3,4,5,6,7,8,9,10]

removes3_10Test : Removes3_10 = [[4,5,6,7,8,9,10],[1,2,3,7,8,9,10],[1,2,3,4,5,6,10]]
removes3_10Test = Refl

List3 : List $ List Int
List3 = take 10 $ list 0 [1,2,3]

List4 : List $ List Int
List4 = take 10 $ list 0 [1,2,3,4]

List5 : List $ List Int
List5 = take 10 $ list 2 [1,2,3,4,5]

list3Test : List3 = [[],[2,3],[1,3],[1,2]]
list3Test = Refl

list4Test : List4 = [[],[3,4],[1,2],[2,3,4],[1,3,4],[1,2,4],[1,2,3]]
list4Test = Refl

list5Test : List5 = [[4,5],[2,3,4,5],[1,3,4,5],[1,2,4,5],[1,2,3,5],[1,2,3,4]]
list5Test = Refl
