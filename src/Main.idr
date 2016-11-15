module Main

import Effects
import Effect.Perf
import Effect.Random

import Data.HashSet
import Data.SortedSet as SortedSet

Cell : Type
Cell = (Int, Int)

Cells : Type
Cells = HashSet Cell

gosperGun : List Cell
gosperGun =
  [(1,5),  (2,5),  (1,6),  (2,6),
   (11,5), (11,6), (11,7), (12,4), (12,8),
   (13,3), (14,3), (13,9), (14,9), (15,6),
   (16,4), (16,8), (17,5), (17,7), (17,6), (18,6),
   (21,3), (21,4), (21,5), (22,3), (22,4), (22,5),
   (23,2), (23,6), (25,2), (25,1), (25,6), (25,7),
   (35,3), (36,3), (35,4), (36,4)]

interface Set (s: Type -> Type) where
  fromList' : (Hash a, Ord a) => List a -> s a
  member' : (Hash a, Ord a) => a -> s a -> Bool

Set HashSet where
  fromList' = fromList
  member' = member

Set SortedSet where
  fromList' = fromList
  member' = contains

interface Gen a where
  rand' : Eff a [RND]

Gen Cell where
  rand' = do
    x <- rndInt 1 100
    y <- rndInt 1 100
    pure (fromInteger x, fromInteger y)

time : (Ord a, Hash a, Gen a, Set s) => String -> List a -> Eff (s a, List (a, Bool), PMetrics) [PERF, RND]
time label xs = do
  collectPMetricsOnly
  mkTimer label
  startTimer label
  let set = fromList' xs
  cases <- loop set 1000000 []
  stopTimer label
  pure (set, cases, !getPerfMetrics)
 where
  loop : (Ord a, Hash a, Gen a, Set s) => s a -> Nat -> List (a, Bool) -> Eff (List (a, Bool)) [RND]
  loop _ Z acc = pure acc
  loop set (S k) acc = do
    e <- rand'
    loop set k ((e, member' e set) :: acc)

main : IO ()
main = do
  (s, cases, ms) <- run (time {s = HashSet} "HashSet" gosperGun)
  putStrLn (displayPerfMetrics ms)
  (s, cases, ms) <- run (time {s = SortedSet} "SortedSet" gosperGun)
  putStrLn (displayPerfMetrics ms)
