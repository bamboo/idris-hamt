module Data.HashSet

import Data.Hash

%default total

%access public export

{- Pretend array API -}
Array : Type -> Type
Array = List

Index : Type
Index = Nat

singleton : a -> Array a
singleton x = [x]

elementAt : Index -> Array a -> a
elementAt i xs =
  case (index' i xs) of
    Just x  => x
    Nothing => assert_unreachable

insertAt : Index -> Array a -> a -> Array a
insertAt i xs x =
  let (before, after) = splitAt i xs
  in before ++ x :: after

updateAt : Index -> Array a -> a -> Array a
updateAt i xs x =
  let (before, after) = splitAt i xs
  in before ++ x :: drop 1 after

HashCode : Type
HashCode = Bits64

Bitmap : Type
Bitmap = Bits64

Cast Bits64 Index where
  cast = cast . prim__zextB64_BigInt

mutual
  data Node a
    = Empty
    | Key HashCode a
    | HashCollision HashCode (List a)
    | SubTrie Bitmap (NodeList a)

  NodeList : Type -> Type
  NodeList a = List (Node a)

record HashSet a where
  constructor MkHashSet
  size : Nat
  root : NodeList a

Show a => Show (Node a) where
  show Empty = "E"
  show (Key h a) = "(K " ++ show a ++ ")"
  show (SubTrie bm l) = "(S " ++ show bm ++ " " ++ assert_total (show l) ++ ")"
  show _ = "*"

Show a => Show (HashSet a) where
  show (MkHashSet s r) = "HashSet " ++ show s ++ " " ++ show r

infixl 7 &
(&) : Bits64 -> Bits64 -> Bits64
(&) = prim__andB64

infixl 7 >>
(>>) : Bits64 -> Bits64 -> Bits64
(>>) = prim__lshrB64

infixl 7 <<
(<<) : Bits64 -> Bits64 -> Bits64
(<<) = prim__shlB64

(-) : Bits64 -> Bits64 -> Bits64
(-) x y = prim__truncBigInt_B64 (prim__zextB64_BigInt x - prim__zextB64_BigInt y)

shiftMask : Bits64 -> Bits64 -> Bits64 -> Bits64
shiftMask bits shift mask = (bits >> shift) & mask

next5Bits : Bits64 -> HashCode -> HashCode
next5Bits lvl hash = shiftMask hash (5 * lvl) 0x1F

bitAt : Bits64 -> Bits64 -> Bool
bitAt pos bits = 1 == shiftMask bits pos 1

popcnt : Bits64 -> Bits64
popcnt x =
  let x = x - shiftMask x 1 0x5555555555555555
      x = (x & 0x3333333333333333) + shiftMask x 2 0x3333333333333333
      x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0F
      x = x + (x >> 8)
      x = x + (x >> 16)
  in x & 0x000000000000003F

setBit : Bits64 -> Bits64 -> Bits64
setBit bitPos bits = prim__orB64 bits (1 << bitPos)

nodeIndex : Bits64 -> Bits64 -> Index
nodeIndex bitPos bitmap = cast (popcnt (bitmap & ((1 << bitPos) - 1)))

{-
3.1 Search for a key Map Hash Array Mapped Trie (HAMT)

Compute a full 64 bit hash for the key, take the most significant t bits and use 
them as an integer to index into the root hash table. One of three cases may be 
encountered:
 1) The entry is empty indicating that the key is not in the hash tree. 
 2) The entry is a Key/Value pair and the key either matches the desired key 
    indicating success or not, indicating failure. 
 3) The entry has a 32 bit map sub-hash table and a sub-trie pointer, Base, that 
    points to an ordered list of the non-empty sub-hash table entries.

Take the next 5 bits of the hash and use them as an integer to index into the bit Map. 
If this bit is a zero the hash table entry is empty indicating failure, 
otherwise, it’s a one, so count the one bits below it using CTPOP and use the result 
as the index into the non-empty entry list at Base. This process is repeated taking 
five more bits of the hash each time until a terminating key/value pair is found or 
the search fails. Typically, only a few iterations are required and it is important 
to note that the key is only compared once and that is with the terminating node key.
-}
member : (Hashable a, Eq a) => a -> HashSet a -> Bool
member key (MkHashSet _ root) =
  let rootPos = cast (next5Bits 0 hashCode)
  in memberOf root rootPos 1
  where
    hashCode : HashCode
    hashCode = hash key
    memberOf : NodeList a -> Index -> Bits64 -> Bool
    memberOf nodes index nextLevel =
      case elementAt index nodes of
        Empty => False
        Key existingHashCode existingKey =>
          existingHashCode == hashCode && existingKey == key
        HashCollision existingHashCode keys =>
          existingHashCode == hashCode && elem key keys
        SubTrie bitmap nodes =>
          let
            bitPos = next5Bits nextLevel hashCode
            bitVal = bitAt bitPos bitmap
          in
            if bitVal
              then assert_total (memberOf nodes (nodeIndex bitPos bitmap) (nextLevel + 1))
              else False

{-
3.2 Insertion
The initial steps required to add a new key to the hash tree are identical to the search. 
The search algorithm is followed until one of two failure modes is encountered.

Either an empty position is discovered in the hash table or a sub-hash table is found. 
In this case, if this is in the root hash table, the new key/value pair is simply substituted 
for the empty position. However, if in a sub-hash table then a new bit must be added to the 
bit map and the sub-hash table increased by one in size. A new sub-hash table must be 
allocated, the existing sub-table copied to it, the new key/value entry added in sub-hash 
sorted order and the old hash table made free.

Or the key will collide with an existing one. In which case the existing key must be 
replaced with a sub-hash table and the next 5 bit hash of the existing key computed. 
If there is still a collision then this process is repeated until no collision occurs. 
The existing key is then inserted in the new sub-hash table and the new key added. Each 
time 5 more bits of the hash are used the probability of a collision reduces by a factor 
of 1 . Occasionally an entire 64 bit hash may be consumed and 64 a new one must be computed 
to differentiate the two keys.
-}
insert : (Hashable a, Eq a) => a -> HashSet a -> HashSet a
insert key set@(MkHashSet size root) =
  case elementAt rootPos root of
    Empty => insertRootNode (Key hashCode key)
    node  => maybe set insertRootNode (insertInto node 0)
  where
    hashCode : HashCode
    hashCode = hash key
    rootPos : Index
    rootPos = cast (next5Bits 0 hashCode)
    insertRootNode : Node a -> HashSet a
    insertRootNode n = MkHashSet (S size) (updateAt rootPos root n)
    mutual
      insertIntoSubTrie : Bitmap -> NodeList a -> Bits64 -> Maybe (Node a)
      insertIntoSubTrie bitmap nodes level =
        let
          bitPos = next5Bits level hashCode
          bitVal = bitAt bitPos bitmap
          nodeIdx = nodeIndex bitPos bitmap
        in
          if bitVal
            then SubTrie bitmap . updateAt nodeIdx nodes <$> insertInto (elementAt nodeIdx nodes) level
            else Just (SubTrie (setBit bitPos bitmap) (insertAt nodeIdx nodes (Key hashCode key)))

      insertInto : Node a -> Bits64 -> Maybe (Node a)
      insertInto (SubTrie bitmap nodes) level =
        assert_total (insertIntoSubTrie bitmap nodes (level + 1))
      insertInto node@(Key existingHashCode existingKey) level =
        if existingHashCode == hashCode
          then
            if existingKey == key
              then Nothing
              else Just (HashCollision hashCode [key, existingKey])
          else
            assert_total (spawnSubTrie node existingHashCode (level + 1))
      insertInto node@(HashCollision existingHashCode keys) level =
        if existingHashCode == hashCode
          then
            if elem key keys
              then Nothing
              else Just (HashCollision hashCode (key :: keys))
          else
            assert_total (spawnSubTrie node existingHashCode (level + 1))
      insertInto Empty _ = assert_unreachable

      spawnSubTrie : Node a -> HashCode -> Bits64 -> Maybe (Node a)
      spawnSubTrie node existingHashCode level =
          let bitPos = next5Bits level existingHashCode
              bitmap = setBit bitPos 0
          in insertIntoSubTrie bitmap (singleton node) level

empty : (Hashable a, Eq a) => HashSet a
empty = MkHashSet 0 (replicate 64 Empty)

length : HashSet a -> Nat
length (MkHashSet size _) = size

fromList : (Eq a, Hashable a) => List a -> HashSet a
fromList = foldl (flip insert) empty

foldl : (acc -> elem -> acc) -> acc -> HashSet elem -> acc
foldl f init (MkHashSet _ nodes) = foldNodes init nodes
  where
   mutual
    foldNodes : acc -> NodeList elem -> acc
    foldNodes acc [] = acc
    foldNodes acc (x :: xs) = foldNodes (foldNode acc x) xs
    foldNode : acc -> Node elem -> acc
    foldNode acc Empty = acc
    foldNode acc (Key _ k) = f acc k
    foldNode acc (HashCollision _ keys) = foldl f acc keys
    foldNode acc (SubTrie _ nodes) = assert_total (foldNodes acc nodes)

-- TODO: optimize not to recompute hashcodes
filter : (Eq elem, Hashable elem) => (elem -> Bool) -> HashSet elem -> HashSet elem
filter f xs = foldl (\acc, e => if f e then (insert e acc) else acc) empty xs

into : (Eq a, Hashable a, Foldable f) => HashSet a -> f a -> HashSet a
into = foldl (flip insert)

elements : HashSet a -> List a
elements = foldl (flip (::)) []
