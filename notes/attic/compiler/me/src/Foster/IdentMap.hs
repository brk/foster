module Foster.IdentMap where

import Data.IntMap.Strict as IntMap

import Data.Hashable

import Foster.Ident(Ident(..))

newtype IdentMap a = IDM (IntMap a)

identHash :: Ident -> Int
identHash (Ident _ u) = u
identHash (GlobalSymbol t _mr) = hash t

empty :: IdentMap a
empty = IDM (IntMap.empty)

findWithDefault :: a -> Ident -> IdentMap a -> a
findWithDefault def k (IDM m) = IntMap.findWithDefault def (identHash k) m

singleton :: Ident -> a -> IdentMap a
singleton k v = IDM (IntMap.singleton (identHash k) v)

delete :: Ident -> IdentMap a -> IdentMap a
delete k (IDM m) = IDM (IntMap.delete (identHash k) m)

insert :: Ident -> a -> IdentMap a -> IdentMap a
insert k v (IDM m) = IDM (IntMap.insert (identHash k) v m)

insertWith :: (a -> a -> a) -> Ident -> a -> IdentMap a -> IdentMap a
insertWith f k v (IDM m) = IDM (IntMap.insertWith f (identHash k) v m)

lookup :: Ident -> IdentMap a -> Maybe a
lookup k (IDM m) = IntMap.lookup (identHash k) m

--Can't recover original Idents for toList because they're not stored!
-- Would need HashMap for that.
--toList :: IdentMap a -> [(Ident, a)]
--toList (IDM m) = IntMap.toList m

fromList :: [(Ident, a)] -> IdentMap a
fromList pairs = IDM $ IntMap.fromList [(identHash k, v) | (k, v) <- pairs]

adjust :: (a -> a) -> Ident -> IdentMap a -> IdentMap a
adjust f k (IDM m) = IDM (IntMap.adjust f (identHash k) m)

