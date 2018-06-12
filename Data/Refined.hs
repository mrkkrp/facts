{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.Refined
  (
  )
where

import Data.Coerce
import Data.Either (fromRight)
import Data.Kind
import Data.Proxy
import GHC.Generics
import GHC.TypeLits

----------------------------------------------------------------------------
-- Set on type level

type family PropName (p :: *) :: Symbol where
  PropName p = PropName' (Rep p)

type family PropName' (p :: * -> *) :: Symbol where
  PropName' (D1 ('MetaData n m p nt) V1) =
    p `AppendSymbol` "-" `AppendSymbol` m `AppendSymbol` "-" `AppendSymbol` n

type family AddProp (as :: [*]) (a :: *) :: [*] where
  AddProp '[] a = '[a]
  AddProp (b ': as) a = AddPropC (CmpSymbol (PropName a) (PropName b)) a b as

type family AddPropC (o :: Ordering) (a :: *) (b :: *) (as :: [*]) :: [*] where
  AddPropC 'LT a b as = a ': b ': as
  AddPropC 'EQ a b as = a ': as
  AddPropC 'GT a b as = b ': AddProp as a

type family HasProp (ps :: [*]) (a :: *) :: Constraint where
  HasProp '[] a = TypeError
    ('ShowType a ':<>: 'Text " is not a proven property")
  HasProp (a ': as) a = ()
  HasProp (b ': as) a = HasProp as a

type family AddProps (ps :: [*]) (as :: [*]) :: [*] where
  AddProps ps '[] = ps
  AddProps ps (a ': as) = AddProps (AddProp ps a) as

type family HasProps (ps :: [*]) (as :: [*]) :: Constraint where
  HasProps ps '[] = ()
  HasProps ps (a ': as) = (HasProp ps a, HasProps ps as)

type family RemProp (ps :: [*]) (p :: *) :: [*] where
  RemProp '[] p = '[]
  RemProp (p ': as) p = as
  RemProp (a ': as) p = a ': RemProp as p

----------------------------------------------------------------------------
-- Properties

class Prop a p where

  type PropProjection p :: *

  checkProp :: Proxy p -> a -> Either String (PropProjection p)

  -- TODO for efficiency it may make sense to add a special method that only
  -- does checking but not conversion

----------------------------------------------------------------------------
-- Refined data and its construction

newtype Refined (ps :: [*]) a = Refined a

refined :: a -> Refined '[] a
refined = Refined

data RefinedException = RefinedException

----------------------------------------------------------------------------
-- Assuming facts

-- TODO unsafe stuff, should fail immediately and show stack traces

----------------------------------------------------------------------------
-- Proving facts

-- TODO try to add stack traces

-- TODO via MonadThrow and MonadFail, and with Either

----------------------------------------------------------------------------
-- Deducing facts

class Axiom (name :: Symbol) (qs :: [*]) (p :: *) | name -> qs p where

applyAxiom :: forall name p qs ps a. (Axiom name qs p, ps `HasProps` qs)
  => Refined ps a
  -> Refined (ps `AddProp` p) a
applyAxiom = coerce

selectProps :: forall qs ps a. (ps `HasProps` qs)
  => Refined ps a
  -> Refined qs a
selectProps = coerce

forgetProp :: forall p ps a. (ps `HasProp` p)
  => Refined ps a
  -> Refined (ps `RemProp` p) a
forgetProp = coerce

----------------------------------------------------------------------------
-- Projections

projectRefined :: forall p ps a. (Prop a p, ps `HasProp` p)
  => Refined ps a
  -> PropProjection p
projectRefined (Refined a) =
  fromRight (error "a property has been falsified")
            (checkProp (Proxy :: Proxy p) a)

----------------------------------------------------------------------------
-- Other TODO

-- TH helpers for compile-time validation

----------------------------------------------------------------------------
-- Playground

data FooProp deriving (Generic)
data GooProp deriving (Generic)
data EeeProp deriving (Generic)

instance Prop Int FooProp where
  type PropProjection FooProp = Int
  checkProp Proxy i = Right 10

r :: Refined '[FooProp] Int
r = coerce (5 :: Int)

instance Axiom "bob" '[FooProp] GooProp

-- TODO Error messages absolutely suck

rrr :: Refined '[FooProp, GooProp] Int
rrr = applyAxiom @"bob" r

-- projected :: Int
-- projected = projectRefined @FooProp rrr
