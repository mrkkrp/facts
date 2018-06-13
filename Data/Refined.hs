-- |
-- Module      :  Data.Refined
-- Copyright   :  © 2018 Mark Karpov
-- License     :  BSD 3 clause
--
-- Maintainer  :  Mark Karpov <markkarpov92@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
-- The module introduces a framework that allow us to manipulate refined
-- types.

{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.Refined
  ( -- * 'Refined' types
    Refined
  , refined
  , unrefined
    -- * Properties
  , Prop (..)
  , AddProp
  , AddProps
  , HasProp
  , HasProps
    -- * Projections
  , projectRefined
    -- * Establishing properties
  , assumeProps
  , estPropsThrow
  , estPropsFail
  , estPropsError
  , estPropsTH
  , RefinedException (..)
    -- * Deducing properties
  , Axiom
  , V
  , applyAxiom
  , selectProps )
where

import Control.Monad.Catch (MonadThrow (..))
import Control.Monad.Except (MonadError (..))
import Control.Monad.Fail (MonadFail (..))
import Data.Coerce
import Data.Either (fromRight)
import Data.Kind
import Data.Proxy
import GHC.Generics
import GHC.Stack
import GHC.TypeLits
import Language.Haskell.TH

----------------------------------------------------------------------------
-- Refined types

newtype Refined (ps :: [*]) a = Refined a

refined :: a -> Refined '[] a
refined = Refined

unrefined :: Refined ps a -> a
unrefined (Refined a) = a

----------------------------------------------------------------------------
-- Properties

class (Show a, Generic p) => Prop a p where

  type PropProjection a p :: *

  checkProp :: Proxy p -> a -> Either String (PropProjection a p)

type family PropName (p :: *) :: Symbol where
  PropName p = PropName' (Rep p)

type family PropName' (p :: * -> *) :: Symbol where
  PropName' (D1 ('MetaData n m p nt) V1) =
    p `AppendSymbol` "-" `AppendSymbol` m `AppendSymbol` "-" `AppendSymbol` n
  PropName' p = TypeError
    ('Text "Types that represent properties should not have data constructors")

type family AddProp (as :: [*]) (a :: *) :: [*] where
  AddProp '[] a = '[a]
  AddProp (b ': as) a = AddPropC (CmpSymbol (PropName a) (PropName b)) a b as

type family AddPropC (o :: Ordering) (a :: *) (b :: *) (as :: [*]) :: [*] where
  AddPropC 'LT a b as = a ': b ': as
  AddPropC 'EQ a a as = a ': as
  AddPropC 'EQ a b as = a ': b ': as
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

type family All (c :: k -> Constraint) (xs :: [k]) :: Constraint where
  All c '[] = ()
  All c (x ': xs) = (c x, All c xs)

----------------------------------------------------------------------------
-- Projections

projectRefined :: forall p ps a. (Prop a p, ps `HasProp` p)
  => Refined ps a
  -> PropProjection a p
projectRefined (Refined a) =
  fromRight (error "a property has been falsified")
            (checkProp (Proxy :: Proxy p) a)

----------------------------------------------------------------------------
-- Establishing properties

assumeProps
  :: forall qs ps a. (All (Prop a) qs)
  => Refined ps a
  -> Refined (ps `AddProps` qs) a
assumeProps = undefined

estPropsThrow
  :: forall qs ps m a. (All (Prop a) qs, MonadThrow m)
  => Refined ps a
  -> m (Refined (ps `AddProps` qs) a)
estPropsThrow = undefined

estPropsFail
  :: forall qs ps m a. (All (Prop a) qs, MonadFail m)
  => Refined ps a
  -> m (Refined (ps `AddProps` qs) a)
estPropsFail = undefined

estPropsError
  :: forall qs ps m a. (All (Prop a) qs, MonadError RefinedException m)
  => Refined ps a
  -> m (Refined (ps `AddProps` qs) a)
estPropsError = undefined

estPropsTH :: Q Exp
estPropsTH = undefined

-- TODO try to add stack traces

-- TODO via MonadThrow and MonadFail, and with Either

data RefinedException = RefinedException
  -- call stack
  -- collection of error messages as Strings
  -- property that is violated (via generics again)
  -- input that is problematic (Show'ed)
  -- type of logical failure: wrong assumption, unsatisfied condition,
  -- failure to obtain a projection (bad!)

----------------------------------------------------------------------------
-- Deducing properties

data V (a :: k)

class Axiom (name :: Symbol) (vs :: [*]) (qs :: [*]) (p :: *) | name vs -> qs p

applyAxiom
  :: forall name vs p qs ps a. (Prop a p, Axiom name vs qs p, ps `HasProps` qs)
  => Refined ps a
  -> Refined (ps `AddProp` p) a
applyAxiom = coerce

selectProps :: forall qs ps a. (ps `HasProps` qs)
  => Refined ps a
  -> Refined qs a
selectProps = coerce

----------------------------------------------------------------------------
-- Playground

data FooProp deriving (Generic)
data GooProp deriving (Generic)
data EeeProp deriving (Generic)

instance Prop Int FooProp where
  type PropProjection Int FooProp = Int
  checkProp Proxy i = Right 10

instance Prop Int GooProp where
  type PropProjection Int GooProp = Int
  checkProp Proxy i = Right 20

data GreaterThan (n :: Nat) deriving (Generic)

instance KnownNat n => Prop Int (GreaterThan n) where
  type PropProjection Int (GreaterThan n) = Int
  checkProp Proxy i =
    if i > fromIntegral (natVal (Proxy :: Proxy n))
      then Right i
      else Left "Not your day"

instance CmpNat n m ~ GT => Axiom "weaken_gt" '[V n, V m] '[GreaterThan n] (GreaterThan m)

r :: Refined '[GreaterThan 5] Int
r = assumeProps @'[GreaterThan 5] (refined 10)

rrr :: Refined '[GreaterThan 3, GreaterThan 5] Int
rrr = applyAxiom @"weaken_gt" @'[V 5, V 3] r
