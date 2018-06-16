-- |
-- Module      :  Data.Refined
-- Copyright   :  © 2018 Mark Karpov
-- License     :  BSD 3 clause
--
-- Maintainer  :  Mark Karpov <markkarpov92@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
--
-- The module introduces a framework that allows us to manipulate refined
-- types. The documentation is meant to be read as an article from top to
-- bottom, as it serves as a manual and gradually introduces various
-- features of the library.

{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE RoleAnnotations        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.Refined
  ( -- * 'Refined' types
    Refined
  , refined
  , unrefined
    -- * 'Prop'erties
  , Prop (..)
  , IdProp
  , PropName
  , AddProp
  , HasProp
  , HasProps
  , ProjectionProps
    -- * Establishing properties
  , assumeProp
  , estPropThrow
  , estPropFail
  , estPropError
  , estPropTH
  , RefinedException (..)
    -- * Following properties
  , Via
  , followProp
    -- * Deducing properties
  , Axiom
  , V
  , applyAxiom
  , selectProps )
where

import Control.Monad.Catch (Exception (..), MonadThrow (..))
import Control.Monad.Except (MonadError (..))
import Data.Coerce
import Data.Kind
import Data.Proxy
import Data.Typeable (Typeable)
import GHC.Generics
import GHC.Stack
import GHC.TypeLits
import qualified Control.Monad.Fail         as Fail
import qualified Language.Haskell.TH.Syntax as TH

----------------------------------------------------------------------------
-- Refined types

-- | @'Refined' ps a@ is a wrapper around @a@ proving that it has properties
-- @ps@. @ps@ is a type-level list containing /properties/, that is, void
-- data types symbolizing various concepts, see 'Prop'.

newtype Refined (ps :: [*]) a = Refined a
  deriving (Eq, Ord, Show, Typeable)

type role Refined phantom representational

instance TH.Lift a => TH.Lift (Refined ps a) where
  lift (Refined a) = [| Refined a |]

-- | 'refined' creates a refined type with no associated properties. We
-- don't demand anything, and so quite conveniently this is a pure function.

refined :: a -> Refined '[] a
refined = Refined

-- | We can erase information we know by using 'unrefined'.

unrefined :: Refined ps a -> a
unrefined (Refined a) = a

----------------------------------------------------------------------------
-- Properties

-- | @'Prop' a p@ is a type class for @a@ things that can have @p@ property.
-- Properties are morphisms in the category of refined types.

class (Show a, Generic p) => Prop a p where

  -- | If we consider property @p@ as a morphism, then while @a@ is its
  -- domain, @'PropProjection' a p@ is the codomain.
  --
  -- We could have a property telling that a @Text@ value is not empty,
  -- then:
  --
  -- > type PropProjection Text NotEmpty = NonEmptyText -- e.g. a newtype
  --
  -- We could do the same for linked lists:
  --
  -- > type PropProjection [Char] NotEmpty = NonEmpty Char
  --
  -- This connects the 'Data.List.NonEmpty.NonEmpty' type, normally
  -- obtainable via the smart constructor 'Data.List.NonEmpty.nonEmpty' to
  -- our list. Once we have proven that our list is @NotEmpty@, we'll be
  -- able to get @NonEmpty@ projection purely without possibility of
  -- failure.
  --
  -- We could have a property called @Length@ and in that case we could say:
  --
  -- > type PropProjection Text Length = Int
  --
  -- We could also have a property @IsURI@ telling if a @Text@ value is a
  -- valid @URI@. In that case we could say (assuming that @URI@ is such a
  -- type that can represent only valid URIs):
  --
  -- > type PropProjection Text IsURI = URI

  type PropProjection a p :: *

  -- | 'checkProp' is the way to check if @a@ has property @p@. It either
  -- has it, and then we obtain @'PropProjection' a p@ or it doesn't have
  -- such a property, in which case a reason “why” is returned as a
  -- 'String'.

  checkProp :: Proxy p -> a -> Either String (PropProjection a p)

-- | Identity property. This is the identity in the category of refined
-- types.

data IdProp deriving Generic

-- | Every type has the identity property which allows to treat that type as
-- well… that type.

instance Show a => Prop a IdProp where
  type PropProjection a IdProp = a
  checkProp Proxy = Right

-- | We always can assume that a value has 'IdProp'.

instance Axiom "id_prop" '[] '[] IdProp

-- | An existing property can be pre-composed with 'IdProp'.

instance Axiom "id_prop_pre" '[a] '[a] (a `Via` IdProp)

-- | Pre-composition of 'IdProp' can be dropped.

instance Axiom "id_prop_pre'" '[a] '[a `Via` IdProp] a

-- | An existing prperty can be post-composed with 'IdProp'.

instance Axiom "id_prop_post" '[a] '[a] (IdProp `Via` a)

-- | Post-composition of 'IdProp' can be dropped.

instance Axiom "id_prop_post'" '[a] '[IdProp `Via` a] a

-- | Obtain a name of property type as a type of the kind 'Symbol'.

type family PropName (p :: *) :: Symbol where
  PropName (a `Via` b) = "*"
    `AppendSymbol` PropName' (Rep a)
    `AppendSymbol` "*via*"
    `AppendSymbol` PropName' (Rep b)
  PropName p = PropName' (Rep p)

-- | A helper for 'PropName'.

type family PropName' (p :: * -> *) :: Symbol where
  PropName' (D1 ('MetaData n m p nt) V1) =
    p `AppendSymbol` "-" `AppendSymbol` m `AppendSymbol` "-" `AppendSymbol` n
  PropName' p = TypeError
    ('Text "Types that represent properties should not have data constructors")

-- | Add a property @p@ to the type-level set @ps@. If a property is already
-- in the set, nothing will happen. The order of items in the set is
-- (mostly) deterministic.

type family AddProp (ps :: [*]) (p :: *) :: [*] where
  AddProp '[] p = '[p]
  AddProp (n ': ps) p = AddPropC (CmpSymbol (PropName p) (PropName n)) p n ps

type family AddPropC (o :: Ordering) (a :: *) (b :: *) (as :: [*]) :: [*] where
  AddPropC 'LT a b as = a ': b ': as
  AddPropC 'EQ a a as = a ': as
  AddPropC 'EQ a b as = a ': b ': as
  AddPropC 'GT a b as = b ': AddProp as a

-- | The resulting constraint will be satisfied iff the collection of
-- properties @ps@ has the property @p@ is it.

type family HasProp (ps :: [*]) (p :: *) :: Constraint where
  HasProp '[] p = TypeError
    ('ShowType p ':<>: 'Text " is not a proven property")
  HasProp (p ': ps) p = ()
  HasProp (b ': ps) p = HasProp ps p

-- | Like 'HasProp' but for many properties at once.

type family HasProps (ps :: [*]) (qs :: [*]) :: Constraint where
  HasProps ps '[] = ()
  HasProps ps (q ': qs) = (HasProp ps q, HasProps ps qs)

-- | Construct a list of properties from @ps@ for projection obtained via
-- @p@.

type family ProjectionProps (ps :: [*]) (p :: *)  :: [*] where
  ProjectionProps ps (t `Via` p) = ProjectionProps (ProjectionProps ps p) t
  ProjectionProps '[] p = '[]
  ProjectionProps ((t `Via` p) ': ps) p = t ': ProjectionProps ps p
  ProjectionProps (x ': ps) p = ProjectionProps ps p

----------------------------------------------------------------------------
-- Establishing properties

-- | Assume a property. This is unsafe and may be a source of bugs. Only use
-- when you 100% sure that the property indeed holds.

assumeProp
  :: forall q ps a. (Prop a q)
  => Refined ps a
  -> Refined (ps `AddProp` q) a
assumeProp = coerce

-- | Establish a property in 'MonadThrow'.

estPropThrow
  :: forall q ps m a. ( Prop a q
                      , KnownSymbol (PropName q)
                      , MonadThrow m
                      )
  => Refined ps a
  -> m (Refined (ps `AddProp` q) a)
estPropThrow = either throwM return . probeProp @q

-- | Establish a property in a 'Fail.MonadFail' instance.

estPropFail
  :: forall q ps m a. ( Prop a q
                      , KnownSymbol (PropName q)
                      , Fail.MonadFail m
                      )
  => Refined ps a
  -> m (Refined (ps `AddProp` q) a)
estPropFail = either (Fail.fail . displayException) return . probeProp @q

-- | Establish a property in a 'MonadError' instance.

estPropError
  :: forall q ps m a. ( Prop a q
                      , KnownSymbol (PropName q)
                      , MonadError RefinedException m
                      )
  => Refined ps a
  -> m (Refined (ps `AddProp` q) a)
estPropError = either throwError return . probeProp @q

-- | Establish a property at copmile time using Template Haskell.

estPropTH
  :: forall q ps a. ( Prop a q
                    , KnownSymbol (PropName q)
                    , TH.Lift a
                    )
  => Refined ps a
  -> TH.Q TH.Exp
estPropTH x = estPropFail @q x >>= TH.lift

-- | Check if a property holds and return error message if it doesn't.

probeProp
  :: forall q ps a. (Prop a q, KnownSymbol (PropName q))
  => Refined ps a
  -> Either RefinedException (Refined (ps `AddProp` q) a)
probeProp (Refined a) =
  case checkProp (Proxy :: Proxy q) a of
    Left issue -> Left RefinedException
      { rexpCallStack = callStack
      , rexpValue = show a
      , rexpPropName = symbolVal (Proxy :: Proxy (PropName q))
      , rexpIssue = issue
      }
    Right _ -> Right (Refined a)

-- | Exception that is thrown at run time when a property doesn't hold.

data RefinedException = RefinedException
  { rexpCallStack :: !CallStack
    -- ^ Location where the check failed
  , rexpValue :: !String
    -- ^ Value that failed to satisfy a property check
  , rexpPropName :: !String
    -- ^ Name of the property in question
  , rexpIssue :: !String
    -- ^ Description of why the property check failed
  } deriving (Show, Typeable)

instance Exception RefinedException where
  displayException RefinedException {..} = unlines
    [ "RefinedException:"
    , prettyCallStack rexpCallStack
    , "value: " ++ rexpValue
    , "property: " ++ rexpPropName
    , "issue:" ++ rexpIssue
    ]

----------------------------------------------------------------------------
-- Following properties

-- | 'Via' is the composition in the category of refined types.
--
-- 'Via' is of great utility as it allows to prove properties about values
-- of refined types that are obtainable by following a proprety morphism,
-- not values we currently have. It also allows to state 'Axiom's (see
-- below) that talk about properties of “connected” types. Without 'Via',
-- 'Axiom's could only talk about relations between properties of the same
-- type type.

data (t :: *) `Via` (p :: *) deriving Generic

instance (Prop (PropProjection a p) t, Prop a p) => Prop a (t `Via` p) where

  type PropProjection a (t `Via` p) = PropProjection (PropProjection a p) t

  checkProp Proxy a =
    checkProp (Proxy :: Proxy p) a >>=
    checkProp (Proxy :: Proxy t)

infixl 5 `Via`

-- | Obtain a projection as a refined value, i.e. follow a morphism created
-- by a property.

followProp :: forall p ps a. (Prop a p, ps `HasProp` p, HasCallStack)
  => Refined ps a
  -> Refined (ProjectionProps ps p) (PropProjection a p)
followProp (Refined a) =
  case checkProp (Proxy :: Proxy p) a of
    Left msg -> error $
      prettyCallStack callStack ++ "\n" ++
      show a ++ ": " ++ msg
    Right x -> Refined x

----------------------------------------------------------------------------
-- Deducing properties

-- | A helper wrapper to help us construct heterogeneous type-level lists
-- with respect to kinds of elements.

data V (a :: k)

-- | An @'Axiom' name vs qs p@ allows to prove property @p@ if properties
-- @qs@ are already proven. @name@ and arguments @vs@ determine both @qs@
-- and @p@.
--
-- The arguments are necessary sometimes. Imagine you want to write
-- something as trivial as:
--
-- > instance CmpNat n m ~ GT => Axiom "weaken_gt"
-- >     '[V n, V m] '[GreaterThan n] (GreaterThan m)
--
-- Without having @vs@ you'd have a hard time convincing GHC that this could
-- work.
--
-- Another example. Suppose I have two refined types @A@ and @B@ and
-- properties @PropM@ and @PropN@ such that @PropM@ allows me to go from @A@
-- to @B@ and @PropN@ allows me to go back to get exactly the same value of
-- @A@ as before. Now it makes sense that I could arrange things is such a
-- way that when I'm “back” I can recover any properties that I originally
-- knew about @A@.
--
-- > instance Axiom "preserve" '[p] '[p] (p `Via` PropN `Via` PropM)
--
-- Now I can first create as many properties as necessary of the form @p
-- `Via` PropN `Via` PropM@, then use @PropM@ to go to @B@ with help of
-- 'followProp'. After that I'll be able to go back to @A@ and my old
-- properties “preserved” in that way will be with me.
--
-- Again, without the argument parameter @vs@ that trick would be
-- impossible.

class Axiom (name :: Symbol) (vs :: [*]) (qs :: [*]) (p :: *) | name vs -> qs p

-- | Apply 'Axiom' and deduce a new property.

applyAxiom
  :: forall name vs p qs ps a. (Prop a p, Axiom name vs qs p, ps `HasProps` qs)
  => Refined ps a
  -> Refined (ps `AddProp` p) a
applyAxiom = coerce

-- | Select some properties from known properties.

selectProps :: forall qs ps a. (ps `HasProps` qs)
  => Refined ps a
  -> Refined qs a
selectProps = coerce
