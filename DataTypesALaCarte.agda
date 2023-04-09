module DataTypesALaCarte where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Category.Functor using (RawFunctor)

data _:+:_ : (f g : Set → Set) → (e : Set) → Set where
  Inl : ∀ {f g e}
    → f e
    → (f :+: g) e
  Inr : ∀ {f g e}
    → g e
    → (f :+: g) e

-- Given two Functor type constructors, the coproduct is also a functor
:+:-<$> : ∀ {A B f g} → {{RawFunctor f}} → {{RawFunctor g}} → (A → B) → (f :+: g) A → (f :+: g) B
:+:-<$> {{Funcf}} {{Funcg}} m (Inl fa) = Inl (RawFunctor._<$>_ Funcf m fa)
:+:-<$> {{Funcf}} {{Funcg}} m (Inr ga) = Inr (RawFunctor._<$>_ Funcg m ga)

instance
  functor-:+: : ∀ {f g} → {{RawFunctor f}} → {{RawFunctor g}} → RawFunctor (f :+: g)
  functor-:+: = record { _<$>_ = :+:-<$> }

data _:<:_ : (f g : Set → Set) → {{RawFunctor f}} → {{RawFunctor g}} → Set₁ where
  Id : (f : Set → Set) → {{Funcf : RawFunctor f}} → f :<: f
  Inl : {f g h : Set → Set}
    → {{Funcf : RawFunctor f}}
    → {{Funcg : RawFunctor g}}
    → {{Funch : RawFunctor h}}
    → {{Func:+: : RawFunctor (g :+: h)}}
    → f :<: g
    → _:<:_ f (g :+: h) {{Funcf}} {{Func:+:}} 
  Inr : {f g h : Set → Set}
    → {{Funcf : RawFunctor f}}
    → {{Funcg : RawFunctor g}}
    → {{Funch : RawFunctor h}}
    → {{Func:+: : RawFunctor (g :+: h)}}
    → f :<: h
    → _:<:_ f (g :+: h) {{Funcf}} {{Func:+:}} 

instance
  :<:-functor : ∀ {f} → {{Funcf : RawFunctor f}} → f :<: f
  :<:-functor {f} = Id f

  :<:-:+:ˡ : ∀ {f g h} 
    → {{Funcf : RawFunctor f}} 
    → {{Funcg : RawFunctor g}} 
    → {{Funch : RawFunctor h}} 
    → {{Func:+: : RawFunctor (f :+: g)}}
    → {{f :<: g}}
    → f :<: (g :+: h)
  :<:-:+:ˡ {{_}} {{_}} {{_}} {{_}} {{f:<:g}} = Inl f:<:g

  :<:-:+:ʳ : ∀ {f g h} 
    → {{Funcf : RawFunctor f}} 
    → {{Funcg : RawFunctor g}} 
    → {{Funch : RawFunctor h}} 
    → {{Func:+: : RawFunctor (f :+: g)}}
    → {{f :<: h}}
    → f :<: (g :+: h)
  :<:-:+:ʳ {{_}} {{_}} {{_}} {{_}} {{f:<:h}} = Inr f:<:h

inj : ∀ {a} {f g : Set → Set} → {{Funcf : RawFunctor f}} {{Funcg : RawFunctor g}}
  → f :<: g 
  → f a 
  → g a
inj (Id _) x = x
inj (Inl f:<:g) fa = Inl (inj f:<:g fa)
inj (Inr f:<:h) fa = Inr (inj f:<:h fa)
