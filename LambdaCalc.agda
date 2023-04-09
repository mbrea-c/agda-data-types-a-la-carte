{-# OPTIONS --no-positivity-check --overlapping-instances #-}

module LambdaCalc where

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
open import DataTypesALaCarte

data Type : (Set → Set) → Set where
  In : ∀ {f : Set → Set}
    → f (Type f)
    → Type f

data Fun : Set → Set where
  _⇒_ : ∀ {E : Set} 
    → E → E → Fun E

data Nat : Set → Set where
  `ℕ : ∀ {E : Set} 
    → Nat E

BasicType = Fun :+: Nat

instance
  functor-fun : RawFunctor Fun
  functor-fun = record {
      _<$>_ = λ { m (A ⇒ B) → (m A) ⇒ (m B) } 
    }
  functor-nat : RawFunctor Nat
  functor-nat = record {
      _<$>_ = λ { m (`ℕ) → `ℕ } 
    }

inject-type : ∀ {f g} 
  → {{Funcf : RawFunctor f}} 
  → {{Funcg : RawFunctor g}} 
  → {{g :<: f}}
  → g (Type f) 
  → Type f
inject-type {{_}} {{_}} {{g:<:f}} ga = In (inj g:<:f ga)

nat : ∀ {f} → {{Funcf : RawFunctor f}} → {{Nat :<: f}} → Type f
nat = inject-type `ℕ

fun : ∀ {f} → {{Funcf : RawFunctor f}} → {{Fun :<: f}} → Type f → Type f → Type f
fun A B = inject-type (A ⇒ B)

data Context : (Set → Set) → Set where
  ∅   : ∀ {f} → Context f
  _,_ : ∀ {f} → Context f → Type f → Context f

data _∋_ : {f : Set → Set} → Context f → Type f → Set where
  Z : ∀ {f} {Γ : Context f} {A : Type f}
      ---------
    → _∋_ {f} (Γ , A) A

  S_ : ∀ {f} {Γ : Context f} {A B : Type f}
    → _∋_ {f} Γ A
      ---------
    → _∋_ {f} (Γ , B) A

data TypeJudgement : {Tp : Set → Set} → (Set₁ → Set₁) → Context Tp → Type Tp → Set₁ where
  In : ∀ {Tp} {Γ : Context Tp} {A : Type Tp} {f : Set₁ → Set₁}
    → f (TypeJudgement f)
    → TypeJudgement f Γ A

data Variable : Set₁ → Set₁ where
  `_ : ∀ {E : Set₁} {Tp : Set → Set} {Γ : Context Tp} {A : Type Tp}
    → Γ ∋ A
    → Variable E

-- data Lambda : {} Set₁ → Set₁ where
--   `_ : ∀ {E : Set₁} {Tp : Set → Set} {Γ : Context Tp} {A B : Type Tp}
--     → E (Γ , A) B
--     → Variable E
