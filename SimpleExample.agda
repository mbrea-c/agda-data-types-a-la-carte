{-# OPTIONS --no-positivity-check --overlapping-instances #-}

module SimpleExample where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; _+_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Category.Functor using (RawFunctor)
open import DataTypesALaCarte

data Expr : (Set → Set) → Set where
  In : ∀ {f : Set → Set}
    → f (Expr f)
    → Expr f

data Add : Set → Set where
  add : ∀ {E : Set} 
    → E → E → Add E

data Nat : Set → Set where
  nat : ∀ {E : Set} 
    → ℕ
    → Nat E

instance
  functor-add : RawFunctor Add
  functor-add = record {
      _<$>_ = λ { m (add A B) → add (m A) (m B) } 
    }
  functor-nat : RawFunctor Nat
  functor-nat = record {
      _<$>_ = λ { m (nat a) → nat a } 
    }

inject-expr : ∀ {f g} 
  → {{Funcf : RawFunctor f}} 
  → {{Funcg : RawFunctor g}} 
  → {{g :<: f}}
  → g (Expr f) 
  → Expr f
inject-expr {{_}} {{_}} {{g:<:f}} ga = In (inj g:<:f ga)

infixl 6 _∔_
infix 7 !_

!_ : ∀ {f} → {{Funcf : RawFunctor f}} → {{Nat :<: f}} → ℕ → Expr f
!_ n = inject-expr (nat n)

_∔_ : ∀ {f} → {{Funcf : RawFunctor f}} → {{Add :<: f}} → Expr f → Expr f → Expr f
_∔_ A B = inject-expr (add A B)

-- Termination checking fails, can be fixed properly but for now disable
-- checking
foldExpr : ∀ {f a} → {{RawFunctor f}} → (f a → a) → Expr f → a
{-# TERMINATING #-}
foldExpr {{f}} m (In t) = m ((RawFunctor._<$>_ f) (foldExpr m) t)

record Eval (f : Set → Set) {{Fucnf : RawFunctor f}} : Set where
  field
    evalAlgebra : f ℕ → ℕ

instance
  eval-add : Eval Add
  eval-add = record {
      evalAlgebra = λ { (add a b) → a + b }
    }
  eval-nat : Eval Nat
  eval-nat = record {
      evalAlgebra = λ { (nat a) → a }   
    }
  eval-:+: : ∀ {f g} → {{Funcf : RawFunctor f}} → {{Funcg : RawFunctor g}} → {{Eval f}} → {{Eval g}} → Eval (f :+: g)
  eval-:+: {{_}} {{_}} {{evalf}} {{evalg}} = record {
      evalAlgebra = λ { 
          (Inl a) → Eval.evalAlgebra evalf a ;
          (Inr b) → Eval.evalAlgebra evalg b
        }
    }
eval : ∀ {f} → {{Funcf : RawFunctor f}} → {{Eval f}} → Expr f → ℕ
eval {{_}} {{evalf}} expr = foldExpr (Eval.evalAlgebra evalf) expr

addExample : Expr (Add :+: Nat)
addExample = (! 5 ∔ ! 6) ∔ ! 1

_ : eval addExample ≡ 12
_ = refl
