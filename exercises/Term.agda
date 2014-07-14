
module Term where

open import Prelude
open import Lists
open import Type public

Name = String

module Unchecked where

  data Term : Set where
    var : Name → Term
    lit : Nat → Term
    suc : Term
    app : Term → Term → Term
    lam : Name → Type → Term → Term

module WellTyped where

  Cxt = List (Name × Type)

  data Term : Cxt → Type → Set where
    var : ∀ {Γ a} (x : Name) (i : (x , a) ∈ Γ) → Term Γ a
    app : ∀ {Γ a b} (u : Term Γ (a => b)) (v : Term Γ a) →
            Term Γ b
    lam : ∀ {Γ} x a {b} (v : Term ((x , a) ∷ Γ) b) → Term Γ (a => b)
    lit : ∀ {Γ} (n : Nat) → Term Γ nat
    suc : ∀ {Γ} → Term Γ (nat => nat)

  open Unchecked renaming (Term to Expr)

  -- Exercise: Define the erasure from well-typed to unchecked terms.
  forgetTypes : ∀ {Γ a} → Term Γ a → Expr
  forgetTypes (var x i) = var x
  forgetTypes (app e e₁) = app (forgetTypes e) (forgetTypes e₁)
  forgetTypes (lam x a e) = lam x a (forgetTypes e)
  forgetTypes (lit n) = lit n
  forgetTypes suc = suc


module WellScoped where

  Cxt = List Name

  data Term (Γ : Cxt) : Set where
    var : (x : Name) (i : x ∈ Γ) → Term Γ
    app : (u : Term Γ) (v : Term Γ) → Term Γ
    lam : (x : Name) → (a : Type) → (v : Term (x ∷ Γ)) → Term Γ
    lit : (n : Nat) → Term Γ
    suc : Term Γ

  open Unchecked renaming (Term to Expr)

  -- Exercise: Define the erasure from well-typed to unchecked terms.
  forgetScope : ∀ {Γ} → Term Γ → Expr
  forgetScope (var x i) = var x
  forgetScope (app e e₁) = app (forgetScope e) (forgetScope e₁)
  forgetScope (lam x a e) = lam x a (forgetScope e)
  forgetScope (lit n) = lit n
  forgetScope suc = suc
