-- An instruction set and compiler for the SECD machine.
-- Adapted from Ager et al. 2003 (From Interpreter to
-- Compiler and Virtual Machine: a Functional Derivation).
module SECD.Compiled where

open import Prelude
open import Lists

open import Term
open import Term.Show
open Term.WellTyped

-- Cxt → StackType → StackType

StackType : Set
StackType = List Type

Control : Cxt → StackType → StackType → Set

data Instr (Γ : Cxt) : StackType → StackType → Set where
  access : ∀ {Δ x a} → (x , a) ∈ Γ → Instr Γ Δ (a ∷ Δ)
  close  : ∀ {Δ b} (x : Name) → (a : Type) → Control ((x , a) ∷ Γ) [] (b ∷ []) → Instr Γ Δ ((a => b) ∷ Δ)
  call   : ∀ {Δ a b} → Instr Γ ((a => b) ∷ a ∷ Δ) (b ∷ Δ)
  lit    : ∀ {Δ} → Nat → Instr Γ Δ (nat ∷ Δ)
  suc    : ∀ {Δ} → Instr Γ Δ ((nat => nat) ∷ Δ)

Control Γ = Path (Instr Γ)

compile′ : ∀ {Γ Δ a b} → Term Γ a → Control Γ (a ∷ Δ) (b ∷ []) → Control Γ Δ (b ∷ [])
compile′ (var x i)   c = access i ∷ c
compile′ (app u v)   c = compile′ v $ compile′ u $ call ∷ c
compile′ (lam x a v) c = close x a (compile′ v []) ∷ c
compile′ (lit n)     c = lit n ∷ c
compile′ suc         c = suc ∷ c

compile : ∀ {Γ a} → Term Γ a → Control Γ [] (a ∷ [])
compile v = compile′ v []

-- Exercise:
--   Make the instruction set above type safe and modify (a copy of) the
--   TypeSafe SECD machine to use this representation of the control
--   component.
