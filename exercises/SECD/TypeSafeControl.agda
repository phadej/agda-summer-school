-- An implementation of Landin's SECD machine. Adapted from
-- Danvy 2003 (A Rational Deconstruction of Landin's SECD Machine).
module SECD.TypeSafeControl where

open import Prelude

open import Term
open import Term.Show
open Term.WellTyped

open import Lists

open import SECD.Compiled

data Value : Type → Set

Env : Cxt → Set
Env Γ = All (Value ∘ snd) Γ

data Value where
  lit     : Nat → Value nat
  suc     : Value (nat => nat)
  closure : ∀ {Γ a b} → (x : Name) → Env Γ → Control ((x , a) ∷ Γ) [] (b ∷ []) → Value (a => b)

data Directive Γ : StackType → StackType → Set where
  term  : ∀ {Δ a} → Term Γ a → Directive Γ Δ (a ∷ Δ)
  apply : ∀ {Δ a b} → Directive Γ ((a => b) ∷ a ∷ Δ) (b ∷ Δ)

Stack : StackType → Set
Stack Δ = All Value Δ 

record Snapshot Θ a : Set where
  constructor snapshot
  field
    {Δ}         : StackType
    stack       : Stack Δ
    {Γ}         : Cxt
    environment : Env Γ
    control     : Control Γ (Θ ++ Δ) (a ∷ [])

Dump : Type → Type → Set
Dump = Path (λ a b → Snapshot (a ∷ []) b)

record SECD a : Set where
  constructor secd
  field
    {b}     : Type
    current : Snapshot [] b
    dump    : Dump b a

  open Snapshot current public

infix 1 _∣_∣_∣_
pattern _∣_∣_∣_ s e c d = secd (snapshot s e c) d

data StepResult a : Set where
  done  : Value a → StepResult a
  next  : SECD a → StepResult a
  error : String → StepResult a

step : ∀ {a} → SECD a → StepResult a
step (v ∷ [] ∣ _ ∣ [] ∣ []) = done v

step (v ∷ [] ∣ e′ ∣ [] ∣ (snapshot s e c) ∷ d) =
  next (v ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ access i ∷ c ∣ d) =
  case lookup∈ e i of (λ v → next (v ∷ s ∣ e  ∣ c ∣ d))

step (s ∣ e ∣ close x a c′ ∷ c ∣ d) =
  next (closure x e c′ ∷ s ∣ e ∣ c ∣ d)

step (suc ∷ lit n ∷ s ∣ e ∣ call ∷ c ∣ d) =
  next (lit (suc n) ∷ s ∣ e ∣ c ∣ d)

step (closure x e′ c′ ∷ v ∷ s ∣ e ∣ call ∷ c ∣ d) =
  next ([] ∣  v ∷ e′ ∣ c′ ∣ snapshot s e c ∷ d)

step (s ∣ e ∣ lit n ∷ c ∣ d) =
  next (lit n ∷ s ∣ e ∣ c ∣ d)

step (s ∣ e ∣ suc ∷ c ∣ d) =
  next (suc ∷ s ∣ e ∣ c ∣ d)

{-# NO_TERMINATION_CHECK #-}
run′ : ∀ {a} → SECD a → Either String (Value a)
run′ s with step s
... | next s′ = run′ s′
... | done v  = right v
... | error e = left e 

run : ∀ {a} → Term [] a → Either String (Value a)
run t = run′ ([] ∣ [] ∣ compile t ∣ [])

-- Show instance for values --

{-
private
  showValue : Nat → Value → ShowS
  showEnv   : Env → ShowS

  showValue p (lit n)         = shows n
  showValue p suc             = showString "suc"
  showValue p (closure x e v) = showParen (p > 0) $ showEnv e ∘ showString (" λ " & x & " → ") ∘ shows v

  showBinding : Name × Value → ShowS
  showBinding (x , v) = showString x ∘ showString " = " ∘ showValue 0 v

  showEnv′ : Env → ShowS
  showEnv′ []      = showString ""
  showEnv′ [ b ]   = showBinding b
  showEnv′ (b ∷ e) = showBinding b ∘ showString ", " ∘ showEnv′ e

  showEnv e = showString "[" ∘ showEnv′ e ∘ showString "]"

ShowValue : Show Value
ShowValue = record { showsPrec = showValue }

-}
