
module Term.Eval where

open import Prelude

open import Lists
open import Term
open WellTyped

El : Type → Set
El nat      = Nat
El (a => b) = El a → El b

Env : Cxt → Set
Env Γ = All (El ∘ snd) Γ

lookupVar : ∀ {Γ a} x → (x , a) ∈ Γ → Env Γ → El a
lookupVar x (zero refl) (p ∷ env) = p
lookupVar x (suc i)     (p ∷ env) = lookupVar x i env


-- Exercise: Implement an evaluator for well-typed terms.
eval : ∀ {Γ a} → Term Γ a → Env Γ → El a
eval (var x i) env = lookupVar x i env
eval (app e e₁) env = eval e env (eval e₁ env)
eval (lam x a e) env x₁ = eval e (x₁ ∷ env)
eval (lit n) env = n
eval suc env x = suc x
