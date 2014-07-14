
module TypeCheck where

open import Prelude
open import Lists

open import Term
open WellTyped
open Unchecked  renaming (Term to Expr)
open import Term.Show
open import Term.Parse

TypeError = String

TC : Set → Set
TC = Either TypeError

typeError : ∀ {A} → TypeError → TC A
typeError = left

data TypeChecked Γ : Expr → Set where
  ok : ∀ a (v : Term Γ a) → TypeChecked Γ (forgetTypes v)

data CheckedVar (Γ : Cxt) x : Set where
  ok : ∀ a (i : (x , a) ∈ Γ) → CheckedVar Γ x

lookupVarSuc : ∀ {x y a Γ} → CheckedVar Γ x → CheckedVar ((y , a) ∷ Γ) x
lookupVarSuc (ok a₁ i) = ok a₁ (suc i)

lookupVar : (x : Name) (Γ : Cxt) → TC (CheckedVar Γ x)
lookupVar x [] = typeError ("not in scope:" & x)
lookupVar x ((y , a) ∷ Γ) with x == y
lookupVar x ((.x , a) ∷ Γ) | yes refl = pure (ok a (zero refl))
lookupVar x ((y , a) ∷ Γ)  | no _     = lookupVarSuc <$> lookupVar x Γ

checkedVar : ∀ {Γ x} → CheckedVar Γ x → TypeChecked Γ (var x)
checkedVar (ok a i) = ok a (var _ i)

checkedLam : ∀ {Γ x a e} → TypeChecked ((x , a) ∷ Γ) e → TypeChecked Γ (lam x a e)
checkedLam (ok a₁ v) = ok (_ => a₁) (lam _ _ v)

checkedApp : ∀ {Γ e e₁} → TypeChecked Γ e → TypeChecked Γ e₁ → TC (TypeChecked Γ (app e e₁))
checkedApp (ok nat v) (ok a₁ v₁) = typeError "nat is not fun"
checkedApp (ok (a => b) v) (ok a₁ v₁) with a == a₁
checkedApp (ok (a => b) v) (ok .a v₁) | yes refl = pure (ok b (app v v₁))
checkedApp (ok (a => b) v) (ok a₁ v₁) | no _     = typeError "types don't match"

-- Exercise: Implement the type checker. When you are done,
--           go to Lambda.agda and make it type check the
--           input and print the inferred type.
typeCheck : ∀ Γ (e : Expr) → TC (TypeChecked Γ e)
typeCheck Γ (var x) = checkedVar <$> lookupVar x Γ
typeCheck Γ (lit x) = right (ok nat (lit x))
typeCheck Γ suc = right (ok (nat => nat) suc)
typeCheck Γ (app e e₁) =
  typeCheck Γ e  >>= λ v  →
  typeCheck Γ e₁ >>= λ v₁ →
  checkedApp v v₁
typeCheck Γ (lam x a e) = checkedLam <$> typeCheck ((x , a) ∷ Γ) e

-- Forget which unchecked term we started with.
forgetOrigin : ∀ {Γ e} → TypeChecked Γ e → Σ Type (Term Γ)
forgetOrigin (ok a v) = a , v

parseAndTypeCheck : String → TC (Σ Type (Term []))
parseAndTypeCheck s =
  flip (maybe (typeError "Parse error")) (parseTerm s) $ λ e →
  forgetOrigin <$> typeCheck [] e

