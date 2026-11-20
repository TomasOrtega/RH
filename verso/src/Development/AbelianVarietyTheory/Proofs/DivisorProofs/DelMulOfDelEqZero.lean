import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.CxForm.DelClosed

/- English proof (translation)
Introduce `M _ n A α β hα hβ hdβ`. Use function extensionality and compare the values at `x`. Establish `hl : A.loc (α * β) x.1.1 = fun v => A.loc α x.1.1 v * A.loc β x.1.1 v`. Use function extensionality and compare the values at `(FormMul.loc_mul A α β _)`. Take `⟨y, hy⟩` from `FormMul.delAt_mul (FormMul.differentiableAt_coef hα x) (FormMul.differentiableAt_coef hβ x)`.

Establish `h2 : delAt (A.loc β x.1.1) x.crd = 0` using `congrFun hdβ x`. Use `show delAt (A.loc (α * β) x.1.1) x.crd = delAt (A.loc α x.1.1) x.crd * β x`. Rewrite using `[hl, hy, h2, mul_zero, add_zero, HolAtlas.loc_crd]`.
-/
theorem del_mul_of_del_eq_zero : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n)
    (α β : A.Fld), A.IsForm α → A.IsForm β → A.del β = 0 → A.del (α * β) = A.del α * β := by
  intro M _ n A α β hα hβ hdβ
  funext x
  have hl : A.loc (α * β) x.1.1 = fun v => A.loc α x.1.1 v * A.loc β x.1.1 v :=
    funext (FormMul.loc_mul A α β _)
  obtain ⟨y, hy⟩ := FormMul.delAt_mul (FormMul.differentiableAt_coef hα x) (FormMul.differentiableAt_coef hβ x)
  have h2 : delAt (A.loc β x.1.1) x.crd = 0 := congrFun hdβ x
  show delAt (A.loc (α * β) x.1.1) x.crd = delAt (A.loc α x.1.1) x.crd * β x
  rw [hl, hy, h2, mul_zero, add_zero, HolAtlas.loc_crd]

end GlobalTheory.CxForm.DelClosed
