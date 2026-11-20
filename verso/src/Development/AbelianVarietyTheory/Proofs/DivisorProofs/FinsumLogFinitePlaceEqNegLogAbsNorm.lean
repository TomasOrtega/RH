import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.ProdFormula

/- English proof (translation)
Introduce `F _ _ δ hδ`. Establish `hpos : ∀ q : FinitePlace F, 0 < q δ` using `fun q => FinitePlace.pos_iff.2 hδ`. Rewrite using `[← Real.log_finprod hpos, FinitePlace.prod_eq_inv_abs_norm hδ]`. Use `push_cast`. Rewrite using `[Real.log_inv]`.
-/
theorem finsum_log_finitePlace_eq_neg_log_abs_norm :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 →
      ∑ᶠ q : FinitePlace F, Real.log (q δ) = -Real.log |((Algebra.norm ℚ δ : ℚ) : ℝ)| := by
  intro F _ _ δ hδ
  have hpos : ∀ q : FinitePlace F, 0 < q δ := fun q => FinitePlace.pos_iff.2 hδ
  rw [← Real.log_finprod hpos, FinitePlace.prod_eq_inv_abs_norm hδ]
  push_cast
  rw [Real.log_inv]

end GlobalTheory.ProdFormula
