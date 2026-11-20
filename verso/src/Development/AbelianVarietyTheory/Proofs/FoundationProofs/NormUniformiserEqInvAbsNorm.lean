import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open scoped NNReal
open NumberField IsDedekindDomain

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ _ v ϖ h`. Apply `NNReal.eq` to reduce the goal to its premises. Rewrite using `[coe_nnnorm, FinitePlace.norm_def]`. Unfold `Formalism.UG.IsUnifV at h`. Rewrite using `[h]`.

Establish `hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0` using `WithZero.coe_ne_zero`. Rewrite using `[WithZeroMulInt.toNNReal_neg_apply _ hne]`. Simplify using `only [WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv]`.
-/
theorem norm_uniformiser_eq_inv_absNorm :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : v.adicCompletion F),
      Formalism.UG.IsUnifV F v ϖ → ‖ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ := by
  intro F _ _ v ϖ h
  apply NNReal.eq
  rw [coe_nnnorm, FinitePlace.norm_def]
  unfold Formalism.UG.IsUnifV at h
  rw [h]
  have hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    WithZero.coe_ne_zero
  rw [WithZeroMulInt.toNNReal_neg_apply _ hne]
  simp only [WithZero.unzero_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv]

end GlobalTheory
