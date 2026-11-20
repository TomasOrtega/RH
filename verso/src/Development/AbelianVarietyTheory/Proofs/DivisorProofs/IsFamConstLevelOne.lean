import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isFam_const_of_isMF (ι : Type) (act : ι → SL(2, ℤ) → ι) (k : ℤ) (F : ℍ → ℂ)
    (h : IsMF k F) : IsFam act k fun _ => F := by
  intro i γ
  funext τ
  have hne : UpperHalfPlane.denom γ τ ^ k ≠ 0 := zpow_ne_zero _ (UpperHalfPlane.denom_ne_zero _ _)
  rw [ModularForm.SL_slash_apply]
  beta_reduce
  rw [h.smul_eq γ τ, zpow_neg, mul_right_comm, mul_inv_cancel₀ hne, one_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isFam_const_E4 (ι : Type) (act : ι → SL(2, ℤ) → ι) : IsFam act 4 (fun _ => ⇑E₄) :=
  isFam_const_of_isMF ι act 4 _ ⟨E₄, fun _ => rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isFam_const_E6 (ι : Type) (act : ι → SL(2, ℤ) → ι) : IsFam act 6 (fun _ => ⇑E₆) :=
  isFam_const_of_isMF ι act 6 _ ⟨E₆, fun _ => rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isFam_const_DD (ι : Type) (act : ι → SL(2, ℤ) → ι) : IsFam act 12 fun _ => DD :=
  isFam_const_of_isMF ι act 12 _ ReciprocityTheory.ChartRestriction.L1.isMF_DD

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem isFam_const_level_one (ι : Type) (act : ι → SL(2, ℤ) → ι) :
    (∀ (k : ℤ) (F : ℍ → ℂ), IsMF k F → IsFam act k fun _ => F) ∧ IsFam act 4 (fun _ => ⇑E₄) ∧
      IsFam act 6 (fun _ => ⇑E₆) ∧ IsFam act 12 fun _ => DD :=
  ⟨isFam_const_of_isMF ι act, isFam_const_E4 ι act, isFam_const_E6 ι act, isFam_const_DD ι act⟩

end GlobalTheory.QFam
