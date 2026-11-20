import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFreeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
The claim follows from `(isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).2 (TensorProduct.isBaseChange ℤ M ℚ)`.
-/
theorem isLocalizedModule_ratTensor (M : Type) [AddCommGroup M] :
    IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) :=
  (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).2 (TensorProduct.isBaseChange ℤ M ℚ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toEnd0_apply {K : Type} [Field K] (A : AbVar K) (f : End A) :
    toEnd0 A f = TensorProduct.mk ℤ ℚ (End A) 1 f := rfl

/- English proof (translation)
Introduce `K _ A`. Use `haveI := isLocalizedModule_ratTensor (End A)`. Use `⟨fun f g h => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[toEnd0_apply, toEnd0_apply]`. Take `⟨c, hc⟩` from `IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ) h`.

Establish `hc0 : (c : ℤ) ≠ 0` using `nonZeroDivisors.coe_ne_zero c`. Establish `h1 : (c : ℤ) • (f - g) = 0`. Rewrite using `[smul_sub, sub_eq_zero]`. Simplify `hc` using `[Submonoid.smul_def]`. Conclude with `sub_eq_zero.1 (GlobalTheory.T.abVar_hom_eq_zero_of_nsmul_eq_zero K A A (c : ℤ) (f - g) hc0 h1)`.

Take `⟨⟨m, c⟩, hc⟩` from `IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ (End A) 1) x`. Establish `hc0 : (c : ℤ) ≠ 0` using `nonZeroDivisors.coe_ne_zero c`. Simplify using `only [Submonoid.smul_def] at hc`. Break down `Int.natAbs_eq (c : ℤ) with h | h` into its components or cases. Use `⟨(c : ℤ).natAbs, m, Int.natAbs_pos.2 hc0, ?_⟩` and prove the remaining obligations.

Rewrite using `[toEnd0_apply, ← hc, ← natCast_zsmul, ← h]`. Use `⟨(c : ℤ).natAbs, -m, Int.natAbs_pos.2 hc0, ?_⟩` and prove the remaining obligations. Establish `h' : (((c : ℤ).natAbs : ℕ) : ℤ) = -(c : ℤ)` using `by omega`. Rewrite using `[toEnd0_apply, map_neg, ← hc, ← natCast_zsmul, h', neg_smul]`.
-/
theorem toEnd0_injective_and_fraction : ∀ (K : Type) [Field K] (A : AbVar K),
    Function.Injective (toEnd0 A) ∧ ∀ x : End0 A, ∃ (n : ℕ) (f : End A), 0 < n ∧ n • x = toEnd0 A f := by
  intro K _ A
  haveI := isLocalizedModule_ratTensor (End A)
  refine ⟨fun f g h => ?_, fun x => ?_⟩
  · rw [toEnd0_apply, toEnd0_apply] at h
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ) h
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    have h1 : (c : ℤ) • (f - g) = 0 := by
      rw [smul_sub, sub_eq_zero]
      simpa [Submonoid.smul_def] using hc
    exact sub_eq_zero.1 (GlobalTheory.T.abVar_hom_eq_zero_of_nsmul_eq_zero K A A (c : ℤ) (f - g) hc0 h1)
  · obtain ⟨⟨m, c⟩, hc⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ (End A) 1) x
    have hc0 : (c : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    simp only [Submonoid.smul_def] at hc
    rcases Int.natAbs_eq (c : ℤ) with h | h
    · refine ⟨(c : ℤ).natAbs, m, Int.natAbs_pos.2 hc0, ?_⟩
      rw [toEnd0_apply, ← hc, ← natCast_zsmul, ← h]
    · refine ⟨(c : ℤ).natAbs, -m, Int.natAbs_pos.2 hc0, ?_⟩
      have h' : (((c : ℤ).natAbs : ℕ) : ℤ) = -(c : ℤ) := by omega
      rw [toEnd0_apply, map_neg, ← hc, ← natCast_zsmul, h', neg_smul]

end GlobalTheory.AV.AbVar
