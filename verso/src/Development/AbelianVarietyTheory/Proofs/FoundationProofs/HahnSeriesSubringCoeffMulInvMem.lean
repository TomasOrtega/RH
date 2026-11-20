import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HahnSub

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_mul_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h h' : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hh' : ∀ r, h'.coeff r ∈ A) (r : ℚ) : (h * h').coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact A.sum_mem fun ij _ => A.mul_mem (hh ij.1) (hh' ij.2)

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_inv_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hl : h.leadingCoeff⁻¹ ∈ A) (r : ℚ) : (h⁻¹).coeff r ∈ A := by
  by_cases h0 : h = 0
  · subst h0
    simp

  let g : HahnSeries ℚ A :=
    { coeff := fun s => ⟨h.coeff s, hh s⟩
      isPWO_support' := h.isPWO_support.mono fun s hs e => hs (Subtype.ext e) }
  have hg : ∀ s, (g.coeff s : Ω) = h.coeff s := fun s => rfl
  have hg0 : g ≠ 0 := by
    intro e
    apply h0
    ext s
    rw [← hg, e]
    rfl
  have hord : g.order = h.order := by
    apply le_antisymm
    · apply HahnSeries.order_le_of_coeff_ne_zero
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 h0
      rw [HahnSeries.leadingCoeff_eq, ← hg, e]
      rfl
    · apply HahnSeries.order_le_of_coeff_ne_zero
      rw [← hg]
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 hg0
      rw [HahnSeries.leadingCoeff_eq]
      exact Subtype.ext e
  have hlead : (g.leadingCoeff : Ω) = h.leadingCoeff := by
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hg, hord]
  have hunit : IsUnit g.leadingCoeff := by
    refine IsUnit.of_mul_eq_one (⟨h.leadingCoeff⁻¹, hl⟩ : A) ?_
    apply Subtype.ext
    show (g.leadingCoeff : Ω) * h.leadingCoeff⁻¹ = 1
    rw [hlead]
    exact mul_inv_cancel₀ (HahnSeries.leadingCoeff_ne_zero.2 h0)
  obtain ⟨v, hv⟩ := (HahnSeries.isUnit_iff.2 hunit).exists_right_inv
  let f : A →ₙ+* Ω := A.subtype.toNonUnitalRingHom
  have hgf : g.map f = h := by
    ext s
    rfl
  have hone : (1 : HahnSeries ℚ A).map f = 1 := by
    ext s
    rw [HahnSeries.map_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> rfl
  have key : h * v.map f = 1 := by
    rw [← hgf, ← HahnSeries.map_mul, hv, hone]
  rw [inv_eq_of_mul_eq_one_right key, HahnSeries.map_coeff]
  exact (v.coeff r).2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem coeff_mul_inv_mem : ∀ (Ω : Type) [Field Ω] (A : Subring Ω), (∀ h h' : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → (∀ r, h'.coeff r ∈ A) → ∀ r, (h * h').coeff r ∈ A) ∧ ∀ h : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → h.leadingCoeff⁻¹ ∈ A → ∀ r, (h⁻¹).coeff r ∈ A := by
  intro Ω _ A
  exact ⟨fun h h' hh hh' r => coeff_mul_mem A h h' hh hh' r,
    fun h hh hl r => coeff_inv_mem A h hh hl r⟩

end GlobalTheory.HahnSub
