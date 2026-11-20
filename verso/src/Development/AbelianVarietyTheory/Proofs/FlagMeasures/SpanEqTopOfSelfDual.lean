import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FullySplitStabilizers
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianMassFormula
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal

namespace GlobalTheory.SgSpan

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem form_smul_left {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (a : E) (x y : Fin n → E) : form σ J (a • x) y = a * form σ J x y := by
  simp only [form, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem form_smul_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (a : E) (x y : Fin n → E) : form σ J x (a • y) = σ a * form σ J x y := by
  simp only [form, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem form_add_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x y z : Fin n → E) : form σ J x (y + z) = form σ J x y + form σ J x z := by
  simp only [form, dotProduct, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem form_zero_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x : Fin n → E) : form σ J x 0 = 0 := by
  simp [form, dotProduct]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem span_eq_top_of_selfDual : ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)), (∀ x : 𝓞 E, IsIntegral ℤ (σ (x : E))) → GlobalTheory.SgGlob.SelfDual σ J Λ → Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by
  classical
  intro E _ _ σ n J Λ hσ h
  obtain ⟨⟨s, hs⟩, hd⟩ := h
  rw [eq_top_iff]
  intro v _
  obtain ⟨N, hN0, hN⟩ := exists_integral_multiples ℤ ℚ (s.image fun w => form σ J v w)
  have hrange : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.isIntegral_coe
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN0
  have hmem : (N : E) • v ∈ Λ := by
    rw [hd]
    intro w hw
    rw [hrange]
    rw [← hs] at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      rw [form_smul_left]
      have := hN _ (Finset.mem_image_of_mem _ hw)
      simpa [zsmul_eq_mul] using this
    | zero => rw [form_zero_right]; exact isIntegral_zero
    | add x y _ _ hx hy => rw [form_add_right]; exact hx.add hy
    | smul a x _ hx =>
      have : a • x = (a : E) • x := rfl
      rw [this, form_smul_right]
      exact (hσ a).mul hx
  have : v = (N : E)⁻¹ • ((N : E) • v) := by
    rw [smul_smul, inv_mul_cancel₀ hNE, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.SgSpan
