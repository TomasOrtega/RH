import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FullySplitStabilizers
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianMassFormula
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct ENNReal

namespace GlobalTheory.SgSpan

/- English proof (translation)
Simplify using `only [form, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem form_smul_left {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (a : E) (x y : Fin n → E) : form σ J (a • x) y = a * form σ J x y := by
  simp only [form, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [form, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]`.
-/
theorem form_smul_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (a : E) (x y : Fin n → E) : form σ J x (a • y) = σ a * form σ J x y := by
  simp only [form, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `only [form, dotProduct, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem form_add_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x y z : Fin n → E) : form σ J x (y + z) = form σ J x y + form σ J x z := by
  simp only [form, dotProduct, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[form, dotProduct]`.
-/
theorem form_zero_right {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x : Fin n → E) : form σ J x 0 = 0 := by
  simp [form, dotProduct]

/- English proof (translation)
Introduce `E _ _ σ n J Λ hσ h`. Take `⟨⟨s, hs⟩, hd⟩` from `h`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Take `⟨N, hN0, hN⟩` from `exists_integral_multiples ℤ ℚ (s.image fun w => form σ J v w)`.

Establish `hrange : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.isIntegral_coe`.

Introduce `hx`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Establish `hNE : (N : E) ≠ 0` using `by exact_mod_cast hN0`. Establish `hmem : (N : E) • v ∈ Λ`. Rewrite using `[hd]`.

Introduce `w hw`. Rewrite using `[hrange]`. Rewrite `hw` using `[← hs]`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`.

Rewrite using `[form_smul_left]`. Use `hN _ (Finset.mem_image_of_mem _ hw)` as an intermediate fact. Simplify `this` using `[zsmul_eq_mul]`. Consider the case `zero => rw [form_zero_right]`. Conclude with `isIntegral_zero`.

Consider the case `add x y _ _ hx hy => rw [form_add_right]`. Conclude with `hx.add hy`. Consider the case `smul a x _ hx`. Establish `: a • x = (a : E) • x` using `rfl`. Rewrite using `[this, form_smul_right]`.

Conclude with `(hσ a).mul hx`. Establish `: v = (N : E)⁻¹ • ((N : E) • v)`. Rewrite using `[smul_smul, inv_mul_cancel₀ hNE, one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
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
