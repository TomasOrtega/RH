import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.RegInv

/- English proof (translation)
Establish `h : (Hpk k r).det * (Hpk k r).det = 1`. Rewrite using `[← Matrix.det_mul, GBasic.Hpk_sq, Matrix.det_one]`. Conclude with `⟨⟨_, _, h, h⟩, rfl⟩`.
-/
theorem hpk_isUnit_det (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h : (Hpk k r).det * (Hpk k r).det = 1 := by
    rw [← Matrix.det_mul, GBasic.Hpk_sq, Matrix.det_one]
  exact ⟨⟨_, _, h, h⟩, rfl⟩

/- English proof (translation)
The claim follows from `(unitary_group_holds _ (Hpk k r) (hpk_isUnit_det k r)).2.2 γ h`.
-/
private lemma unit_lemma' {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) : IsUnit γ.det ∧ γ⁻¹ ∈ GG k r :=
  (unitary_group_holds _ (Hpk k r) (hpk_isUnit_det k r)).2.2 γ h

/- English proof (translation)
The claim follows from `(unit_lemma' h).2`.
-/
theorem inv_mem {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) : γ⁻¹ ∈ GG k r := (unit_lemma' h).2

/- English proof (translation)
Establish `hγ : γᴴ * Hpk k r * γ = Hpk k r` using `h`. Simplify using `only [herm]`. Rewrite using `[Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hγ]`.
-/
private lemma herm_mulVec_eq_of_mem_GG {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (γ *ᵥ x) (γ *ᵥ y) = herm (Hpk k r) x y := by
  have hγ : γᴴ * Hpk k r * γ = Hpk k r := h
  simp only [herm]
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hγ]

/- English proof (translation)
Simplify using `only [herm]`. Rewrite using `[Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, GBasic.Hpk_herm]`.
-/
private lemma herm_Hpk_swap (k r : ℕ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (herm (Hpk k r) y x) := by
  simp only [herm]
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, GBasic.Hpk_herm]

/- English proof (translation)
Establish `hv : γ *ᵥ (γ⁻¹ *ᵥ v) = v`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_lemma' h).1, Matrix.one_mulVec]`. Rewrite using `[← herm_mulVec_eq_of_mem_GG h (γ⁻¹ *ᵥ v) w, hv]`. Conclude with `herm_Hpk_swap k r _ _`.
-/
theorem herm_inv {k r : ℕ} {γ : Mat k r} (h : γ ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (γ⁻¹ *ᵥ v) w = star (herm (Hpk k r) (γ *ᵥ w) v) := by
  have hv : γ *ᵥ (γ⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_lemma' h).1, Matrix.one_mulVec]
  rw [← herm_mulVec_eq_of_mem_GG h (γ⁻¹ *ᵥ v) w, hv]
  exact herm_Hpk_swap k r _ _

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Zhat, Matrix.conjTranspose_apply]`. Conclude with `herm_inv h _ _`.
-/
theorem zhat_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r) :
    Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ := by
  ext a b
  simp only [Zhat, Matrix.conjTranspose_apply]
  exact herm_inv h _ _

/- English proof (translation)
Simplify using `only [Dmin]`. Rewrite using `[zhat_inv z z' h, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]`.
-/
theorem dmin_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r)
    (l : Fin (r + 2)) : Dmin k r z' z γ⁻¹ l = star (Dmin k r z z' γ l) := by
  simp only [Dmin]
  rw [zhat_inv z z' h, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]

/- English proof (translation)
Simplify using `only [Gf, dmin_inv z z' h, Complex.star_def, Complex.normSq_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gf_inv {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (h : γ ∈ GG k r) :
    Gf k r z' z γ⁻¹ = Gf k r z z' γ := by
  simp only [Gf, dmin_inv z z' h, Complex.star_def, Complex.normSq_conj]
  ring

/- English proof (translation)
Use `⟨zhat_inv z z' h, ?_⟩` and prove the remaining obligations. Simplify using `only [Greg, Set.mem_ofPred_eq, dmin_inv z z' h, gf_inv z z' h, star_ne_zero, h, inv_mem h, true_and]`.
-/
theorem zhat_inv_and_reg (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (h : γ ∈ GG k r) :
    Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ ∧ (γ ∈ Greg k r z z' ↔ γ⁻¹ ∈ Greg k r z' z) := by
  refine ⟨zhat_inv z z' h, ?_⟩
  simp only [Greg, Set.mem_ofPred_eq, dmin_inv z z' h, gf_inv z z' h, star_ne_zero, h, inv_mem h,
    true_and]

end GlobalTheory.SgInf.RegInv
