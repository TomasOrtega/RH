import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieOfIndefiniteUnitaryLieRightAc
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.SpLieD

open Matrix GlobalTheory.RealLift.SpLie

/- English proof (translation)
Introduce `ι l _ _ _ _ P Q R S φ hφ Y hY`. Set `G : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ)` to `{ toFun := fun c w => c w * (Y w)ᵀ map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul] map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }`. Use `set Z := LinearMap.toMatrix' (φ.toLinearMap ∘ₗ G ∘ₗ φ.symm.toLinearMap) with hZdef`. Establish `hZ : ∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ`. Introduce `c`.

Rewrite using `[hZdef, LinearMap.toMatrix'_mulVec]`. Simplify using `[G]`. Use `⟨Z, ?_, hZ, ?_⟩` and prove the remaining obligations. Use `mem_sp_of_sympl Z fun u v => ?_` and prove the remaining obligations. Take `⟨c, rfl⟩` from `φ.surjective u`.

Take `⟨c', rfl⟩` from `φ.surjective v`. Establish `hs : (∑ w, ∑ a, ∑ b, lineSign a b * (c w * (Y w)ᵀ) a b * star (c' w a b)) + (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star ((c' w * (Y w)ᵀ) a b)) = 0`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_eq_zero fun w _ => sum_zero _ _ _ (hY w)`. Rewrite using `[hZ, hZ, hφ, hφ, ← mul_add, ← Complex.add_im]`.

Simplify using `only [hs, Complex.zero_im, mul_zero]`. Introduce `t c`. Establish `hpow : ∀ (n : ℕ) (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), (t • Z) ^ n *ᵥ φ c = φ fun w => c w * ((t • Y w) ^ n)ᵀ`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro c`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `c`. Rewrite using `[pow_succ, ← mulVec_mulVec, Matrix.smul_mulVec, hZ, ← φ.map_smul]`.

Establish `: (t • fun w => c w * (Y w)ᵀ) = fun w => c w * (t • Y w)ᵀ`. Use function extensionality and compare the values at `w`. Simplify using `[Matrix.transpose_smul, Matrix.mul_smul]`. Rewrite using `[this, ih]`. Use `congr 1`.

Use function extensionality and compare the values at `w`. Rewrite using `[pow_succ, Matrix.transpose_mul, Matrix.mul_assoc]`. Use `letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra`. Establish `h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • (t • Z) ^ n) *ᵥ φ c) (NormedSpace.exp (t • Z) *ᵥ φ c)` using `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Z)).map (Matrix.mulVec.addMonoidHomLeft (φ c)) (Continuous.matrix_mulVec continuous_id continuous_const)`.

Establish `hw : ∀ w, HasSum (fun n : ℕ => c w * (((n.factorial : ℝ)⁻¹ • (t • Y w) ^ n))ᵀ) (c w * (NormedSpace.exp (t • Y w))ᵀ)`. Introduce `w`. Use `letI : NormedRing (Mat (R w) (S w)) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Mat (R w) (S w)) := Matrix.linftyOpNormedAlgebra`. Use `(NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Y w)).matrix_transpose` as an intermediate fact.

Conclude with `this.map (AddMonoidHom.mk' (fun M => c w * M) fun _ _ => Matrix.mul_add _ _ _) (continuous_const.matrix_mul continuous_id)`. Establish `h2` using `(Pi.hasSum.2 hw).map φ (LinearMap.continuous_of_finiteDimensional φ.toLinearMap)`. Use `h1.unique ?_` and prove the remaining obligations. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`.

Simplify using `only [Function.comp_def]`. Rewrite using `[Matrix.smul_mulVec, hpow, ← φ.map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Simplify using `[Matrix.transpose_smul, Matrix.mul_smul]`.
-/
theorem exists_sp_rightActD : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ∀ w : ι, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ Y hY
  let G : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun c w => c w * (Y w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  set Z := LinearMap.toMatrix' (φ.toLinearMap ∘ₗ G ∘ₗ φ.symm.toLinearMap) with hZdef
  have hZ : ∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ := by
    intro c; rw [hZdef, LinearMap.toMatrix'_mulVec]; simp [G]
  refine ⟨Z, ?_, hZ, ?_⟩
  · refine mem_sp_of_sympl Z fun u v => ?_
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    have hs : (∑ w, ∑ a, ∑ b, lineSign a b * (c w * (Y w)ᵀ) a b * star (c' w a b)) +
        (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star ((c' w * (Y w)ᵀ) a b)) = 0 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun w _ => sum_zero _ _ _ (hY w)
    rw [hZ, hZ, hφ, hφ, ← mul_add, ← Complex.add_im]
    simp only [hs, Complex.zero_im, mul_zero]
  · intro t c
    have hpow : ∀ (n : ℕ) (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
        (t • Z) ^ n *ᵥ φ c = φ fun w => c w * ((t • Y w) ^ n)ᵀ := by
      intro n
      induction n with
      | zero => intro c; simp
      | succ n ih =>
        intro c
        rw [pow_succ, ← mulVec_mulVec, Matrix.smul_mulVec, hZ, ← φ.map_smul]
        have : (t • fun w => c w * (Y w)ᵀ) = fun w => c w * (t • Y w)ᵀ := by
          funext w; simp [Matrix.transpose_smul, Matrix.mul_smul]
        rw [this, ih]
        congr 1; funext w
        rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc]
    letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
    have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • (t • Z) ^ n) *ᵥ φ c)
        (NormedSpace.exp (t • Z) *ᵥ φ c) :=
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Z)).map
        (Matrix.mulVec.addMonoidHomLeft (φ c)) (Continuous.matrix_mulVec continuous_id continuous_const)
    have hw : ∀ w, HasSum (fun n : ℕ => c w * (((n.factorial : ℝ)⁻¹ • (t • Y w) ^ n))ᵀ)
        (c w * (NormedSpace.exp (t • Y w))ᵀ) := by
      intro w
      letI : NormedRing (Mat (R w) (S w)) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℝ (Mat (R w) (S w)) := Matrix.linftyOpNormedAlgebra
      have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Y w)).matrix_transpose
      exact this.map (AddMonoidHom.mk' (fun M => c w * M) fun _ _ => Matrix.mul_add _ _ _)
        (continuous_const.matrix_mul continuous_id)
    have h2 := (Pi.hasSum.2 hw).map φ (LinearMap.continuous_of_finiteDimensional φ.toLinearMap)
    refine h1.unique ?_
    convert h2 using 1
    funext n
    simp only [Function.comp_def]
    rw [Matrix.smul_mulVec, hpow, ← φ.map_smul]
    congr 1; funext w
    simp [Matrix.transpose_smul, Matrix.mul_smul]

end GlobalTheory.HoweD.SpLieD
