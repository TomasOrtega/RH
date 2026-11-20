import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace KLinesGramPosDef

open Matrix

variable {K : Type*} [Field K] {n : ℕ} {ι : Type*}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[gramAt, embVec, Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem gramAt_eq (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) (u : ι → Fin n → K) :
    gramAt h σ u = (((Matrix.of fun j a => u a j).map σ)ᴴ * h *
      (Matrix.of fun j a => u a j).map σ) := by
  ext a b
  simp [gramAt, embVec, Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/- English proof (translation)
Use `set Uk : Matrix (Fin n) ι K := Matrix.of fun j a => u a j with hUk`. Establish `hinj : LinearMap.ker Uk.mulVecLin = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `c hc`. Rewrite `hu` using `[Fintype.linearIndependent_iff]`.

Use function extensionality and compare the values at `a`. Use `hu c ?_ a` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Use `congrFun hc j` as an intermediate fact. Simplify `this` using `[Uk, Matrix.mulVec, dotProduct, mul_comm]`.

Take `⟨g, hg⟩` from `Uk.mulVecLin.exists_leftInverse_of_injective hinj`. Use `set Lk : Matrix ι (Fin n) K := LinearMap.toMatrix' g`. Establish `hL : Lk * Uk = 1`. Use `congrArg LinearMap.toMatrix' hg` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']`. Then use the resulting hypothesis.

Establish `hLσ : Lk.map σ * Uk.map σ = 1`. Rewrite using `[← Matrix.map_mul, hL, Matrix.map_one _ σ.map_zero σ.map_one]`. Introduce `x y hxy`. Use `congrArg (fun v => (Lk.map σ) *ᵥ v) hxy` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, hLσ]`.
-/
theorem mulVec_injective [Fintype ι] (σ : K →+* ℂ) (u : ι → Fin n → K) (hu : LinearIndependent K u) :
    Function.Injective ((Matrix.of fun j a => u a j).map σ).mulVec := by
  classical
  set Uk : Matrix (Fin n) ι K := Matrix.of fun j a => u a j with hUk
  have hinj : LinearMap.ker Uk.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Fintype.linearIndependent_iff] at hu
    funext a
    refine hu c ?_ a
    funext j
    have := congrFun hc j
    simpa [Uk, Matrix.mulVec, dotProduct, mul_comm] using this
  obtain ⟨g, hg⟩ := Uk.mulVecLin.exists_leftInverse_of_injective hinj
  set Lk : Matrix ι (Fin n) K := LinearMap.toMatrix' g
  have hL : Lk * Uk = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin'] at this
  have hLσ : Lk.map σ * Uk.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have := congrArg (fun v => (Lk.map σ) *ᵥ v) hxy
  simpa [Matrix.mulVec_mulVec, hLσ] using this

end KLinesGramPosDef

open KLinesGramPosDef Matrix ComplexOrder in

/- English proof (translation)
Introduce `K _ n h σ ι _ u hh hu`. Rewrite using `[gramAt_eq]`. Conclude with `hh.conjTranspose_mul_mul_same (mulVec_injective σ u hu)`.
-/
theorem LinesGramPosDef.proof : LinesGramPosDef.Statement := by
  intro K _ n h σ ι _ u hh hu
  rw [gramAt_eq]
  exact hh.conjTranspose_mul_mul_same (mulVec_injective σ u hu)

end GroundTheory.Heights₂.Heights
