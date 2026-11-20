import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter

open Matrix

namespace GlobalTheory.OneParamUnitary

open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
Use `haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _`. Establish `hsm : ContDiff ℝ ∞ u` using `GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (Fin n) (Fin n) ℂ) u hc h0 hadd`. Establish `hdiff : Differentiable ℝ u` using `hsm.differentiable (by simp)`. Use `set Y := deriv u 0 with hY`. Establish `hY0 : HasDerivAt u Y 0` using `(hdiff 0).hasDerivAt`.

Establish `hder : ∀ t, HasDerivAt u (u t * Y) t`. Introduce `t`. Establish `h1 : HasDerivAt (fun s => u (s - t)) Y t` using `(show HasDerivAt u Y (t - t) by simpa using hY0).comp_sub_const t t`. Establish `h2` using `h1.const_mul (u t)`. Establish `h3 : (fun s => u t * u (s - t)) = u`.

Use function extensionality and compare the values at `s`. Rewrite using `[← hadd]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[h3]`. Then use the resulting hypothesis.

Establish `hexp : ∀ t : ℝ, u t = NormedSpace.exp (t • Y)` using `by set v : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => u t * NormedSpace.exp (t • (-Y)) with hv`. Establish `hvd : ∀ t, HasDerivAt v 0 t`. Introduce `t`. Establish `hE` using `hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Y) t`. Use `(hder t).mul hE` as an intermediate fact.

Rewrite `this` using `[Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]`. Conclude with `this`. Establish `hvc : ∀ t, v t = v 0` using `fun t => is_const_of_deriv_eq_zero (fun s => (hvd s).differentiableAt) (fun s => (hvd s).deriv) t 0`. Establish `hv0 : v 0 = 1` using `by simp [hv, h0]`. Introduce `t`.

Establish `hcomm : Commute (t • (-Y)) (t • Y)` using `((Commute.refl Y).neg_left.smul_left t).smul_right t`. Establish `hinv : NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ hcomm, smul_neg, neg_add_cancel, NormedSpace.exp_zero]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨Y, ?_, hexp⟩` and prove the remaining obligations.

Use `show Yᴴ * G + G * Y = 0`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ` to `{ toFun := fun A => star A map_add' := fun A B => star_add A B map_smul' := fun c A => by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul] }`. Establish `hst : HasDerivAt (fun t => star (u t)) (star Y) 0` using `(LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hY0`. Establish `hw` using `(hst.mul_const G).mul hY0`. Establish `hconst : ((fun t => star (u t) * G) * u) = fun _ => G`.

Use function extensionality and compare the values at `t`. Conclude with `hU t`. Rewrite `hw` using `[hconst]`. Use `(hasDerivAt_const (0 : ℝ) G).unique hw` as an intermediate fact. Rewrite `*` using `[h0, star_one, Matrix.one_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose]`.

Conclude with `this.symm`.
-/
theorem oneParam_eq_exp_lieU {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (u : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hc : Continuous u) (h0 : u 0 = 1) (hadd : ∀ s t, u (s + t) = u s * u t)
    (hU : ∀ t, u t ∈ Formalism.QuantumDeterminants.UH G) :
    ∃ Y ∈ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.lieU G, ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have hsm : ContDiff ℝ ∞ u :=
    GlobalTheory.contDiff_of_continuous_oneParameter (Matrix (Fin n) (Fin n) ℂ) u hc h0 hadd
  have hdiff : Differentiable ℝ u := hsm.differentiable (by simp)
  set Y := deriv u 0 with hY
  have hY0 : HasDerivAt u Y 0 := (hdiff 0).hasDerivAt
  have hder : ∀ t, HasDerivAt u (u t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => u (s - t)) Y t :=
      (show HasDerivAt u Y (t - t) by simpa using hY0).comp_sub_const t t
    have h2 := h1.const_mul (u t)
    have h3 : (fun s => u t * u (s - t)) = u := by
      funext s
      rw [← hadd]; congr 1; ring
    rwa [h3] at h2

  have hexp : ∀ t : ℝ, u t = NormedSpace.exp (t • Y) := by
    set v : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => u t * NormedSpace.exp (t • (-Y)) with hv
    have hvd : ∀ t, HasDerivAt v 0 t := by
      intro t
      have hE := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-Y) t
      have := (hder t).mul hE
      rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel] at this
      exact this
    have hvc : ∀ t, v t = v 0 := fun t =>
      is_const_of_deriv_eq_zero (fun s => (hvd s).differentiableAt) (fun s => (hvd s).deriv) t 0
    have hv0 : v 0 = 1 := by simp [hv, h0]
    intro t
    have hcomm : Commute (t • (-Y)) (t • Y) :=
      ((Commute.refl Y).neg_left.smul_left t).smul_right t
    have hinv : NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ hcomm, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
    calc u t = u t * (NormedSpace.exp (t • (-Y)) * NormedSpace.exp (t • Y)) := by rw [hinv, Matrix.mul_one]
      _ = v t * NormedSpace.exp (t • Y) := by rw [hv, Matrix.mul_assoc]
      _ = NormedSpace.exp (t • Y) := by rw [hvc t, hv0, Matrix.one_mul]
  refine ⟨Y, ?_, hexp⟩

  show Yᴴ * G + G * Y = 0
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => star A
      map_add' := fun A B => star_add A B
      map_smul' := fun c A => by simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul] }
  have hst : HasDerivAt (fun t => star (u t)) (star Y) 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hY0
  have hw := (hst.mul_const G).mul hY0
  have hconst : ((fun t => star (u t) * G) * u) = fun _ => G := by
    funext t; exact hU t
  rw [hconst] at hw
  have := (hasDerivAt_const (0 : ℝ) G).unique hw
  rw [h0, star_one, Matrix.one_mul, Matrix.mul_one, ← Matrix.star_eq_conjTranspose] at *
  exact this.symm

end GlobalTheory.OneParamUnitary
