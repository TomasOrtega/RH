import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

namespace GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve

section RingNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/- English proof (translation)
The claim follows from `continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y t).continuousAt`.
-/
theorem continuous_exp_smul {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp (t • Y)) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y t).continuousAt

/- English proof (translation)
Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)`. Rewrite `h` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Conclude with `h`.
-/
theorem hasDerivAt_exp_smul_zero {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Y)) Y 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

end RingNorm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hc : (t • Y)ᴴ = -(t • Y)`. Rewrite using `[conjTranspose_smul, hY]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hc, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Y)).neg_right]`. Simplify using the standard rewrite rules.
-/
theorem exp_smul_mem_unitaryGroup {n : ℕ} (Y : Mat n) (hY : Yᴴ = -Y) (t : ℝ) :
    NormedSpace.exp (t • Y) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hc : (t • Y)ᴴ = -(t • Y) := by
    rw [conjTranspose_smul, hY]; simp
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Y)).neg_right]
  simp

/- English proof (translation)
Introduce `n Y hY`. Use `⟨fun t => ⟨NormedSpace.exp (t • Y), exp_smul_mem_unitaryGroup Y hY t⟩, (continuous_exp_smul Y).subtype_mk _, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Introduce `s t`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y)`. Rewrite using `[add_smul]`. Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left s).smul_right t)`. Conclude with `hasDerivAt_exp_smul_zero Y`.
-/
theorem exists_unitary_curve : ∀ {n : ℕ} (Y : Mat n), Yᴴ = -Y →
    ∃ c : ℝ → Matrix.unitaryGroup (Fin n) ℂ, Continuous c ∧ c 0 = 1 ∧
      (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => (c t).1) Y 0 := by
  intro n Y hY
  refine ⟨fun t => ⟨NormedSpace.exp (t • Y), exp_smul_mem_unitaryGroup Y hY t⟩,
    (continuous_exp_smul Y).subtype_mk _, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp
  · intro s t
    apply Subtype.ext
    show NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y)
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _
      (((Commute.refl Y).smul_left s).smul_right t)
  · exact hasDerivAt_exp_smul_zero Y

end GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve
