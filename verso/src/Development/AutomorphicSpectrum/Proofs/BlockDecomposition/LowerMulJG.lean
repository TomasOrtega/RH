import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLowG

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.BigCell

open PositivityTheory.Rg.Sw

variable {n : ℕ}

/- English proof (translation)
Establish `hc : (JJ n)ᴴ = -JJ n`. Unfold `JJ`. Simplify using `[Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]`. Use `show (JJ n)ᴴ * JJ n * JJ n = JJ n`. Rewrite using `[hc, Matrix.mul_assoc, JJ_mul_JJ]`.

Simplify using the standard rewrite rules.
-/
theorem JJ_inG : InG (JJ n) := by
  have hc : (JJ n)ᴴ = -JJ n := by
    unfold JJ
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
  show (JJ n)ᴴ * JJ n * JJ n = JJ n
  rw [hc, Matrix.mul_assoc, JJ_mul_JJ]
  simp

def JG : GR n :=
  ⟨⟨JJ n, -JJ n, by simp [JJ_mul_JJ], by simp [JJ_mul_JJ]⟩, JJ_inG⟩

/- English proof (translation)
Establish `h : mR (y * JG) = mR y * JJ n` using `rfl`. Rewrite using `[h, ← Matrix.fromBlocks_toBlocks (mR y)]`. Unfold `JJ`. Rewrite using `[Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]`. Simplify using the standard rewrite rules.
-/
theorem lower_mul_JG (y : GR n) :
    (mR (y * JG)).toBlocks₂₁ = -(mR y).toBlocks₂₂ := by
  have h : mR (y * JG) = mR y * JJ n := rfl
  rw [h, ← Matrix.fromBlocks_toBlocks (mR y)]
  unfold JJ
  rw [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  simp

/- English proof (translation)
Introduce `n`. Establish `hset : {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} = (fun y => y * (JG (n` using `n))) ⁻¹' {y : GR n | ((mR y).toBlocks₂₁).det ≠ 0} := by`. Use extensionality with `y`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_preimage, lower_mul_JG, Matrix.det_neg]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `mul_ne_zero (pow_ne_zero _ (by norm_num)) h`. Introduce `h h0`. Conclude with `h (by rw [h0, mul_zero])`. Rewrite using `[hset]`.

Conclude with `(dense_bigCell n).preimage (isOpenMap_mul_right _)`.
-/
theorem dense_bigCell₂₂ : ∀ n : ℕ, Dense {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} := by
  intro n
  have hset : {y : GR n | ((mR y).toBlocks₂₂).det ≠ 0} =
      (fun y => y * (JG (n := n))) ⁻¹' {y : GR n | ((mR y).toBlocks₂₁).det ≠ 0} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, lower_mul_JG, Matrix.det_neg]
    constructor
    · intro h
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h
    · intro h h0
      exact h (by rw [h0, mul_zero])
  rw [hset]
  exact (dense_bigCell n).preimage (isOpenMap_mul_right _)

end GlobalTheory.CompanionTheory.BigCell
