import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PZeroLocusDimH
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped NNReal ENNReal

noncomputable section

/- English proof (translation)
Use extensionality with `z`. Both sides reduce to the same expression.
-/
theorem NullSmaller.zeroSetEuc_eq_preimage_equiv {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSetEuc J =
      (EuclideanSpace.equiv (Fin n) ℂ) ⁻¹' {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} := by
  ext z
  rfl

/- English proof (translation)
Generalize the expression as in `ringKrullDim R = a at h ⊢`. Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => exact bot_le`. Consider the case `coe a`. Proceed by induction on `a using ENat.recTopCoe with`.

Consider the case `top => exact absurd h (by simp)`. Consider the case `coe a`. Establish `h' : a < k + 1` using `by exact_mod_cast h`. Conclude with `Nat.lt_succ_iff.1 h'` after adjusting the coercions.
-/
theorem NullSmaller.ringKrullDim_le_of_lt_succ {R : Type*} [CommRing R] {k : ℕ}
    (h : ringKrullDim R < ((k + 1 : ℕ) : WithBot ℕ∞)) : ringKrullDim R ≤ (k : WithBot ℕ∞) := by
  generalize ringKrullDim R = a at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe a =>
      have h' : a < k + 1 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.1 h'

/- English proof (translation)
Introduce `n d J hJ`. Break down `Nat.eq_zero_or_pos d with rfl | hd` into its components or cases. Establish `htop : J = ⊤`. Assume the negation of the conclusion as `h`. Establish `: Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J)` using `Ideal.Quotient.nontrivial_iff.2 h`.

Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)`. Conclude with `absurd (h0.trans_lt hJ) (by simp)`. Establish `hempty : zeroSetEuc J = ∅`. Use extensionality with `z`. Simplify using `only [zeroSetEuc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]`.

Conclude with `⟨1, htop ▸ Submodule.mem_top, by simp⟩`. Rewrite using `[hempty, measure_empty]`. Take `⟨k, rfl⟩ : ∃ k, d = k + 1` from `⟨d - 1, by omega⟩`. Establish `hk` using `ZeroLocusDimH.proof n k J (NullSmaller.ringKrullDim_le_of_lt_succ hJ)`. Establish `hlt : dimH (zeroSetEuc J) < (((2 * (k + 1) : ℕ) : ℝ≥0) : ℝ≥0∞)`.

Rewrite using `[NullSmaller.zeroSetEuc_eq_preimage_equiv, ContinuousLinearEquiv.dimH_preimage]`. Use `hk.trans_lt ?_` and prove the remaining obligations. Establish `: 2 * k < 2 * (k + 1)` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `h0` using `hausdorffMeasure_of_dimH_lt hlt`.

Simplify using `using h0`.
-/
theorem NullSmaller.proof : NullSmaller.Statement := by
  intro n d J hJ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have htop : J = ⊤ := by
      by_contra h
      have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.2 h
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)
      exact absurd (h0.trans_lt hJ) (by simp)
    have hempty : zeroSetEuc J = ∅ := by
      ext z
      simp only [zeroSetEuc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨1, htop ▸ Submodule.mem_top, by simp⟩
    rw [hempty, measure_empty]
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have hk := ZeroLocusDimH.proof n k J (NullSmaller.ringKrullDim_le_of_lt_succ hJ)
    have hlt : dimH (zeroSetEuc J) < (((2 * (k + 1) : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      rw [NullSmaller.zeroSetEuc_eq_preimage_equiv, ContinuousLinearEquiv.dimH_preimage]
      refine hk.trans_lt ?_
      have : 2 * k < 2 * (k + 1) := by omega
      exact_mod_cast this
    have h0 := hausdorffMeasure_of_dimH_lt hlt
    simpa using h0

end

end GroundTheory.Heights₂.Heights
