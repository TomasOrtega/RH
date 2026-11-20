import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PZeroLocusDimH
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped NNReal ENNReal

noncomputable section

/- English proof (translation)
By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
theorem NullSmaller.zeroSetEuc_eq_preimage_equiv {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSetEuc J =
      (EuclideanSpace.equiv (Fin n) ℂ) ⁻¹' {x : Fin n → ℂ | ∀ q ∈ J, eval x q = 0} := by
  ext z
  rfl

/- English proof (translation)
Replace the chosen expression with an arbitrary variable. Proceed by induction. Treat this case separately. Treat this case separately. Proceed by induction.

Treat this case separately. Treat this case separately. Establish an intermediate fact. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Supply the required witnesses or components.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
