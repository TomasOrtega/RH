import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicValNatMulLogLeLog
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier AlgebraicGeometry CategoryTheory

namespace GlobalTheory.PlaceBd

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem sum_vDiff_mul_log_le_log_rdE :
    ∀ (D : D7) (T : Finset ℕ), (∀ p ∈ T, p.Prime) →
    ∑ p ∈ T, vDiff D.host.E p * Real.log p ≤ Real.log D.host.rdE := by
  intro D T hT
  have hn : (0 : ℝ) < (Module.finrank ℚ D.host.E : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < |(discr D.host.E : ℝ)| := by
    rw [abs_pos]; exact_mod_cast discr_ne_zero D.host.E
  have hc : (((discr D.host.E).natAbs : ℕ) : ℝ) = |(discr D.host.E : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hr : Real.log D.host.rdE =
      Real.log ((discr D.host.E).natAbs : ℕ) / (Module.finrank ℚ D.host.E : ℝ) := by
    rw [hc]
    unfold Host.rdE
    rw [Real.log_rpow hd]; ring
  rw [hr]
  refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right
    (GlobalTheory.MeanTop.sum_padicValNat_mul_log_le_log (discr D.host.E).natAbs T hT) hn.le)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [vDiff]; ring

end GlobalTheory.PlaceBd
