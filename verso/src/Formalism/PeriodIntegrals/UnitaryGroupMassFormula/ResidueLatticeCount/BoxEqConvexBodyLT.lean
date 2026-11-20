import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace PI.Residue

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem box_eq_convexBodyLT (K : Type) [Field K] [NumberField K] (r : InfinitePlace K → ℝ)
    (hr : ∀ w, 0 < r w) : box K r = convexBodyLT K (fun w => (r w).toNNReal) := by
  ext y
  simp only [box, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_ball_zero_iff, Subtype.forall, Real.coe_toNNReal _ (hr _).le]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · simpa [normAtPlace_apply_of_isReal hw] using h w
    · simpa [normAtPlace_apply_of_isComplex hw] using h w
  · rintro ⟨h1, h2⟩ w
    rcases isReal_or_isComplex w with hw | hw
    · rw [normAtPlace_apply_of_isReal hw]; exact h1 w hw
    · rw [normAtPlace_apply_of_isComplex hw]; exact h2 w hw

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem boxVolume : BoxVolume := by
  intro K _ _ r hr
  rw [box_eq_convexBodyLT K r hr, convexBodyLT_volume, vfac]
  congr 1
  rw [ENNReal.ofReal_prod_of_nonneg (fun w _ => (pow_pos (hr w) _).le)]
  push_cast
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [ENNReal.ofReal_pow (hr w).le]
  rfl

end PI.Residue
