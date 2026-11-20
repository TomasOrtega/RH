import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem flagIntegral_sum_smul_blockPermute (f N : ℕ) (H : RootRing f N)
    (s : Finset (Fin f → Equiv.Perm (Fin N))) :
    flagIntegral f N (∑ w ∈ s, blockSign f N w • blockPermute f N w H) =
      ∑ w ∈ s, blockSign f N w * flagIntegral f N (blockPermute f N w H) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Flag.flagIntegral_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Flag.flagIntegral_add, ih, smul_eq_C_mul,
      Flag.flagIntegral_C_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FlagIntegralAntisymmetrize.proof (h1 : FlagIntegralPermute.Statement) :
    FlagIntegralAntisymmetrize.Statement := by
  intro f N H
  rw [antisymmetrize, flagIntegral_sum_smul_blockPermute]
  rw [Finset.sum_congr rfl fun w _ => by
    rw [h1 f N w H, ← mul_assoc, Flag.blockSign_mul_self, one_mul]]
  rw [Finset.sum_const, Finset.card_univ, Flag.card_blockPerm, nsmul_eq_mul]
  push_cast
  ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
