import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Comb

noncomputable section

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem symmetricGroupCharacter_eq_cf {m : ℕ} (lam : Fin m → ℕ) (rho : List ℕ) :
    symmetricGroupCharacter lam rho =
      cf (fun i => lam i + stair m i) (alternantPsum m rho) := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem CharacterAtIdentity.proof (h1 : CombTableEqWords.Statement)
    (h2 : CombCfAtStair.Statement) : CharacterAtIdentity.Statement := by
  intro m lam hlam
  rw [symmetricGroupCharacter_eq_cf, h2 m (∑ i, lam i) lam hlam, h1 m lam hlam]

end

end GroundTheory.Heights₂.Heights.RestTerms
