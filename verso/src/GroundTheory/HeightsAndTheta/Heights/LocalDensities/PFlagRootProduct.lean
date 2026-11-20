import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

/- English proof (translation)
Take `⟨⟨a, b⟩, hba⟩` from `q`. Establish `hba' : b.val < a.val` using `hba`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Unfold `rootPairing`.

Simplify using `only`. Distinguish the cases in `h : b.val < p ∧ p ≤ a.val`. Rewrite using `[if_pos h]`. Establish `hle : lam b ≤ lam a` using `hd a b (by`. Unfold `splitRank`.

Rewrite using `[if_pos h.2, if_neg (by omega)]`. Use the proof step `omega)`. Rewrite using `[abs_of_nonneg (by linarith)]`. Rewrite using `[if_neg h]`. Establish `hle : lam a ≤ lam b` using `hd b a (by`.

Unfold `splitRank`. Apply the tactic sequence `split_ifs <;> omega)`. Rewrite using `[abs_of_nonpos (by linarith)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FlagRootProduct.rootPairing_eq_abs {N p : ℕ} {lam : Fin N → ℝ}
    (hd : IsSplitDominant N p lam) (q : LowerPair N) :
    rootPairing N p lam q = |lam q.1.1 - lam q.1.2| := by
  obtain ⟨⟨a, b⟩, hba⟩ := q
  have hba' : b.val < a.val := hba
  have ha := a.isLt
  have hb := b.isLt
  unfold rootPairing
  dsimp only
  by_cases h : b.val < p ∧ p ≤ a.val
  · rw [if_pos h]
    have hle : lam b ≤ lam a := hd a b (by
      unfold splitRank
      rw [if_pos h.2, if_neg (by omega)]
      omega)
    rw [abs_of_nonneg (by linarith)]
  · rw [if_neg h]
    have hle : lam a ≤ lam b := hd b a (by
      unfold splitRank
      split_ifs <;> omega)
    rw [abs_of_nonpos (by linarith)]
    ring

/- English proof (translation)
Introduce `N p lam hd`. Establish `h` using `fun q => FlagRootProduct.rootPairing_eq_abs (N := N) (p := p) hd q`. Conclude with `⟨h, Finset.prod_congr rfl fun q _ => h q⟩`.
-/
theorem FlagRootProduct.proof : FlagRootProduct.Statement := by
  intro N p lam hd
  have h := fun q => FlagRootProduct.rootPairing_eq_abs (N := N) (p := p) hd q
  exact ⟨h, Finset.prod_congr rfl fun q _ => h q⟩

end GroundTheory.Heights₂.Heights.FourB
