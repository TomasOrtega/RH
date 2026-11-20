import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.KhwLowKSubRootEqZero

noncomputable section

open Finset

namespace PositivityTheory.RgHe3.DropRoots

open ReciprocityTheory.ChartRestriction.DS

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem abs_rhoC_le {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ (n : ℝ) / 2 := by
  unfold rhoC
  have h1 : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) ≤ n := by
    exact_mod_cast (card_filter_le _ _).trans (by simp)
  have h2 : ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) ≤ n := by
    exact_mod_cast (card_filter_le _ _).trans (by simp)
  have h3 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem dot_root {n : ℕ} (x : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) : dot x (root a b) = x a - x b := by
  simp [dot, root, Pi.single_apply, mul_sub, Finset.sum_sub_distrib]

end PositivityTheory.RgHe3.DropRoots

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgHe3.DropRoots

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem drop_holds : Drop := by
  intro n ε L a b hab
  unfold casValK
  have e : L - root a b + rhoC ε = (L + rhoC ε) - root a b := by
    funext c; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [e, nsq_sub', nsq_root hab, dot_root _ hab]
  have h1 := abs_rhoC_le ε a
  have h2 := abs_rhoC_le ε b
  simp only [Pi.add_apply]
  rw [abs_le] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

end PositivityTheory.RgHe3
