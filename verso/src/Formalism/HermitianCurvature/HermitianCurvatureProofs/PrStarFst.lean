import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd

section Act

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_add_fst (p q : Q.Pr V) : (p + q).1 = p.1 + q.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_mul_fst (p q : Q.Pr V) : (p * q).1 = p.1 * q.1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_zero_fst : (0 : Q.Pr V).1 = 0 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pr_one_fst : (1 : Q.Pr V).1 = 1 := rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem pr_sum_fst {ι : Type*} (s : Finset ι) (f : ι → Q.Pr V) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, pr_zero_fst]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add_fst, ih]

def actP (M : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : Ix S → V := fun a => ∑ b, (M a b).1 (X b)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem polyAction_mul (M N : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : actP (M * N) X = actP M (actP N X) := by
  funext a
  unfold actP
  simp only [Matrix.mul_apply, pr_sum_fst, pr_mul_fst, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  exact Finset.sum_comm

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem polyAction_one₂ (X : Ix S → V) : actP (1 : SlopeTestRemainingChoices S (Q.Pr V)) X = X := by
  funext a
  unfold actP
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, pr_one_fst]
    rfl
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), pr_zero_fst]
    rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem blockMulVec_add (M : SlopeTestRemainingChoices S (Q.Pr V)) (X Y : Ix S → V) : actP M (X + Y) = actP M X + actP M Y := by
  funext a
  simp only [actP, Pi.add_apply, map_add, Finset.sum_add_distrib]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem actP_smul (M : SlopeTestRemainingChoices S (Q.Pr V)) (c : ℂ) (X : Ix S → V) : actP M (c • X) = c • actP M X := by
  funext a
  simp only [actP, Pi.smul_apply, map_smul, Finset.smul_sum]

end Act

end Formalism.FourierDecayAlt.P.PBF
