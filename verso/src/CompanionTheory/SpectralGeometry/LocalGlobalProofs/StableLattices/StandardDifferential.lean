import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.ZuckStdD

/- English proof (translation)
Use extensionality with `c d`. Apply the tactic sequence `exact (PI.ComplexConjugateDerivative.exp_entry X c d).deriv`.
-/
theorem dR_std (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (vr k r false).dR X = X := by
  ext c d
  exact (PI.ComplexConjugateDerivative.exp_entry X c d).deriv

/- English proof (translation)
Use extensionality with `c d`. Apply the tactic sequence `have h := (PI.ComplexConjugateDerivative.exp_entry (-X) d c).deriv`. Establish `e : (fun t : ℝ => (vr k r true).ρ (NormedSpace.exp ((t : ℂ) • X)) c d) = fun t : ℝ => (NormedSpace.exp ((t : ℂ) • (-X))) d c`. Use function extensionality and compare the values at `t`. Rewrite using `[smul_neg, Matrix.exp_neg]`.

Simplify using `[dualM]`. Use `show deriv (fun t : ℝ => (vr k r true).ρ (NormedSpace.exp ((t : ℂ) • X)) c d) 0 = _`. Rewrite using `[e, h]`. Both sides reduce to the same expression.
-/
theorem dR_dual (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (vr k r true).dR X = -Xᵀ := by
  ext c d
  have h := (PI.ComplexConjugateDerivative.exp_entry (-X) d c).deriv
  have e : (fun t : ℝ => (vr k r true).ρ (NormedSpace.exp ((t : ℂ) • X)) c d) =
      fun t : ℝ => (NormedSpace.exp ((t : ℂ) • (-X))) d c := by
    funext t
    rw [smul_neg, Matrix.exp_neg]
    simp [dualM]
  show deriv (fun t : ℝ => (vr k r true).ρ (NormedSpace.exp ((t : ℂ) • X)) c d) 0 = _
  rw [e, h]
  rfl

/- English proof (translation)
Unfold `reH imH`. Establish `hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2`. Use `Complex.I_ne_zero` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite using `[smul_smul, hI, ← smul_add]`.

Establish `: ∀ Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Y + Z + (Y - Z) = (2 : ℂ) • Y`. Introduce `Z`. Rewrite using `[two_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[this, smul_smul]`.

Evaluate the numerical expressions.
-/
theorem reH_add_imH (k r : ℕ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    reH k r Y + Complex.I • imH k r Y = Y := by
  unfold reH imH
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    have := Complex.I_ne_zero
    field_simp
  rw [smul_smul, hI, ← smul_add]
  have : ∀ Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Y + Z + (Y - Z) = (2 : ℂ) • Y := by
    intro Z; rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num

/- English proof (translation)
Introduce `k r Y`. Prove the components needed by the constructor for the conclusion. Unfold `FRep.dC`. Rewrite using `[dR_std, dR_std]`. Conclude with `reH_add_imH k r Y`.

Unfold `FRep.dC`. Rewrite using `[dR_dual, dR_dual]`. Use `conv_rhs => rw [← reH_add_imH k r Y]`. Rewrite using `[Matrix.transpose_add, Matrix.transpose_smul, neg_add, smul_neg]`.
-/
theorem stdD : StdD := by
  intro k r Y
  constructor
  · unfold FRep.dC
    rw [dR_std, dR_std]
    exact reH_add_imH k r Y
  · unfold FRep.dC
    rw [dR_dual, dR_dual]
    conv_rhs => rw [← reH_add_imH k r Y]
    rw [Matrix.transpose_add, Matrix.transpose_smul, neg_add, smul_neg]

end GlobalTheory.CompanionTheory.ZuckStdD
