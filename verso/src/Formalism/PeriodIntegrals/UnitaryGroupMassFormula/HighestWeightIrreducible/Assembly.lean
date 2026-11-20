import Formalism.PeriodIntegrals.HwIrred
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ClosedEqNablaC

noncomputable section

namespace PI.WHw

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem natW_antitone {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold Formalism.BasicNotions.DomWeight.natW
  exact Int.toNat_le_toNat (by linarith [lam.anti hij])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Prove the first alternative. Prove the second alternative.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem hwIrred_of (hA1 : StableClosedC) (hA2 : FixedKilledC) (hB1 : HWInClosedC)
    (hB2 : ClosedEqNablaC) : PI.HwIrred := by
  intro N lam
  have hν := natW_antitone lam
  have hsub : delSq ℂ N lam ≤ nablaSq ℂ N lam := weylLeDual ℂ N N le_rfl lam.natW hν
  have hclosed : RowDivClosed (delSq ℂ N lam) := fun a b k f hf =>
    weylRowDivStable ℂ N N le_rfl lam.natW a b k f hf
  have hhw : extremal ℂ N lam ∈ delSq ℂ N lam :=
    Submodule.subset_span ⟨[], rfl⟩
  refine ⟨(hB2 N N le_rfl lam.natW hν _ hsub hclosed hhw).symm, ?_, ?_⟩
  · intro U hU hst
    by_cases h0 : U = ⊥
    · exact Or.inl h0
    · exact Or.inr (hB2 N N le_rfl lam.natW hν U hU (hA1 N lam U hU hst)
        (hB1 N N le_rfl lam.natW hν U hU (hA1 N lam U hU hst) h0))
  · intro f hf hfix
    exact hwLine ℂ N N le_rfl lam.natW hν f hf (hA2 N lam f hf hfix)

end PI.WHw
