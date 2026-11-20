import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleMemOfMem
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_of_components : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S]
    [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N,
    (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F := by
  intro C _ w S _ _ a N F ha hF x hx hc
  have hle : ∀ s, filSpace F s ≤ clearDen F s := fun s => by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨diffGen a s, diffGen_ne_zero a ha s, single_mem_of_mem a F hF.stable s y hy⟩
  choose b hb hbx using fun s => hle s (hc s)
  have hB : (∏ s, b s) ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => hb s
  refine hF.saturated x hx (∏ s, b s) hB ?_
  have key : (∏ s, b s) • x = ∑ s, (∏ t ∈ Finset.univ.erase s, b t) •
      (Pi.single s (b s • x s) : S → Fin N → C) := by
    funext s' i
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single s']
    · simp only [smul_pi_apply, Pi.single_eq_same, smul_vec_apply]
      rw [← mul_assoc, ← Subring.coe_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ s')]
    · intro s _ e
      simp [smul_pi_apply, Pi.single_apply, Ne.symm e]
    · simp
  rw [key]
  exact sum_mem fun s _ => F.smul_mem _ (hbx s)

end GlobalTheory.Div.KerFil
