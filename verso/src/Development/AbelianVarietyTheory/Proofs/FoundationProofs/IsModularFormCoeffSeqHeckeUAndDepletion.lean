import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUOperatorLowersLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormCoeffSeqLinearStructureStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
theorem dep_eq_sub (l : ℕ) (a : ℕ → ℂ) : dep l a = a + (-1 : ℂ) • Vo l (Uo l a) := by
  funext n
  simp only [dep, Vo, Uo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rw [Nat.mul_div_cancel' h]; ring
  · ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem depletion_mf : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L → (∀ d, χ (d + L) = χ d) → MF k L χ a → MF k L χ (Uo l a) ∧ MF k (L * l) χ (dep l a) := by
  intro k L l χ a hk hl hlL hχ ha
  have haL : MF k (L * l) χ a := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k L χ).2.2.2.2.1 (L * l) a (dvd_mul_right L l) ha)
  have hU : MF k L χ (Uo l a) := GlobalTheory.T.coeffHeckeUOperator_lowers_level k L l χ a hk hl hlL hχ haL
  refine ⟨hU, ?_⟩
  have hV : MF k (L * l) χ (Vo l (Uo l a)) := (GlobalTheory.T.coeffHeckeVOperator_raises_level k L l χ (Uo l a) hl.pos).1 hU
  have hV' := ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (L * l) χ).2.2.1 (-1 : ℂ) _ hV).1
  rw [dep_eq_sub]
  exact ((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (L * l) χ).2.1 _ _ haL hV').1

end GlobalTheory
