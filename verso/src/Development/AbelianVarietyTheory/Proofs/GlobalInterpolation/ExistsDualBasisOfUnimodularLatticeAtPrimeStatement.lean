import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDualBasisOfUnimodularLatticeAtPrime
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomDual.dual_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsDualBasisOfUnimodularLatticeAtPrime.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.exists_dualBasis_of_unimodular_lattice_at_prime : ∀ (q : ℕ) [Fact q.Prime] (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ), S.Ok → S.NNBasis q b → ∃ (s : ℕ) (c : Fin r → Fin g → ℂ), Nat.Coprime s q ∧ (∀ j, c j ∈ S.La) ∧ (∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s : ℂ) else 0) ∧ ∀ x ∈ S.La, (s : ℂ) • x = ∑ j, beta S.d S.Hm x (b j) • c j := by
  first | exact @GlobalTheory.MomDual.dual_basis | exact GlobalTheory.MomDual.dual_basis | (intros; apply GlobalTheory.MomDual.dual_basis <;> assumption)
