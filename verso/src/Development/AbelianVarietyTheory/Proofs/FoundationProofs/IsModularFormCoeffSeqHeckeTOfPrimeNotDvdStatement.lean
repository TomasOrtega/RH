import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeTOfPrimeNotDvd
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsModularFormCoeffSeqHeckeTOfPrimeNotDvd.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd : ∀ (k L N q : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → N ∣ L → q.Prime → ¬ q ∣ L → MF k L (ch ε) a → MF k L (ch ε) (To k (ch ε q) q a) := by
  first | exact @GlobalTheory.EisM.To_MF | exact GlobalTheory.EisM.To_MF | (intros; apply GlobalTheory.EisM.To_MF <;> assumption)
