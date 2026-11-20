import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberLevelPrimeNotMemUnderLevelPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormOneFiniteAdeleDetClassOfIsDetLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mem.LevTwist.T_notMem_under_uSG` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FMemberLevelPrimeNotMemUnderLevelPrimes.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.memberLevelPrime_not_mem_under_levelPrimes : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → ∀ (u : B.Word) (P : HeightOneSpectrum (𝓞 B.host.E)), P ∈ uSG (B.primes X).vGs I.SQ → (B.T u : 𝓞 B.host.F) ∉ (P.under (𝓞 B.host.F)).asIdeal := by
  first | exact @GlobalTheory.Mem.LevTwist.T_notMem_under_uSG | exact GlobalTheory.Mem.LevTwist.T_notMem_under_uSG | (intros; apply GlobalTheory.Mem.LevTwist.T_notMem_under_uSG <;> assumption)
