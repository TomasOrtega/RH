import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqEisensteinProductParity
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsModularFormCoeffSeqEisensteinProductParity.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.isModularFormCoeffSeq_eisensteinProduct_parity : ∀ (k N l m : ℕ) (ε θ ν : DirichletCharacter ℂ N) (f : ZMod (l ^ m) → ℂ), 3 ≤ k → Odd k → 0 < N → l.Prime → 1 ≤ m → ¬ l ∣ N → ε = θ⁻¹ * ν → ν (-1) = -θ (-1) → (∀ x, f (-x) = θ (-1) * f x) → MF k (N * l ^ (m + 1)) (ch ε) (Zm k l (hat θ) (ch ν) (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹))) := by
  first | exact @GlobalTheory.EisM.zm_fun_mf | exact GlobalTheory.EisM.zm_fun_mf | (intros; apply GlobalTheory.EisM.zm_fun_mf <;> assumption)
