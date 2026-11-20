import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerEis
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FAtkinLehnerEis.lean&line=139#L139)
-/
theorem _root_.GlobalTheory.T.exists_ne_zero_slz_qs_eis_eq_smul : ∀ (j N l : ℕ) (ω : DirichletCharacter ℂ l) (ν : DirichletCharacter ℂ N) (c₁ c₂ : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ j → 0 < N → l.Prime → ¬ l ∣ N → MF j (N * l) (fun d => ch ω d * ch ν d) (eis j c₁ (ch ω) (ch ν)) → MF j (N * l) (fun d => ch ω d * ch ν⁻¹ d) (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) → ∃ κ : ℂ, κ ≠ 0 ∧ slz j !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs (eis j c₁ (ch ω) (ch ν))) = κ • qs (eis j c₂ (fun x => ch ω x * hat ν x) fun _ => 1) := by
  first | exact @GlobalTheory.EisAL.atkin_lehner_eis | exact GlobalTheory.EisAL.atkin_lehner_eis | (intros; apply GlobalTheory.EisAL.atkin_lehner_eis <;> assumption)
