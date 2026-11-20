import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHom
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsInjectiveCuspExpansionRingHom.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.exists_injective_cuspExpansion_ringHom : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ e : GlobalTheory.FN.ring ε.range →+* HahnSeries ℚ Ω, Function.Injective e ∧ ∀ a : GlobalTheory.FN.ring ε.range, IsExp ε a (e a) := by
  first | exact @GlobalTheory.FN.expansion_injective_ringHom | exact GlobalTheory.FN.expansion_injective_ringHom | (intros; apply GlobalTheory.FN.expansion_injective_ringHom <;> assumption)
