import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLogDerivQExpansionModPrimePowOfTranslation
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.dl_exists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsLogDerivQExpansionModPrimePowOfTranslation.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.exists_logDerivQExpansion_modPrimePow_of_translationInvariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (f : X.K), 0 < L → f ≠ 0 → f ∈ KT X L → ∃ φ : HahnSeries ℚ Ω, IsDl X A l n L f φ ∧ ∀ r : ℚ, φ.coeff r ≠ 0 → (r * L).den = 1 := by
  first | exact @GlobalTheory.dl_exists | exact GlobalTheory.dl_exists | (intros; apply GlobalTheory.dl_exists <;> assumption)
