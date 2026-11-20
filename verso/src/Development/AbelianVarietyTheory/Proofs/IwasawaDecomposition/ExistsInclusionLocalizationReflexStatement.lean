import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInclusionLocalizationReflex
import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsInclusionLocalizationReflex.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_inclusion_localization_reflex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (a : ℕ), 0 < a → ∀ (ω : Localization.Away (a : 𝓞 c.F) →+* c.F), ω.comp (algebraMap (𝓞 c.F) (Localization.Away (a : 𝓞 c.F))) = algebraMap (𝓞 c.F) c.F → ∃ bR : RZ H a 1 →+* Localization.Away (a : 𝓞 c.F), IsInc (RZ H a 1).subtype (c.F.val.toRingHom.comp ω) bR := by
  first | exact @GlobalTheory.CoeffAway.exists_isInc_away | exact GlobalTheory.CoeffAway.exists_isInc_away | (intros; apply GlobalTheory.CoeffAway.exists_isInc_away <;> assumption)
