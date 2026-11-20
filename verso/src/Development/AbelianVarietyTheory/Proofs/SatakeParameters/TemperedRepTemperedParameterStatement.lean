import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocLanglands.tempered_of_isTemperedGL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTemperedRepTemperedParameter.lean&line=125#L125)
-/
theorem _root_.GlobalTheory.T.tempered_rep_tempered_parameter : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ (n : ℕ) (σ : IrrRep (GL (Fin n) (w.adicCompletion E))), GlobalTheory.LocGL.IsTemperedGL σ.ρ → (rc (cls σ)).tempered := by
  first | exact @GlobalTheory.LocLanglands.tempered_of_isTemperedGL | exact GlobalTheory.LocLanglands.tempered_of_isTemperedGL | (intros; apply GlobalTheory.LocLanglands.tempered_of_isTemperedGL <;> assumption)
