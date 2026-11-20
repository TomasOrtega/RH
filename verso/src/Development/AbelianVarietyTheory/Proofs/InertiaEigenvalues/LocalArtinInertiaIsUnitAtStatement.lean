import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroTypeInertia
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArtinInertia.isUnitAt_artin_ine` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLocalArtinInertiaIsUnitAt.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.localArtin_inertia_isUnitAt : ∀ {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha : IsLocalArtin h' a') (t : Ine (F := E') A),
    IsUnitAt w' (a' (ineIncl h' t)) := by
  first | exact @GlobalTheory.ArtinInertia.isUnitAt_artin_ine | exact GlobalTheory.ArtinInertia.isUnitAt_artin_ine | (intros; apply GlobalTheory.ArtinInertia.isUnitAt_artin_ine <;> assumption)
