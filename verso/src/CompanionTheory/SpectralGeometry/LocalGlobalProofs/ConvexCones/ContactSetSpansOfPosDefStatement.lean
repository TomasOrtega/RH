import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ContactSetSpansOfPosDef
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact_of_posDef` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FConvexCones%2FContactSetSpansOfPosDef.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.contact_set_spans_of_pos_def : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (ι : Type) [Finite ι] (a : ι → X), HasRedCover bar X → Covers2 a → (∃ B₀ ∈ contact bar a, IsPosDef B₀) → IsSpanned bar (contact bar a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact_of_posDef | exact GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact_of_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.isSpanned_contact_of_posDef <;> assumption)
