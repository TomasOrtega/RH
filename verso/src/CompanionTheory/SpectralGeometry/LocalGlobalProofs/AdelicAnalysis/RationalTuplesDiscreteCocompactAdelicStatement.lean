import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalTuplesDiscreteCocompactAdelic
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FRationalTuplesDiscreteCocompactAdelic.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.rational_tuples_discrete_cocompact_adelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M : ℕ), (∃ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C ∧ ∀ y, ∃ X : Fin n → Fin M → E, y - ratTup (AF F) X ∈ C) ∧ (∀ C : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact C → {X : Fin n → Fin M → E | ratTup (AF F) X ∈ C}.Finite) ∧ (0 < n → 0 < M → NoncompactSpace (Fin n → Fin M → AF F ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.CocW.main | exact GlobalTheory.CompanionTheory.SW.CocW.main | (intros; apply GlobalTheory.CompanionTheory.SW.CocW.main <;> assumption)
