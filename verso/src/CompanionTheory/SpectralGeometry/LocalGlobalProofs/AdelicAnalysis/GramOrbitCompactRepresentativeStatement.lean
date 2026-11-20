import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramOrbitCompactRepresentative
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FGramOrbitCompactRepresentative.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.gram_orbit_compact_representative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (X : Fin n → Fin M → E), (gramE σ J X).det ≠ 0 → ∀ Ω : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact Ω → ∃ C : Set (HA (AF F) σ J), IsCompact C ∧ ∀ Y ∈ Ω, gramR (AF F) σ J Y = (gramE σ J X).map (inclR (AF F)) → ∃ c ∈ C, actW (AF F) σ J c (ratTup (AF F) X) = Y := by
  first | exact @GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre | exact GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre | (intros; apply GlobalTheory.CompanionTheory.SW.Proper.compact_gram_fibre <;> assumption)
