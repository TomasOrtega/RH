import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RingIsomorphismTransportsPlaces
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NineTermExactIff
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FRingIsomorphismTransportsPlaces.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.ring_isomorphism_transports_places : ∀ (F F' : Type) [Field F] [NumberField F] [Field F'] [NumberField F'] (e : F ≃+* F'), ∃ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) ∧ ∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v := by
  first | exact @GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv | exact GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.PTIso.Places.exists_places_of_ringEquiv <;> assumption)
