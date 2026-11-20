import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCohomologyLocalGlobalDual
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGaloisCohomologyLocalGlobalDual.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.finite_local_cohomology_at_places_of_localFiniteness : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, Finite (H0 (ρ.comp (locFam S Av v))) ∧ Finite (H1 (ρ.comp (locFam S Av v))) ∧ Finite (H2 (ρ.comp (locFam S Av v))) := by
  first | exact @GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places | exact GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places | (intros; apply GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places <;> assumption)
