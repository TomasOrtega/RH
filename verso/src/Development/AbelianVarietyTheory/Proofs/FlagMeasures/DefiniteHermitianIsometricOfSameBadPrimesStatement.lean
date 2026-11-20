import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteHermitianIsometricOfSameBadPrimes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FDefiniteHermitianIsometricOfSameBadPrimes.lean&line=352#L352)
-/
theorem _root_.GlobalTheory.T.definite_hermitian_isometric_of_same_bad_primes : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (k : W →ₗ⋆[K] W →ₗ[K] K), k.IsSymm → PD k → (∃ L : Submodule (𝓞 K) W, Submodule.IsLattice K L ∧ IsUnimodular k L) → ∃ I : Submodule (𝓞 K) W, IsOrthoLattice k I (Module.finrank K W)) → ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h' : V' →ₗ⋆[K] V' →ₗ[K] K), h'.IsSymm → PD h' → Module.finrank K V = Module.finrank K V' → ∀ (M : Submodule (𝓞 K) V) (M' : Submodule (𝓞 K) V'), IsMaxLat h M → IsMaxLat h' M' → badP h M = badP h' M' → ∃ e : V ≃ₗ[K] V', ∀ x y, h' (e x) (e y) = h x y := by
  first | exact @GlobalTheory.Mass.SameBad.main | exact GlobalTheory.Mass.SameBad.main | (intros; apply GlobalTheory.Mass.SameBad.main <;> assumption)
