import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGeneratorInvertConstant
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FLatticeGeneratorInvertConstant.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.lattice_generator_invert_constant : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [LocallyOfFiniteType s] [QuasiCompact s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (n₀ : O) (t : Ω), n₀ ≠ 0 → (∀ p, unitAt ξ p (algebraMap O Ω n₀) → p ∈ T) → L.IsVBOn T 1 ⊤ → (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∃ n : O, n ≠ 0 ∧ ∀ p, unitAt ξ p (algebraMap O Ω n) → L.IsGenAt p t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread | exact GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread <;> assumption)
