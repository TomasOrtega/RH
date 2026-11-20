import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsConnectedZeroSetOfIsProper
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIsConnectedZeroSetOfIsProper.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isConnected_zeroSet_uniformizer : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ConstClosed O Ω → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper | exact GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper <;> assumption)
