import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCoordTie
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FJoinCoordsCoordTie.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.join_coords_coordTie : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω), (∀ p : Cpt M.ξ, ∃ l, InChart M.ξ w l p) → CoordTie o M.ξ (joinCo (RingHom.id Ω) x w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts | exact GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.Retie.coordTie_join_of_charts <;> assumption)
