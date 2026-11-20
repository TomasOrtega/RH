import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticSurfaceFibreIsProjOverZmodDimLeOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithmeticSurfaceFibreIsProjOverZmodDimLeOne.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.arithmeticSurface_fibre_isProjOver_zmod_dim_le_one : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  first | exact @GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le | exact GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le | (intros; apply GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le <;> assumption)
