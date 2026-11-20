import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianTensorOverScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SemiProd.isSemiAbelian_tensor` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSemiAbelianTensorOverScheme.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.isSemiAbelian_tensor_over_scheme : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [GrpObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsSemiAbelian (G₁ ⊗ G₂) := by
  first | exact @GlobalTheory.SemiProd.isSemiAbelian_tensor | exact GlobalTheory.SemiProd.isSemiAbelian_tensor | (intros; apply GlobalTheory.SemiProd.isSemiAbelian_tensor <;> assumption)
