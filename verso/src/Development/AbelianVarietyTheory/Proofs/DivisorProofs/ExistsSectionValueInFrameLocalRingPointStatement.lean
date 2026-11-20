import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionValueInFrameLocalRingPoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeatV.exists_isValue` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSectionValueInFrameLocalRingPoint.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_sectionValue_in_frame_localRing_point : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsLocalRing Ω] (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)), g.IsGen → ∀ (k : ℕ) (σ : SecM (𝟙 X) L k), ∃ ω : Ω, IsValue (𝟙 _) L x g k σ ω := by
  first | exact @GlobalTheory.HeatV.exists_isValue | exact GlobalTheory.HeatV.exists_isValue | (intros; apply GlobalTheory.HeatV.exists_isValue <;> assumption)
