import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPointValueCocycle
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTransitionUnitPointValueCocycle.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.transitionUnit_pointValue_cocycle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X) (j j' j'' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → ⊤ ≤ ξ ⁻¹ᵁ L.U j'' → valR ξ (L.U j ⊓ L.U j') (L.g j j').val * valR ξ (L.U j' ⊓ L.U j'') (L.g j' j'').val = valR ξ (L.U j ⊓ L.U j'') (L.g j j'').val := by
  first | exact @GlobalTheory.CocVal.valR_cocycle | exact GlobalTheory.CocVal.valR_cocycle | (intros; apply GlobalTheory.CocVal.valR_cocycle <;> assumption)
