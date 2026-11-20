import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationLiftProjectionComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomOfSecSecPowAppChartSec
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM)
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GrFilt.liftT_comp_proj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiltrationLiftProjectionComp.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.filtration_lift_projection_comp : ∀ {X : Scheme.{0}} [IsIntegral X] {ι : Type} [Fintype ι] {L : X.Modules} {E E' : ι → X.Modules} {r : ι → ℕ}
    (o : ι → ℕ), Function.Injective o → ∀ (T : ∀ a, E a ⟶ L) (u : ∀ a, E a ⟶ E' a),
    (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ LocAdapted r o T u V) → FrameMem r o T u →
    ∀ (b : ι) (κ : (filtSub o T (o b + 1)).toMod ⟶ E' b), IsProj r o T u b κ → liftT o T b ≫ κ = u b := by
  first | exact @GlobalTheory.GrFilt.liftT_comp_proj | exact GlobalTheory.GrFilt.liftT_comp_proj | (intros; apply GlobalTheory.GrFilt.liftT_comp_proj <;> assumption)
