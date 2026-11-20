import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LineNorm.Add.fromModel_add` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FFromModelAdd.lean&line=114#L114)
-/
theorem _root_.GlobalTheory.T.fromModel_add' : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ Δ' : Y.Dv) (t t' : Y.X → Y.Fnˣ) (φ φ' : PtFn Y), (∀ y, Δ.IsEqn y (t y)) → (∀ y, Δ'.IsEqn y (t' y)) → FromModel Y Δ t φ → FromModel Y Δ' t' φ' → FromModel Y (Δ + Δ') (fun y => t y * t' y) (fun v e y => φ v e y + φ' v e y) := by
  first | exact @GlobalTheory.LineNorm.Add.fromModel_add | exact GlobalTheory.LineNorm.Add.fromModel_add | (intros; apply GlobalTheory.LineNorm.Add.fromModel_add <;> assumption)
