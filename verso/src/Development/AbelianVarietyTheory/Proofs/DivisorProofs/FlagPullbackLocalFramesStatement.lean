import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPullbackLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagQ.exists_isFrame` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagPullbackLocalFrames.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.flag_pullback_local_frames : ∀ (ι : Type) [Fintype ι] (N : ℕ) (Y : GlobalTheory.ProjVar.Var ℚ) (j : Y.X ⟶ GlobalTheory.FlagZ.Fl ι N), IsPullback j Y.str (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ)) → ∀ y : Y.X, ∃ (U : Y.X.Opens) (A : GlobalTheory.FlagBundle.Mat (fun _ : ι => N) Y.Fn), y ∈ U ∧ ∀ z ∈ U, GlobalTheory.FlagQ.IsFrame j z A := by
  first | exact @GlobalTheory.FlagQ.exists_isFrame | exact GlobalTheory.FlagQ.exists_isFrame | (intros; apply GlobalTheory.FlagQ.exists_isFrame <;> assumption)
