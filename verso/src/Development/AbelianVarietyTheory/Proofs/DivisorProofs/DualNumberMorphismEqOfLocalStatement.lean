import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberMorphismEqOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDualNumberMorphismEqOfLocal.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.dual_number_morphism_eq_of_local : ∀ {L : Type} [CommRing L] {s : Set L}, Ideal.span s = ⊤ → ∀ {Y : Scheme.{0}} {w w' : Sp (DualNumber L) ⟶ Y}, (∀ a : s, spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w = spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w') → w = w' := by
  first | exact @GlobalTheory.ArLieBase.hom_ext_dualNumber_away | exact GlobalTheory.ArLieBase.hom_ext_dualNumber_away | (intros; apply GlobalTheory.ArLieBase.hom_ext_dualNumber_away <;> assumption)
