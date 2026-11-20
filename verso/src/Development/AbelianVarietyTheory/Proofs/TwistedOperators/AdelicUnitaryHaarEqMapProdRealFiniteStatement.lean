import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryHaarEqMapProdRealFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HaarSplit.haar_eq_map_prod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FAdelicUnitaryHaarEqMapProdRealFinite.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.adelicUnitaryHaar_eq_map_prod_real_finite : ∀ (D : D7) (Y : HSp D) (ν : Measure (GA D Y)), ν.IsHaarMeasure → ∃ (m : Measure (GinfC Y)) (μ : Measure (GfC Y)), m.IsHaarMeasure ∧ μ.IsHaarMeasure ∧ SigmaFinite m ∧ SigmaFinite μ ∧ MeasurableEmbedding (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) ∧ ν = (m.prod μ).map (fun q : GinfC Y × GfC Y => (q.1 : GA D Y) * q.2) := by
  first | exact @GlobalTheory.HaarSplit.haar_eq_map_prod | exact GlobalTheory.HaarSplit.haar_eq_map_prod | (intros; apply GlobalTheory.HaarSplit.haar_eq_map_prod <;> assumption)
