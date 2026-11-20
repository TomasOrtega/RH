import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorKeepsLatticeVacuumOfTrivialAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinZeta.MoveVac.vacFin_om_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FWeilOperatorKeepsLatticeVacuumOfTrivialAt.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.weilOperator_keeps_latticeVacuum_of_trivialAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D T), projV T v g = 1 → ∀ f, VacFin ψ S T v f → VacFin ψ S T v (om (1, g) f) := by
  first | exact @GlobalTheory.FinZeta.MoveVac.vacFin_om_one | exact GlobalTheory.FinZeta.MoveVac.vacFin_om_one | (intros; apply GlobalTheory.FinZeta.MoveVac.vacFin_om_one <;> assumption)
