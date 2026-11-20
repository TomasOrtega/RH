import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaQlLeInertiaOfFiniteExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InerQl.IK_mem_Iner` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FInertiaQlLeInertiaOfFiniteExtension.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.inertia_Ql_le_inertia_of_finite_extension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → g ∈ (pc Pl h hN hF hS).Iner := by
  first | exact @GlobalTheory.InerQl.IK_mem_Iner | exact GlobalTheory.InerQl.IK_mem_Iner | (intros; apply GlobalTheory.InerQl.IK_mem_Iner <;> assumption)
