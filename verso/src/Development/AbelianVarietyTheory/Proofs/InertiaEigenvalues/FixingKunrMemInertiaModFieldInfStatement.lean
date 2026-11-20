import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingKunrMemInertiaModFieldInf
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertiaMod.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FFixingKunrMemInertiaModFieldInf.lean&line=128#L128)
-/
theorem _root_.GlobalTheory.T.fixing_kunr_mem_inertia_mod_fieldInf : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x) → ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ h ∈ ϖ.GfieldInf a, (k' : GQ l) = g * h := by
  first | exact @GlobalTheory.InertiaMod.main | exact GlobalTheory.InertiaMod.main | (intros; apply GlobalTheory.InertiaMod.main <;> assumption)
