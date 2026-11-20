import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneTmulBcrisGaloisLatticeInjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FOneTmulBcrisGaloisLatticeInjective.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.one_tmul_bcris_galoisLattice_injective : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL), Function.Injective (fun x : ↥T.L.T => (1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) := by
  first | exact @GlobalTheory.TContInj.main | exact GlobalTheory.TContInj.main | (intros; apply GlobalTheory.TContInj.main <;> assumption)
