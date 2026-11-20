import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDvdOfForallNearOD.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.dvd_of_forall_approx_toOD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ) (w : OD l O), (∀ k : ℕ, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ w - (l : OD l O) ^ k * toOD l O y) → ϖ.iAl O K (EIn l e _) ^ m ∣ w := by
  first | exact @GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD | exact GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD | (intros; apply GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD <;> assumption)
