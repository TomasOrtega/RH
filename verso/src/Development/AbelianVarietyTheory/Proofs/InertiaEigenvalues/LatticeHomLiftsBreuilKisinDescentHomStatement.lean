import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomLiftsBreuilKisinDescentHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BKGal.PackMap.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLatticeHomLiftsBreuilKisinDescentHom.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T₁ T₂ : QLat LL) (P₁ : Pack a ϖ η H T₁) (P₂ : Pack a ϖ η H T₂) (f : LatHom T₁.L T₂.L), ∃ F : BKHom P₁.D P₂.D, IsMapOf P₁.R.I P₂.R.I f F.toHom := by
  first | exact @GlobalTheory.BKGal.PackMap.main | exact GlobalTheory.BKGal.PackMap.main | (intros; apply GlobalTheory.BKGal.PackMap.main <;> assumption)
