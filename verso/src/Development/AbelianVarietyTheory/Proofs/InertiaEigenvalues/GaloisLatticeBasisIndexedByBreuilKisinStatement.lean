import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticeBasisIndexedByBreuilKisin
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BKGal.IdentRank.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGaloisLatticeBasisIndexedByBreuilKisin.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.galoisLattice_basis_indexed_by_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL), Ident (thetaW a LL) ϖ P T → Nonempty (Module.Basis ι ↥(OL LL) ↥T.L.T) := by
  first | exact @GlobalTheory.BKGal.IdentRank.main | exact GlobalTheory.BKGal.IdentRank.main | (intros; apply GlobalTheory.BKGal.IdentRank.main <;> assumption)
