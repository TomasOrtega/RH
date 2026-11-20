import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Per.TiedRestrict.restrict_crys_deRham` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRestrictCrystallineDeRhamFiniteExt.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.restrict_crystalline_deRham_finiteExt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (IsCrys (P.PD K) ρ → IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) ∧ (IsDR (P.PD K) ρ ↔ IsDR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) := by
  first | exact @GlobalTheory.Per.TiedRestrict.restrict_crys_deRham | exact GlobalTheory.Per.TiedRestrict.restrict_crys_deRham | (intros; apply GlobalTheory.Per.TiedRestrict.restrict_crys_deRham <;> assumption)
