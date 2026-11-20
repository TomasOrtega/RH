import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionEmptySecondIsSubquotientFirst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FParabolicInductionEmptySecondIsSubquotientFirst.lean&line=146#L146)
-/
theorem _root_.GlobalTheory.T.parabolicInduction_emptySecond_isSubquotient_first : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (r : ℕ) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin r) (s : ∀ j, IrrRep (GL (Fin (c j)) F)), c true = 0 → ∃ φ : Fin r ≃ Fin (c false), IsSubquotient (multiProd f fun j => (s j).ρ) ((s false).ρ.comp (reix F φ) : Representation ℂ (GL (Fin r) F) (s false).V) := by
  first | exact @GlobalTheory.EmptySecondBlockProd.isSubquotient_multiProd | exact GlobalTheory.EmptySecondBlockProd.isSubquotient_multiProd | (intros; apply GlobalTheory.EmptySecondBlockProd.isSubquotient_multiProd <;> assumption)
