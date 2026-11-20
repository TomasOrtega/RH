import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationAlgebraMapEq
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.nval_algebraMap_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNormalizedValuationAlgebraMapEq.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.normalizedValuation_algebraMap_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (l : ℕ) (x : O), Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' x) = Formalism.MainNotions.BlochKatoReduction.Gen.nval O l x := by
  first | exact @GlobalTheory.nval_algebraMap_eq | exact GlobalTheory.nval_algebraMap_eq | (intros; apply GlobalTheory.nval_algebraMap_eq <;> assumption)
