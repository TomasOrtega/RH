import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ _ _ _ a d`. Use `letI : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _`. Use `haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩`. Use `haveI : LocallyCompactSpace (Matrix (Fin a) (Fin d) k) := inferInstanceAs (LocallyCompactSpace (Fin a → Fin d → k))`. Conclude with `⟨Measure.addHaar, inferInstance⟩`.
-/
theorem haar_exists_matrix_local_field : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ},
    ∃ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν := by
  intro k _ _ _ _ a d
  letI : MeasurableSpace (Matrix (Fin a) (Fin d) k) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin d) k) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin a) (Fin d) k) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin d → k))
  exact ⟨Measure.addHaar, inferInstance⟩

end GlobalTheory
