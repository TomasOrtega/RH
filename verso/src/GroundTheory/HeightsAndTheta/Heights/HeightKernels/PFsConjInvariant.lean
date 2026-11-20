import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace FubiniStudyConjugationInvariant

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem fsMetric_conj {n : Type*} [Fintype n] (w : n → ℂ) :
    (fsMetric n).ρ (fun i => (starRingEnd ℂ) (w i)) = (fsMetric n).ρ w := by
  simp [fsMetric, EuclideanSpace.norm_eq]

end FubiniStudyConjugationInvariant

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem FsConjInvariant.proof : FsConjInvariant.Statement := by
  intro K _ ι _ z
  simp only [fsMulti, HermLine.ofMetrics]
  exact Finset.prod_congr rfl fun k _ => by
    rw [FubiniStudyConjugationInvariant.fsMetric_conj (fun i => z ⟨k, i⟩)]

end GroundTheory.Heights₂.Heights
