import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesSUIff
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationOfSpecialUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationUnitaryOfFullStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassificationRankOneStatement

open GlobalTheory.DSSU

namespace GlobalTheory.DSSU.FromSU

/- English proof (translation)
Break down `Nat.lt_or_ge n 2 with h2 | h2` into its components or cases. Take `rfl : n = 1` from `by omega`. Conclude with `GlobalTheory.T.classification_rank_one.1 ε`. Conclude with `(GlobalTheory.Published.discreteSeriesSU_iff.mp h) n h2 ε`.
-/
theorem classS_of_discreteSeriesSU (h : GlobalTheory.Published.DiscreteSeriesSU) (n : ℕ) (hn : 1 ≤ n) (ε : Fin n → Bool) : ClassS ε := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · obtain rfl : n = 1 := by omega
    exact GlobalTheory.T.classification_rank_one.1 ε
  · exact (GlobalTheory.Published.discreteSeriesSU_iff.mp h) n h2 ε

/- English proof (translation)
Introduce `h`. Rewrite using `[GlobalTheory.Published.discreteSeriesClassification_iff, dsClass_iff]`. Introduce `n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Conclude with `GlobalTheory.T.classification_rank_one.2`.

Conclude with `GlobalTheory.T.classification_unitary_of_full n (fun ε => GlobalTheory.T.classification_of_special_unitary n hn ε (classS_of_discreteSeriesSU h n hn ε))`.
-/
theorem discreteSeriesClassification_of_SU :
    GlobalTheory.Published.DiscreteSeriesSU → GlobalTheory.Published.DiscreteSeriesClassification := by
  intro h
  rw [GlobalTheory.Published.discreteSeriesClassification_iff, dsClass_iff]
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.T.classification_rank_one.2
  · exact GlobalTheory.T.classification_unitary_of_full n (fun ε => GlobalTheory.T.classification_of_special_unitary n hn ε (classS_of_discreteSeriesSU h n hn ε))

end GlobalTheory.DSSU.FromSU
