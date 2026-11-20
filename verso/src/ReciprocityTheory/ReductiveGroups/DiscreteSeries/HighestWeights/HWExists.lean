import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.HW

def HighestWeightExistsBody : Prop :=
  ∀ (k : ℕ) (u : Fin k → ℝ), Formalism.QuantumDeterminants.IsHCParam u →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsHCTypeU k u π

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

/- English proof (translation)
Establish `hJ : Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) = 1`. Unfold `Formalism.REAL.Jm Formalism.MainNotions.S.allPos`. Use `first`. Consider the case `simp`. Consider the case `(ext i j; simp [Matrix.diagonal, Matrix.one_apply])`.

Use extensionality with `g`. Use `first`. Consider the case `simp only [Formalism.MainNotions.S.UJset, Formalism.REAL.Kset, Set.mem_setOf_eq, Formalism.REAL.inUJ, hJ, mul_one, one_mul, and_true, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Consider the case `simp [Formalism.MainNotions.S.UJset, Formalism.REAL.Kset, Formalism.REAL.inUJ, hJ, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`.
-/
theorem UJset_allPos_eq_Kset (k : ℕ) :
    Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos k) = Formalism.REAL.Kset (Formalism.MainNotions.S.allPos k) := by
  have hJ : Formalism.REAL.Jm (Formalism.MainNotions.S.allPos k) = 1 := by
    unfold Formalism.REAL.Jm Formalism.MainNotions.S.allPos
    first
    | simp
    | (ext i j; simp [Matrix.diagonal, Matrix.one_apply])
  ext g
  first
  | simp only [Formalism.MainNotions.S.UJset, Formalism.REAL.Kset, Set.mem_setOf_eq, Formalism.REAL.inUJ, hJ, mul_one, one_mul,
      and_true, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  | simp [Formalism.MainNotions.S.UJset, Formalism.REAL.Kset, Formalism.REAL.inUJ, hJ, Matrix.mem_unitaryGroup_iff',
      Matrix.star_eq_conjTranspose]

/- English proof (translation)
Introduce `k u hu`. Take `⟨T⟩` from `kType_exists (Formalism.MainNotions.S.allPos k) u hu`. Take `⟨σ, -, hU, hK⟩` from `KType.exists_rep T`. Use `⟨T.V, inferInstance, inferInstance, σ, ?_, inferInstance, ?_, hK⟩` and prove the remaining obligations. Use `⟨⟨T.w, 0, ?_⟩⟩` and prove the remaining obligations.

Introduce `h`. Use `T.w_norm` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this`. Rewrite using `[UJset_allPos_eq_Kset]`.

Conclude with `hU`.
-/
theorem highest_weight_exists : HighestWeightExistsBody := by
  intro k u hu
  obtain ⟨T⟩ := kType_exists (Formalism.MainNotions.S.allPos k) u hu
  obtain ⟨σ, -, hU, hK⟩ := KType.exists_rep T
  refine ⟨T.V, inferInstance, inferInstance, σ, ?_, inferInstance, ?_, hK⟩
  · refine ⟨⟨T.w, 0, ?_⟩⟩
    intro h
    have := T.w_norm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  · rw [UJset_allPos_eq_Kset]
    exact hU

end ReciprocityTheory.ChartRestriction.DS.HW
