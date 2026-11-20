import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.OneParam
import Formalism.RealPlaceAnalysis.QuotientSettingHolds

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Establish `hk : toMK k ∈ Formalism.REAL.Kset ε`. Rewrite using `[← Formalism.REAL.range_toMK]`. Conclude with `⟨k, rfl⟩`. Take `⟨Y, hY, he, -⟩` from `Formalism.REAL.kExp n ε (toMK k) hk`. Conclude with `⟨Y, hY, he.symm⟩`.
-/
theorem exists_log (ε : Fin n → Bool) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ toMK k = NormedSpace.exp Y := by
  have hk : toMK k ∈ Formalism.REAL.Kset ε := by
    rw [← Formalism.REAL.range_toMK]; exact ⟨k, rfl⟩
  obtain ⟨Y, hY, he, -⟩ := Formalism.REAL.kExp n ε (toMK k) hk
  exact ⟨Y, hY, he.symm⟩

/- English proof (translation)
Take `⟨Y, hY, he⟩` from `exists_log ε k`. Take `⟨γ, hγ⟩` from `exists_curve ε hY`. Establish `h1 : γ 1 = k` using `onep_KG_ext (by rw [hγ, he]; simp)`. Use `⟨Y, hY, ?_⟩` and prove the remaining obligations. Establish `h2` using `ReciprocityTheory.ChartRestriction.DS.HW.KType.op_curve T hY γ hγ 1`.

Rewrite `h2` using `[h1]`. Simplify using `using h2`.
-/
theorem KType.op_eq_exp {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ T.op k = NormedSpace.exp (T.dτ Y) := by
  obtain ⟨Y, hY, he⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : γ 1 = k := onep_KG_ext (by rw [hγ, he]; simp)
  refine ⟨Y, hY, ?_⟩
  have h2 := ReciprocityTheory.ChartRestriction.DS.HW.KType.op_curve T hY γ hγ 1
  rw [h1] at h2
  simpa using h2

end ReciprocityTheory.ChartRestriction.DS.HW
