import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousTorepK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hwfin_rhoC_eq (ε : Fin n → Bool) : Formalism.REAL.rhoC ε = rhoC ε := rfl

/- English proof (translation)
Take `⟨σ, -, hU, hK⟩` from `KType.exists_rep T`. Establish `h` using `weyl_dimension_formula_product n ε Λ T.V σ ⊤ hU hK`. Rewrite `h` using `[finrank_top]`. Conclude with `h`.
-/
theorem hwfin_weyl {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    (Module.finrank ℂ T.V : ℝ) =
      (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Λ + rhoC ε) a - (Λ + rhoC ε) b)) /
      ((∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) *
        ∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ)) := by
  obtain ⟨σ, -, hU, hK⟩ := KType.exists_rep T
  have h := weyl_dimension_formula_product n ε Λ T.V σ ⊤ hU hK
  rw [finrank_top] at h
  exact h

/- English proof (translation)
Establish `h` using `hwfin_weyl (trivialKType ε)`. Establish `h1 : (Module.finrank ℂ (trivialKType ε).V : ℝ) = 1` using `by show (Module.finrank ℂ ℂ : ℝ) = 1`. Simplify using the standard rewrite rules. Rewrite `h` using `[h1]`. Simplify using `only [zero_add] at h`.

Establish `hD : ((∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ)) ≠ 0`. Introduce `h0`. Rewrite `h` using `[h0, div_zero]`. Conclude with `one_ne_zero h`. Clear denominators, using `at h` for the nonvanishing conditions.

Conclude with `h.symm`.
-/
theorem hwfin_denom (ε : Fin n → Bool) :
    (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b), (rhoC ε a - rhoC ε b)) =
      (∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) *
        ∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ) := by
  have h := hwfin_weyl (trivialKType ε)
  have h1 : (Module.finrank ℂ (trivialKType ε).V : ℝ) = 1 := by
    show (Module.finrank ℂ ℂ : ℝ) = 1
    simp
  rw [h1] at h
  simp only [zero_add] at h
  have hD : ((∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nPl ε), (i.factorial : ℝ)) *
        ∏ i ∈ Finset.range (Formalism.MainNotions.LocalBesselAndTopKernel.nMi ε), (i.factorial : ℝ)) ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h
    exact one_ne_zero h
  field_simp at h
  exact h.symm

/- English proof (translation)
Rewrite using `[hwfin_weyl T, ← hwfin_denom ε, ← Finset.prod_div_distrib]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_div_distrib]`.
-/
theorem kType_finrank {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    (Module.finrank ℂ T.V : ℝ) = ∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
      ((Λ + rhoC ε) a - (Λ + rhoC ε) b) / (rhoC ε a - rhoC ε b) := by
  rw [hwfin_weyl T, ← hwfin_denom ε, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_div_distrib]

end ReciprocityTheory.ChartRestriction.DS.HW
