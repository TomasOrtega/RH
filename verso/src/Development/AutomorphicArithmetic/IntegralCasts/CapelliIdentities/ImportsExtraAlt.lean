import Mathlib

namespace UpperTheory.Reformulated.B.S6

/- English proof (translation)
Set `v : Valuation (PadicAlgCl l) NNReal` to `NormedField.valuation`. Establish `hmem : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer`. Introduce `a`. Establish `h : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']`.

Conclude with `a.2`. Conclude with `h`. Set `f : ℤ_[l] →+* v.integer` to `(algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer hmem`. Establish `hint : IsIntegral v.integer x`. Take `⟨P, hP, hPx⟩` from `hx`.

Use `⟨P.map f, hP.map f, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Conclude with `hPx`. Conclude with `(Valuation.integer.integers v).mem_of_integral hint`.
-/
theorem norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  let v : Valuation (PadicAlgCl l) NNReal := NormedField.valuation
  have hmem : ∀ a : ℤ_[l], algebraMap ℤ_[l] (PadicAlgCl l) a ∈ v.integer := by
    intro a
    have h : ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
      exact a.2
    exact h
  let f : ℤ_[l] →+* v.integer := (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer hmem
  have hint : IsIntegral v.integer x := by
    obtain ⟨P, hP, hPx⟩ := hx
    refine ⟨P.map f, hP.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hPx
  exact (Valuation.integer.integers v).mem_of_integral hint

end UpperTheory.Reformulated.B.S6
