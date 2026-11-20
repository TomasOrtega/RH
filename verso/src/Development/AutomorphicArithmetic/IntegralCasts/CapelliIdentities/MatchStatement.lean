import Mathlib

/- English proof (translation)
Introduce `Ω _ W κ _ x ⟨j0, hj0⟩`. Establish `: Nonempty κ` using `⟨j0⟩`. Take `⟨c, hc⟩` from `Finite.exists_max (fun j => W.valuation (x j))`. Establish `hc0 : x c ≠ 0`. Introduce `h`.

Establish `h1` using `hc j0`. Simplify using `only [h, map_zero] at h1`. Conclude with `hj0 ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le))`. Use `⟨c, hc0, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← ValuationSubring.valuation_le_one_iff, map_div₀]`.

Establish `hpos : W.valuation (x c) ≠ 0` using `(Valuation.ne_zero_iff _).2 hc0`. Conclude with `(div_le_one₀ (zero_lt_iff.2 hpos)).2 (hc j)`.
-/
theorem UpperTheory.Reformulated.B.ValuationSubringDominantCoordinate.main.{u_1} :
    ∀ {Ω : Type} [inst : Field Ω] (W : ValuationSubring Ω) {κ : Type u_1} [Finite κ] (x : κ → Ω),
      (∃ (j : κ), x j ≠ (0 : Ω)) → ∃ (c : κ), x c ≠ (0 : Ω) ∧ ∀ (j : κ), x j / x c ∈ W := by
  intro Ω _ W κ _ x ⟨j0, hj0⟩
  have : Nonempty κ := ⟨j0⟩
  obtain ⟨c, hc⟩ := Finite.exists_max (fun j => W.valuation (x j))
  have hc0 : x c ≠ 0 := by
    intro h
    have h1 := hc j0
    simp only [h, map_zero] at h1
    exact hj0 ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le))
  refine ⟨c, hc0, fun j => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
  have hpos : W.valuation (x c) ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  exact (div_le_one₀ (zero_lt_iff.2 hpos)).2 (hc j)
