import Mathlib

/- English proof (translation)
Introduce `Ω _ A T _ y ⟨x1, hx1⟩`. Establish `: Nonempty {x : T // y x ≠ 0}` using `⟨⟨x1, hx1⟩⟩`. Take `⟨⟨x₀, h0⟩, hmax⟩` from `Finite.exists_max (fun z : {x : T // y x ≠ 0} => A.valuation (y z.1))`. Use `⟨x₀, h0, fun x => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hx : y x = 0`.

Rewrite using `[hx, zero_div]`. Conclude with `A.zero_mem`. Rewrite using `[← A.valuation_le_one_iff, map_div₀]`. Establish `hpos : (0 : A.ValueGroup) < A.valuation (y x₀)`. Rewrite using `[zero_lt_iff]`.

Conclude with `(Valuation.ne_zero_iff _).mpr h0`. Conclude with `(div_le_one₀ hpos).mpr (hmax ⟨x, hx⟩)`.
-/
theorem UpperTheory.Reformulated.B.Yla8.main :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {T : Type} [Finite T] (y : T → Ω),
      (∃ (x : T), y x ≠ (0 : Ω)) → ∃ (x₀ : T), y x₀ ≠ (0 : Ω) ∧ ∀ (x : T), y x / y x₀ ∈ A := by
  intro Ω _ A T _ y ⟨x1, hx1⟩
  have : Nonempty {x : T // y x ≠ 0} := ⟨⟨x1, hx1⟩⟩
  obtain ⟨⟨x₀, h0⟩, hmax⟩ := Finite.exists_max (fun z : {x : T // y x ≠ 0} => A.valuation (y z.1))
  refine ⟨x₀, h0, fun x => ?_⟩
  by_cases hx : y x = 0
  · rw [hx, zero_div]; exact A.zero_mem
  · rw [← A.valuation_le_one_iff, map_div₀]
    have hpos : (0 : A.ValueGroup) < A.valuation (y x₀) := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr h0
    exact (div_le_one₀ hpos).mpr (hmax ⟨x, hx⟩)
