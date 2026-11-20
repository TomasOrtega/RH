import Mathlib

/- English proof (translation)
Introduce `K _ _ l _ e x`. Establish `hx : IsIntegral ℤ (e (algebraMap (NumberField.RingOfIntegers K) K x))` using `(NumberField.RingOfIntegers.isIntegral_coe x).map e.toIntAlgHom`. Generalize the expression as in `e (algebraMap (NumberField.RingOfIntegers K) K x) = y at hx`. Set `S : Subring (PadicAlgCl l)` to `(NormedField.valuation (K := PadicAlgCl l)).integer`. Establish `hS : IsIntegral S y` using `hx.tower_top`.

Establish `h` using `(Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral hS`. Rewrite `h` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `h` after adjusting the coercions.
-/
theorem UpperTheory.norm_integers_le_one :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact (Nat.Prime l)] (e : K →+* PadicAlgCl l) (x : NumberField.RingOfIntegers K), ‖e (algebraMap (NumberField.RingOfIntegers K) K x)‖ ≤ 1 := by
  intro K _ _ l _ e x
  have hx : IsIntegral ℤ (e (algebraMap (NumberField.RingOfIntegers K) K x)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map e.toIntAlgHom
  generalize e (algebraMap (NumberField.RingOfIntegers K) K x) = y at hx
  let S : Subring (PadicAlgCl l) := (NormedField.valuation (K := PadicAlgCl l)).integer
  have hS : IsIntegral S y := hx.tower_top
  have h := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral hS
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h
