import Mathlib
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[NumberField.isTotallyComplex_iff]`. Introduce `v`. Assume the negation of the conclusion as `hc`. Establish `hr : v.IsReal` using `InfinitePlace.not_isComplex_iff_isReal.mp hc`. Use `set ψ : K →+* ℝ := InfinitePlace.embedding_of_isReal hr`.

Establish `hψ : IsPrimitiveRoot (ψ ζ) m` using `hζ.map_of_injective ψ.injective`. Establish `hm0 : m ≠ 0` using `by omega`. Establish `h1 : ψ ζ ^ m = 1` using `hψ.pow_eq_one`. Establish `h2 : ψ ζ ^ 2 = 1`. Apply the tactic sequence `rcases (pow_eq_one_iff_of_ne_zero hm0).mp h1 with h | ⟨h, _⟩ <;> rw [h] <;> norm_num`.

Establish `h3 : ψ (ζ ^ 2) = ψ 1` using `by rw [map_pow, h2, map_one]`. Establish `h4 : ζ ^ 2 = 1` using `ψ.injective h3`. Establish `h5 : m ∣ 2` using `hζ.pow_eq_one_iff_dvd 2 |>.mp h4`. Use `Nat.le_of_dvd (by norm_num) h5` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem isTotallyComplex_of_primitiveRoot (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ)
    (hζ : IsPrimitiveRoot ζ m) (hm : 3 ≤ m) : NumberField.IsTotallyComplex K := by
  rw [NumberField.isTotallyComplex_iff]
  intro v
  by_contra hc
  have hr : v.IsReal := InfinitePlace.not_isComplex_iff_isReal.mp hc
  set ψ : K →+* ℝ := InfinitePlace.embedding_of_isReal hr
  have hψ : IsPrimitiveRoot (ψ ζ) m := hζ.map_of_injective ψ.injective
  have hm0 : m ≠ 0 := by omega
  have h1 : ψ ζ ^ m = 1 := hψ.pow_eq_one
  have h2 : ψ ζ ^ 2 = 1 := by
    rcases (pow_eq_one_iff_of_ne_zero hm0).mp h1 with h | ⟨h, _⟩ <;> rw [h] <;> norm_num
  have h3 : ψ (ζ ^ 2) = ψ 1 := by rw [map_pow, h2, map_one]
  have h4 : ζ ^ 2 = 1 := ψ.injective h3
  have h5 : m ∣ 2 := hζ.pow_eq_one_iff_dvd 2 |>.mp h4
  have := Nat.le_of_dvd (by norm_num) h5
  omega

/- English proof (translation)
Introduce `K _ _ ζ m hζ hm` and use `isTotallyComplex_of_primitiveRoot K ζ m hζ hm`.
-/
theorem tcroot : ∀ (K : Type) [Field K] [NumberField K] (ζ : K) (m : ℕ), IsPrimitiveRoot ζ m → 3 ≤ m →
    NumberField.IsTotallyComplex K :=
  fun K _ _ ζ m hζ hm => isTotallyComplex_of_primitiveRoot K ζ m hζ hm

end GlobalTheory
