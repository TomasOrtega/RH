import Mathlib
import Formalism.TruncatedSeriesCounting.StatementX

namespace Formalism.TruncatedSeriesCounting.X

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro z hz`. Simplify using `using hz`. Consider the case `succ n ih`.

Introduce `z hz`. Apply `ih` to reduce the goal to its premises. Apply `h` to reduce the goal to its premises. Establish `e : ℓ * (ℓ ^ n * z) = ℓ ^ (n + 1) * z` using `by ring`. Rewrite using `[e]`.

Conclude with `hz`.
-/
private theorem iter_nzd {A : Type} [CommRing A] (ℓ g : A)
    (h : ∀ a : A, ℓ * a ∈ Ideal.span {g} → a ∈ Ideal.span {g}) :
    ∀ (n : ℕ) (z : A), ℓ ^ n * z ∈ Ideal.span {g} → z ∈ Ideal.span {g} := by
  intro n
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
    intro z hz
    apply ih
    apply h
    have e : ℓ * (ℓ ^ n * z) = ℓ ^ (n + 1) * z := by ring
    rw [e]; exact hz

/- English proof (translation)
Introduce `A _ _ ℓ f f' hf' hℓf hℓf' x k ⟨b, hb⟩ ⟨a, ha⟩`. Establish `inj : Function.Injective (algebraMap A (FractionRing A))` using `IsFractionRing.injective A (FractionRing A)`. Establish `h1 : ℓ ^ k * b = f' * (f * a)`. Apply `inj` to reduce the goal to its premises. Rewrite using `[map_mul, map_pow, hb, map_mul (algebraMap A (FractionRing A)) f', ha]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.mp (iter_nzd ℓ f' hℓf' k b (by`. Rewrite using `[h1]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f')))`. Establish `hf'0 : algebraMap A (FractionRing A) f' ≠ 0` using `(map_ne_zero_iff _ inj).mpr hf'`.

Establish `hx : x = algebraMap A (FractionRing A) c`. Apply `mul_left_cancel₀ hf'0` to reduce the goal to its premises. Rewrite using `[← hb, hc, map_mul]`. Establish `h2 : ℓ ^ k * c = f * a`. Apply `inj` to reduce the goal to its premises.

Rewrite using `[map_mul, map_pow, ← hx, ha]`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton.mp (iter_nzd ℓ f hℓf k c (by`. Rewrite using `[h2]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))`. Conclude with `⟨d, by rw [hx, hd]⟩`.
-/
theorem saturation_criterion : SatA := by
  intro A _ _ ℓ f f' hf' hℓf hℓf' x k ⟨b, hb⟩ ⟨a, ha⟩
  have inj : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective A (FractionRing A)
  have h1 : ℓ ^ k * b = f' * (f * a) := by
    apply inj
    rw [map_mul, map_pow, hb, map_mul (algebraMap A (FractionRing A)) f', ha]
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (iter_nzd ℓ f' hℓf' k b (by
    rw [h1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f')))
  have hf'0 : algebraMap A (FractionRing A) f' ≠ 0 := (map_ne_zero_iff _ inj).mpr hf'
  have hx : x = algebraMap A (FractionRing A) c := by
    apply mul_left_cancel₀ hf'0
    rw [← hb, hc, map_mul]
  have h2 : ℓ ^ k * c = f * a := by
    apply inj
    rw [map_mul, map_pow, ← hx, ha]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (iter_nzd ℓ f hℓf k c (by
    rw [h2]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
  exact ⟨d, by rw [hx, hd]⟩

end Formalism.TruncatedSeriesCounting.X
