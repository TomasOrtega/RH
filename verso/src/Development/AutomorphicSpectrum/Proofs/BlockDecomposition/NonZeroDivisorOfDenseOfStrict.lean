import Mathlib

namespace GlobalTheory.CompanionTheory.ComplReg

/- English proof (translation)
Establish `key : ∀ t : T, t * g π = 0 → ∀ M : ℕ, t ∈ Ideal.span {g π ^ M}`. Introduce `t ht M`. Take `⟨x, hx⟩` from `hd M t`. Rewrite `hx` using `[Ideal.mem_span_singleton]`. Take `⟨d, hd'⟩` from `hx`.

Establish `hxπ : x * π ∈ Ideal.span {π ^ (M + 1)}`. Apply `hk (M + 1) (x * π)` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `⟨-d, by rw [map_mul]; linear_combination ht - g π * hd'⟩`. Rewrite `hxπ` using `[Ideal.mem_span_singleton]`.

Take `⟨c, hc⟩` from `hxπ`. Establish `h0 : (x - π ^ M * c) * π = 0`. Rewrite using `[sub_mul, hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hxeq : x = π ^ M * c` using `sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hπ).2 _ h0)`.

Establish `hgx : g x = g π ^ M * g c`. Rewrite using `[hxeq, map_mul, map_pow]`. Rewrite using `[Ideal.mem_span_singleton]`. Conclude with `⟨d + g c, by linear_combination hd' + hgx⟩`. Establish `main : ∀ t : T, t * g π = 0 → t = 0`.

Introduce `t ht`. Use `IsHausdorff.haus hH t (fun n => ?_)` and prove the remaining obligations. Rewrite using `[SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`. Conclude with `key t ht n`. Rewrite using `[mem_nonZeroDivisors_iff]`.

Conclude with `⟨fun t ht => main t (by rwa [mul_comm] at ht), main⟩`.
-/
theorem nonZeroDivisor_of_dense_of_strict {B T : Type} [CommRing B] [CommRing T] (π : B)
    (g : B →+* T) (hH : IsHausdorff (Ideal.span {g π}) T)
    (hd : ∀ (M : ℕ) (y : T), ∃ x, y - g x ∈ Ideal.span {g π ^ M})
    (hk : ∀ (M : ℕ) (x : B), g x ∈ Ideal.span {g π ^ M} → x ∈ Ideal.span {π ^ M})
    (hπ : π ∈ nonZeroDivisors B) : g π ∈ nonZeroDivisors T := by
  have key : ∀ t : T, t * g π = 0 → ∀ M : ℕ, t ∈ Ideal.span {g π ^ M} := by
    intro t ht M
    obtain ⟨x, hx⟩ := hd M t
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨d, hd'⟩ := hx
    have hxπ : x * π ∈ Ideal.span {π ^ (M + 1)} := by
      apply hk (M + 1) (x * π)
      rw [Ideal.mem_span_singleton]
      exact ⟨-d, by rw [map_mul]; linear_combination ht - g π * hd'⟩
    rw [Ideal.mem_span_singleton] at hxπ
    obtain ⟨c, hc⟩ := hxπ
    have h0 : (x - π ^ M * c) * π = 0 := by
      rw [sub_mul, hc]
      ring
    have hxeq : x = π ^ M * c := sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hπ).2 _ h0)
    have hgx : g x = g π ^ M * g c := by
      rw [hxeq, map_mul, map_pow]
    rw [Ideal.mem_span_singleton]
    exact ⟨d + g c, by linear_combination hd' + hgx⟩
  have main : ∀ t : T, t * g π = 0 → t = 0 := by
    intro t ht
    refine IsHausdorff.haus hH t (fun n => ?_)
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact key t ht n
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun t ht => main t (by rwa [mul_comm] at ht), main⟩

end GlobalTheory.CompanionTheory.ComplReg
