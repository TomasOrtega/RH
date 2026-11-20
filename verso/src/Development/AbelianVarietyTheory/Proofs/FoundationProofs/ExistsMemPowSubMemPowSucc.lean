import Mathlib

universe u_1 u_2

namespace GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `y _`. Take `⟨a, ha⟩` from `h0 y`. Conclude with `⟨a, by simp, by simpa using ha⟩`.

Consider the case `succ n ih`. Introduce `y hy`. Rewrite `hy` using `[pow_succ]`. Use `Submodule.mul_induction_on hy (fun p hp q hq => ?_) (fun y1 y2 h1' h2' => ?_)` and prove the remaining obligations. Take `⟨xp, hxp, hp'⟩` from `ih p hp`.

Take `⟨xq, hxq, hq'⟩` from `h1 q hq`. Use `⟨xp * xq, by rw [pow_succ]; exact Ideal.mul_mem_mul hxp hxq, ?_⟩` and prove the remaining obligations. Establish `e : φ (xp * xq) - p * q = (φ xp - p) * φ xq + p * (φ xq - q)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hp' (Ideal.mem_comap.1 (hIJ hxq))`. Rewrite using `[show n + 1 + 1 = n + 2 from rfl, pow_add]`.

Conclude with `Ideal.mul_mem_mul hp hq'`. Take `⟨x1, hx1, e1⟩` from `h1'`. Take `⟨x2, hx2, e2⟩` from `h2'`. Use `⟨x1 + x2, Ideal.add_mem _ hx1 hx2, ?_⟩` and prove the remaining obligations. Establish `e : φ (x1 + x2) - (y1 + y2) = (φ x1 - y1) + (φ x2 - y2)`.

Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ e1 e2`.
-/
theorem exists_mem_pow_sub_mem_pow_succ {A : Type u_1} [CommRing A] {B : Type u_2} [CommRing B]
    {φ : A →+* B} {I : Ideal A} {J : Ideal B} (hIJ : I ≤ Ideal.comap φ J)
    (h0 : ∀ b : B, ∃ a : A, φ a - b ∈ J)
    (h1 : ∀ y ∈ J, ∃ x ∈ I, φ x - y ∈ J ^ (2 : ℕ)) (n : ℕ) :
    ∀ y ∈ J ^ n, ∃ x ∈ I ^ n, φ x - y ∈ J ^ (n + (1 : ℕ)) := by
  induction n with
  | zero =>
    intro y _
    obtain ⟨a, ha⟩ := h0 y
    exact ⟨a, by simp, by simpa using ha⟩
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun p hp q hq => ?_) (fun y1 y2 h1' h2' => ?_)
    · obtain ⟨xp, hxp, hp'⟩ := ih p hp
      obtain ⟨xq, hxq, hq'⟩ := h1 q hq
      refine ⟨xp * xq, by rw [pow_succ]; exact Ideal.mul_mem_mul hxp hxq, ?_⟩
      have e : φ (xp * xq) - p * q = (φ xp - p) * φ xq + p * (φ xq - q) := by
        rw [map_mul]
        ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hp' (Ideal.mem_comap.1 (hIJ hxq))
      · rw [show n + 1 + 1 = n + 2 from rfl, pow_add]
        exact Ideal.mul_mem_mul hp hq'
    · obtain ⟨x1, hx1, e1⟩ := h1'
      obtain ⟨x2, hx2, e2⟩ := h2'
      refine ⟨x1 + x2, Ideal.add_mem _ hx1 hx2, ?_⟩
      have e : φ (x1 + x2) - (y1 + y2) = (φ x1 - y1) + (φ x2 - y2) := by
        rw [map_add]
        ring
      rw [e]
      exact Ideal.add_mem _ e1 e2

end GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts
