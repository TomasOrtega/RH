import Mathlib

namespace GlobalTheory.SpanPairPowSucc

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `x hx`. Rewrite `hx` using `[zero_add, pow_one]`. Take `⟨a, b, rfl⟩` from `Ideal.mem_span_pair.mp hx`.

Conclude with `⟨b, a, by simp, by ring⟩`. Consider the case `succ k ih`. Introduce `x hx`. Rewrite `hx` using `[pow_succ]`. Use `Submodule.mul_induction_on hx ?_ ?_` and prove the remaining obligations.

Introduce `y hy z hz`. Take `⟨c, G, hG, rfl⟩` from `ih y hy`. Take `⟨a, b, rfl⟩` from `Ideal.mem_span_pair.mp hz`. Use `⟨c * b, w ^ (k + 1) * c * a + G * (a * p + b * w), ?_, by ring⟩` and prove the remaining obligations. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations.

Establish `hw : w ∈ Ideal.span ({p, w} : Set R)` using `Ideal.subset_span (by simp)`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw _))`. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hG hz`. Introduce and unpack `_ _ ⟨c₁, G₁, hG₁, rfl⟩ ⟨c₂, G₂, hG₂, rfl⟩`.

Conclude with `⟨c₁ + c₂, G₁ + G₂, Ideal.add_mem _ hG₁ hG₂, by ring⟩`.
-/
theorem mem_span_pair_pow_succ {R : Type} [inst : CommRing R] (p w : R) (k : ℕ) :
    ∀ x ∈ Ideal.span {p, w} ^ (k + (1 : ℕ)),
      ∃ (c : R), ∃ G ∈ Ideal.span {p, w} ^ k, x = w ^ (k + (1 : ℕ)) * c + p * G := by
  induction k with
  | zero =>
    intro x hx
    rw [zero_add, pow_one] at hx
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
    exact ⟨b, a, by simp, by ring⟩
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro y hy z hz
      obtain ⟨c, G, hG, rfl⟩ := ih y hy
      obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hz
      refine ⟨c * b, w ^ (k + 1) * c * a + G * (a * p + b * w), ?_, by ring⟩
      refine Ideal.add_mem _ ?_ ?_
      · have hw : w ∈ Ideal.span ({p, w} : Set R) := Ideal.subset_span (by simp)
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw _))
      · rw [pow_succ]
        exact Ideal.mul_mem_mul hG hz
    · rintro _ _ ⟨c₁, G₁, hG₁, rfl⟩ ⟨c₂, G₂, hG₂, rfl⟩
      exact ⟨c₁ + c₂, G₁ + G₂, Ideal.add_mem _ hG₁ hG₂, by ring⟩

end GlobalTheory.SpanPairPowSucc
