import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `B A _ _ _ I K N hsurj hN`. Use `set f := algebraMap B A with hf`. Use `set J := I.map f with hJ`. Establish `key : ∀ n : ℕ, ∀ a : A, ∃ b : B, a - f b ∈ J ^ n ⊔ K`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `a`. Conclude with `⟨0, by simp⟩`. Consider the case `succ n ih`.

Establish `hspan : ∀ x ∈ J ^ n, ∀ c : A, ∃ b : B, c * x - f b ∈ J ^ (n + 1) ⊔ K`. Introduce `x hx`. Rewrite `hx` using `[hJ, ← Ideal.map_pow]`. Unfold `Ideal.map at hx`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`. Introduce `c`. Take `⟨b', hb'⟩` from `hsurj c`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp hb'`.

Use `⟨b' * i, ?_⟩` and prove the remaining obligations. Establish `hfi : f i ∈ J ^ n`. Rewrite using `[hJ, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ hi`. Establish `hc : c = f b' + y + z` using `by rw [add_assoc, hyz]; ring`.

Establish `e : c * f i - f (b' * i) = f i * y + z * f i`. Rewrite using `[hc, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `Submodule.add_mem_sup ?_ (K.mul_mem_right _ hz)` and prove the remaining obligations.

Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul hfi hy`. Consider the case `zero`. Introduce `c; exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Introduce `c`. Take `⟨b1, h1⟩` from `hx c`. Take `⟨b2, h2⟩` from `hy c`. Use `⟨b1 + b2, ?_⟩` and prove the remaining obligations. Establish `e : c * (x + y) - f (b1 + b2) = (c * x - f b1) + (c * y - f b2)`.

Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_mem h1 h2`. Consider the case `smul d x _ hx`.

Introduce `c`. Take `⟨b, h⟩` from `hx (c * d)`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `h`.

Introduce `a`. Take `⟨b, hb⟩` from `ih a`. Take `⟨x, hx, k, hk, hxk⟩` from `Submodule.mem_sup.mp hb`. Take `⟨b2, hb2⟩` from `hspan x hx 1`. Use `⟨b + b2, ?_⟩` and prove the remaining obligations.

Establish `e : a - f (b + b2) = (1 * x - f b2) + k`. Rewrite using `[map_add, one_mul]`. Take the linear combination `-hxk`. Rewrite using `[e]`. Use `add_mem hb2 (Submodule.mem_sup_right hk)` and prove the remaining obligations.

Introduce `a`. Take `⟨b, hb⟩` from `key N a`. Use `⟨b, ?_⟩` and prove the remaining obligations. Establish `hle : J ^ N ⊔ K ≤ K`. Use `sup_le ?_ le_rfl` and prove the remaining obligations.

Rewrite using `[hJ, ← Ideal.map_pow]`. Conclude with `hN`. Conclude with `hle hb`.
-/
theorem surj_mod_of_surj_mod_map_sup_of_pow_map_le :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (I : Ideal B) (K : Ideal A) (N : ℕ),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ I.map (algebraMap B A) ⊔ K) →
      (I ^ N).map (algebraMap B A) ≤ K → ∀ a : A, ∃ b : B, a - algebraMap B A b ∈ K := by
  intro B A _ _ _ I K N hsurj hN
  set f := algebraMap B A with hf
  set J := I.map f with hJ

  have key : ∀ n : ℕ, ∀ a : A, ∃ b : B, a - f b ∈ J ^ n ⊔ K := by
    intro n
    induction n with
    | zero =>
      intro a
      exact ⟨0, by simp⟩
    | succ n ih =>

      have hspan : ∀ x ∈ J ^ n, ∀ c : A, ∃ b : B, c * x - f b ∈ J ^ (n + 1) ⊔ K := by
        intro x hx
        rw [hJ, ← Ideal.map_pow] at hx
        unfold Ideal.map at hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨i, hi, rfl⟩ := hx
          intro c
          obtain ⟨b', hb'⟩ := hsurj c
          obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hb'
          refine ⟨b' * i, ?_⟩
          have hfi : f i ∈ J ^ n := by
            rw [hJ, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hi
          have hc : c = f b' + y + z := by rw [add_assoc, hyz]; ring
          have e : c * f i - f (b' * i) = f i * y + z * f i := by
            rw [hc, map_mul]; ring
          rw [e]
          refine Submodule.add_mem_sup ?_ (K.mul_mem_right _ hz)
          rw [pow_succ]
          exact Ideal.mul_mem_mul hfi hy
        | zero =>
          intro c; exact ⟨0, by simp⟩
        | add x y _ _ hx hy =>
          intro c
          obtain ⟨b1, h1⟩ := hx c
          obtain ⟨b2, h2⟩ := hy c
          refine ⟨b1 + b2, ?_⟩
          have e : c * (x + y) - f (b1 + b2) = (c * x - f b1) + (c * y - f b2) := by
            rw [map_add]; ring
          rw [e]; exact add_mem h1 h2
        | smul d x _ hx =>
          intro c
          obtain ⟨b, h⟩ := hx (c * d)
          refine ⟨b, ?_⟩
          rw [smul_eq_mul, ← mul_assoc]; exact h
      intro a
      obtain ⟨b, hb⟩ := ih a
      obtain ⟨x, hx, k, hk, hxk⟩ := Submodule.mem_sup.mp hb
      obtain ⟨b2, hb2⟩ := hspan x hx 1
      refine ⟨b + b2, ?_⟩
      have e : a - f (b + b2) = (1 * x - f b2) + k := by
        rw [map_add, one_mul]; linear_combination -hxk
      rw [e]
      refine add_mem hb2 (Submodule.mem_sup_right hk)
  intro a
  obtain ⟨b, hb⟩ := key N a
  refine ⟨b, ?_⟩
  have hle : J ^ N ⊔ K ≤ K := by
    refine sup_le ?_ le_rfl
    rw [hJ, ← Ideal.map_pow]; exact hN
  exact hle hb

end GlobalTheory
