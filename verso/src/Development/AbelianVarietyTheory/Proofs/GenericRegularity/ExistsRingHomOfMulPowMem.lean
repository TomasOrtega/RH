import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨s, hs⟩` from `hA`. Establish `hden : ∀ x : Ω, ∃ b ∈ B, b ≠ 0 ∧ x * b ∈ B`. Introduce `x`. Take `⟨a, ha, b, hb, hb0, hx⟩` from `hB x`. Conclude with `⟨b, hb, hb0, by rw [hx]; exact ha⟩`.

Use `choose den hdenB hden0 hdenmul using hden`. Establish `hD : ∏ x ∈ s, den x ∈ B` using `Subalgebra.prod_mem B (fun x _ => hdenB x)`. Use `⟨∏ x ∈ s, den x, hD, Finset.prod_ne_zero_iff.mpr (fun x _ => hden0 x), ?_⟩` and prove the remaining obligations. Introduce `a ha`. Rewrite `ha` using `[← hs]`.

Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, ← Finset.mul_prod_erase s den (Finset.mem_coe.mp hx), ← mul_assoc]`. Conclude with `mul_mem (hdenmul x) (Subalgebra.prod_mem B (fun y _ => hdenB y))`.

Consider the case `algebraMap r`. Conclude with `⟨0, by rw [pow_zero, mul_one]; exact B.algebraMap_mem r⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨n, hn⟩` from `hx`. Take `⟨m, hm⟩` from `hy`.

Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `e : (x + y) * (∏ z ∈ s, den z) ^ (n + m) = x * (∏ z ∈ s, den z) ^ n * (∏ z ∈ s, den z) ^ m + y * (∏ z ∈ s, den z) ^ m * (∏ z ∈ s, den z) ^ n` using `by ring`. Rewrite using `[e]`. Conclude with `add_mem (mul_mem hn (pow_mem hD m)) (mul_mem hm (pow_mem hD n))`. Consider the case `mul x y _ _ hx hy`.

Take `⟨n, hn⟩` from `hx`. Take `⟨m, hm⟩` from `hy`. Use `⟨n + m, ?_⟩` and prove the remaining obligations. Establish `e : x * y * (∏ z ∈ s, den z) ^ (n + m) = (x * (∏ z ∈ s, den z) ^ n) * (y * (∏ z ∈ s, den z) ^ m)` using `by ring`. Rewrite using `[e]`.

Conclude with `mul_mem hn hm`.
-/
theorem exists_mul_pow_mem_of_fg {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    (A B : Subalgebra O Ω) (hA : A.FG)
    (hB : ∀ x : Ω, ∃ a ∈ B, ∃ b ∈ B, b ≠ 0 ∧ x * b = a) :
    ∃ d ∈ B, d ≠ 0 ∧ ∀ a ∈ A, ∃ n : ℕ, a * d ^ n ∈ B := by
  classical
  obtain ⟨s, hs⟩ := hA
  have hden : ∀ x : Ω, ∃ b ∈ B, b ≠ 0 ∧ x * b ∈ B := by
    intro x
    obtain ⟨a, ha, b, hb, hb0, hx⟩ := hB x
    exact ⟨b, hb, hb0, by rw [hx]; exact ha⟩
  choose den hdenB hden0 hdenmul using hden
  have hD : ∏ x ∈ s, den x ∈ B := Subalgebra.prod_mem B (fun x _ => hdenB x)
  refine ⟨∏ x ∈ s, den x, hD, Finset.prod_ne_zero_iff.mpr (fun x _ => hden0 x), ?_⟩
  intro a ha
  rw [← hs] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>

    refine ⟨1, ?_⟩
    rw [pow_one, ← Finset.mul_prod_erase s den (Finset.mem_coe.mp hx), ← mul_assoc]
    exact mul_mem (hdenmul x) (Subalgebra.prod_mem B (fun y _ => hdenB y))
  | algebraMap r =>
    exact ⟨0, by rw [pow_zero, mul_one]; exact B.algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have e : (x + y) * (∏ z ∈ s, den z) ^ (n + m) =
        x * (∏ z ∈ s, den z) ^ n * (∏ z ∈ s, den z) ^ m +
          y * (∏ z ∈ s, den z) ^ m * (∏ z ∈ s, den z) ^ n := by ring
    rw [e]
    exact add_mem (mul_mem hn (pow_mem hD m)) (mul_mem hm (pow_mem hD n))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have e : x * y * (∏ z ∈ s, den z) ^ (n + m) =
        (x * (∏ z ∈ s, den z) ^ n) * (y * (∏ z ∈ s, den z) ^ m) := by ring
    rw [e]
    exact mul_mem hn hm

end GlobalTheory
