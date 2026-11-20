import Mathlib

namespace GlobalTheory.ExistsSmulMemLattice

open NumberField

/- English proof (translation)
Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨d₁, hd₁, h₁⟩` from `hx`.

Take `⟨d₂, hd₂, h₂⟩` from `hy`. Use `⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `M.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `M.smul_mem _ h₁`. Rewrite using `[mul_smul]`. Conclude with `M.smul_mem _ h₂`. Consider the case `smul a x _ hx`. Take `⟨d, hd, h⟩` from `hx`.

Take `⟨⟨n, s⟩, hs⟩` from `IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) a`. Establish `hs0 : (s : RingOfIntegers K) ≠ 0` using `nonZeroDivisors.coe_ne_zero s`. Use `⟨(s : RingOfIntegers K) * d, mul_ne_zero hs0 hd, ?_⟩` and prove the remaining obligations. Establish `key : ((s : RingOfIntegers K) * d) • (a • x) = n • (d • x)`. Rewrite using `[← algebraMap_smul K ((s : RingOfIntegers K) * d), ← algebraMap_smul K n (d • x), ← algebraMap_smul K d x, smul_smul, smul_smul, map_mul]`.

Use `congr 1`. Simplify using `only at hs`. Rewrite using `[← hs]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Conclude with `M.smul_mem _ h`.
-/
theorem exists_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    {M : Submodule (RingOfIntegers K) V} {v : V} (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul a x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) a
    have hs0 : (s : RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    refine ⟨(s : RingOfIntegers K) * d, mul_ne_zero hs0 hd, ?_⟩
    have key : ((s : RingOfIntegers K) * d) • (a • x) = n • (d • x) := by
      rw [← algebraMap_smul K ((s : RingOfIntegers K) * d), ← algebraMap_smul K n (d • x),
        ← algebraMap_smul K d x, smul_smul, smul_smul, map_mul]
      congr 1
      simp only at hs
      rw [← hs]; ring
    rw [key]; exact M.smul_mem _ h

end GlobalTheory.ExistsSmulMemLattice
