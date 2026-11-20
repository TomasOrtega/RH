import Mathlib

namespace GlobalTheory

open Module in

/- English proof (translation)
Introduce `X _ _ _ k hk`. Use `set n := Module.finrank ℤ X`. Set `b : Basis (Fin n) ℤ X` to `Module.finBasis ℤ X`. Establish `hk0 : (k : ℤ) ≠ 0` using `by exact_mod_cast (by omega : k ≠ 0)`. Establish `hkpos : (0 : ℤ) < k` using `by exact_mod_cast (by omega : 0 < k)`.

Establish `coord : ∀ (x y : X) (j : Fin n), b.repr (x + k • y) j = b.repr x j + k * b.repr y j`. Introduce `x y j`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℤ]`. Simplify using the standard rewrite rules. Use `⟨fun x y h => ?_, ?_⟩` and prove the remaining obligations.

Apply `b.ext_elem` to reduce the goal to its premises. Introduce `j`. Establish `hj : b.repr (0 + k • x) j = b.repr (0 + k • y) j` using `by rw [h]`. Rewrite `hj` using `[coord, coord]`. Simplify using `only [map_zero, Finsupp.zero_apply, zero_add] at hj`.

Conclude with `mul_left_cancel₀ hk0 hj`. Set `d : Fin (k ^ n) → Fin n → ℤ` to `fun i j => ((finFunctionFinEquiv.symm i j : ℕ) : ℤ)`. Use `⟨fun i => ∑ j, d i j • b j, fun χ => ?_⟩` and prove the remaining obligations. Establish `rep : ∀ i j, b.repr (∑ j', d i j' • b j') j = d i j`. Introduce `i j`.

Rewrite using `[b.repr_sum_self]`. Set `r : Fin n → Fin k` to `fun j => ⟨(b.repr χ j % k).toNat, by`. Establish `h1` using `Int.emod_nonneg (b.repr χ j) hk0`. Establish `h2` using `Int.emod_lt_of_pos (b.repr χ j) hkpos`. Use the proof step `omega⟩`.

Use `⟨finFunctionFinEquiv r, ⟨∑ j, (b.repr χ j / k) • b j, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `b.ext_elem` to reduce the goal to its premises. Introduce `j`. Rewrite using `[coord, rep, b.repr_sum_self]`. Simplify using `only [d, Equiv.symm_apply_apply, r]`.

Establish `h1` using `Int.emod_nonneg (b.repr χ j) hk0`. Rewrite using `[Int.toNat_of_nonneg h1, Int.emod_def]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `i ⟨m, hm⟩`. Apply `finFunctionFinEquiv.symm.injective` to reduce the goal to its premises.

Rewrite using `[Equiv.symm_apply_apply]`. Use function extensionality and compare the values at `j`. Establish `h : b.repr χ j = b.repr (∑ j', d i j' • b j' + k • m) j` using `by rw [hm]`. Rewrite `h` using `[coord, rep]`. Establish `hd : d i j < k` using `by show ((finFunctionFinEquiv.symm i j : ℕ) : ℤ) < k`.

Conclude with `(finFunctionFinEquiv.symm i j).isLt` after adjusting the coercions. Establish `hd0 : 0 ≤ d i j` using `Int.natCast_nonneg _`. Establish `hmod : b.repr χ j % k = d i j`. Rewrite using `[h, Int.add_mul_emod_self_left]`. Conclude with `Int.emod_eq_of_lt hd0 hd`.

Apply `Fin.ext` to reduce the goal to its premises. Use `show (finFunctionFinEquiv.symm i j : ℕ) = (b.repr χ j % k).toNat`. Rewrite using `[hmod]`. Conclude with `(Int.toNat_natCast _).symm`.
-/
theorem _root_.GlobalTheory.exists_representatives_mod_nsmul : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ), 1 ≤ k → (∀ a b : X, k • a = k • b → a = b) ∧ ∃ e : Fin (k ^ Module.finrank ℤ X) → X, ∀ χ : X, ∃! i, ∃ m : X, χ = e i + k • m := by
  intro X _ _ _ k hk
  classical
  set n := Module.finrank ℤ X
  let b : Basis (Fin n) ℤ X := Module.finBasis ℤ X
  have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hkpos : (0 : ℤ) < k := by exact_mod_cast (by omega : 0 < k)
  have coord : ∀ (x y : X) (j : Fin n), b.repr (x + k • y) j = b.repr x j + k * b.repr y j := by
    intro x y j
    rw [← Nat.cast_smul_eq_nsmul ℤ]
    simp
  refine ⟨fun x y h => ?_, ?_⟩
  · apply b.ext_elem
    intro j
    have hj : b.repr (0 + k • x) j = b.repr (0 + k • y) j := by rw [h]
    rw [coord, coord] at hj
    simp only [map_zero, Finsupp.zero_apply, zero_add] at hj
    exact mul_left_cancel₀ hk0 hj
  let d : Fin (k ^ n) → Fin n → ℤ := fun i j => ((finFunctionFinEquiv.symm i j : ℕ) : ℤ)
  refine ⟨fun i => ∑ j, d i j • b j, fun χ => ?_⟩
  have rep : ∀ i j, b.repr (∑ j', d i j' • b j') j = d i j := by
    intro i j
    rw [b.repr_sum_self]
  let r : Fin n → Fin k := fun j => ⟨(b.repr χ j % k).toNat, by
    have h1 := Int.emod_nonneg (b.repr χ j) hk0
    have h2 := Int.emod_lt_of_pos (b.repr χ j) hkpos
    omega⟩
  refine ⟨finFunctionFinEquiv r, ⟨∑ j, (b.repr χ j / k) • b j, ?_⟩, ?_⟩
  · apply b.ext_elem
    intro j
    rw [coord, rep, b.repr_sum_self]
    simp only [d, Equiv.symm_apply_apply, r]
    have h1 := Int.emod_nonneg (b.repr χ j) hk0
    rw [Int.toNat_of_nonneg h1, Int.emod_def]
    ring
  · rintro i ⟨m, hm⟩
    apply finFunctionFinEquiv.symm.injective
    rw [Equiv.symm_apply_apply]
    funext j
    have h : b.repr χ j = b.repr (∑ j', d i j' • b j' + k • m) j := by rw [hm]
    rw [coord, rep] at h
    have hd : d i j < k := by
      show ((finFunctionFinEquiv.symm i j : ℕ) : ℤ) < k
      exact_mod_cast (finFunctionFinEquiv.symm i j).isLt
    have hd0 : 0 ≤ d i j := Int.natCast_nonneg _
    have hmod : b.repr χ j % k = d i j := by
      rw [h, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt hd0 hd
    apply Fin.ext
    show (finFunctionFinEquiv.symm i j : ℕ) = (b.repr χ j % k).toNat
    rw [hmod]
    exact (Int.toNat_natCast _).symm

end GlobalTheory
