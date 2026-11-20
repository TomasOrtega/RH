import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Introduce `Ω K _ _ _ _ _ W x N hN hv`. Use `set p : Polynomial Ω := X ^ N - C 1 with hp`. Establish `hm : p.Monic` using `monic_X_pow_sub_C 1 hN.ne'`. Establish `hs` using `(IsAlgClosed.splits p).eq_prod_roots_of_monic hm`. Establish `hx : x ^ N - 1 = (p.roots.map (fun a => x - algebraMap Ω K a)).prod`.

Use `congrArg (Polynomial.aeval x) hs` as an intermediate fact. Simplify `this` using `[p, map_multiset_prod, Multiset.map_map, Function.comp_def]`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `(not_lt.mpr ?_) hv` and prove the remaining obligations.

Rewrite using `[hx, map_multiset_prod, Multiset.map_map]`. Use `Multiset.one_le_prod_of_one_le ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨a, ha, rfl⟩` from `Multiset.mem_map.mp hy`. Establish `ha' : a ^ N = 1`.

Use `(mem_roots hm.ne_zero).mp ha` as an intermediate fact. Simplify `this` using `[p, sub_eq_zero]`. Conclude with `hcon a ha'`.
-/
theorem exists_root_of_unity_close_of_pow_close : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K]
    [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 →
    ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := by
  intro Ω K _ _ _ _ _ W x N hN hv
  classical
  set p : Polynomial Ω := X ^ N - C 1 with hp
  have hm : p.Monic := monic_X_pow_sub_C 1 hN.ne'
  have hs := (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
  have hx : x ^ N - 1 = (p.roots.map (fun a => x - algebraMap Ω K a)).prod := by
    have := congrArg (Polynomial.aeval x) hs
    simpa [p, map_multiset_prod, Multiset.map_map, Function.comp_def] using this
  by_contra hcon
  push_neg at hcon
  refine (not_lt.mpr ?_) hv
  rw [hx, map_multiset_prod, Multiset.map_map]
  refine Multiset.one_le_prod_of_one_le ?_
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
  have ha' : a ^ N = 1 := by
    have := (mem_roots hm.ne_zero).mp ha
    simpa [p, sub_eq_zero] using this
  exact hcon a ha'

end GlobalTheory
