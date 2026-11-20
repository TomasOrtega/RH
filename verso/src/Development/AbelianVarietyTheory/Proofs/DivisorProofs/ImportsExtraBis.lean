import Mathlib

open FractionalIdeal nonZeroDivisors

namespace GlobalTheory.ClosingLemma

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hSle : ∀ c : S, A.valuation (algebraMap S Ω c) ≤ 1` using `fun c => (A.valuation_le_one_iff _).2 (hS c)`. Set `M : Submodule S Ω` to `{ carrier := {z | A.valuation z < 1} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`.

Conclude with `Valuation.map_add_lt _ ha hb`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := by`. Introduce `c z hz`. Simplify using `only [Set.mem_setOf_eq, Algebra.smul_def, map_mul] at hz ⊢`.

Combine the equalities or inequalities in the displayed calculation. Set `N : Submodule S Ω` to `{ carrier := {z | A.valuation z ≤ 1} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Conclude with `(Valuation.map_add _ _ _).trans (max_le ha hb)`. Use the proof step `zero_mem' := by simp`.

Use the proof step `smul_mem' := by`. Introduce `c z hz`. Simplify using `only [Set.mem_setOf_eq, Algebra.smul_def, map_mul] at hz ⊢`. Combine the equalities or inequalities in the displayed calculation. Set `J : FractionalIdeal S⁰ Ω` to `1 + spanSingleton S⁰ x`.

Establish `hJ1 : (1 : FractionalIdeal S⁰ Ω) ≤ J` using `by show (1 : FractionalIdeal S⁰ Ω) ≤ 1 + spanSingleton S⁰ x`. Rewrite using `[← sup_eq_add]`. Conclude with `le_sup_left`. Establish `hJ0 : J ≠ 0`. Introduce `h`.

Rewrite `hJ1` using `[h]`. Conclude with `one_ne_zero (le_antisymm hJ1 (zero_le _))`. Establish `hJN : (J : Submodule S Ω) ≤ N`. Simplify using `only [J, coe_add, coe_one, coe_spanSingleton]`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Introduce `z hz`. Take `⟨c, rfl⟩` from `Submodule.mem_one.1 hz`. Conclude with `hSle c`. Rewrite using `[Submodule.span_le]`. Introduce `z hz`.

Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality. Conclude with `(A.valuation_le_one_iff _).2 hx`. Establish `hinv : ((J⁻¹ : FractionalIdeal S⁰ Ω) : Submodule S Ω) ≤ M`. Introduce `y hy`.

Establish `hy'` using `(mem_inv_iff hJ0).1 hy`. Take `⟨s, hs⟩` from `(mem_one_iff S⁰).1 (by simpa using hy' 1 (hJ1 (one_mem_one _)))`. Establish `hxJ : x ∈ J` using `by show x ∈ (J : Submodule S Ω)`. Simplify using `only [J, coe_add, coe_one, coe_spanSingleton]`. Conclude with `Submodule.mem_sup_right (Submodule.subset_span rfl)`.

Take `⟨t, ht⟩` from `(mem_one_iff S⁰).1 (hy' x hxJ)`. Use `show A.valuation y < 1`. Rewrite `ht`, the goal using `[← hs]`. Conclude with `lt_of_le_of_ne (hSle s) (fun h => hcon s t h ht.symm)`. Establish `hmul : ((J * J⁻¹ : FractionalIdeal S⁰ Ω) : Submodule S Ω) ≤ M`.

Rewrite using `[coe_mul, Submodule.mul_le]`. Introduce `z hz y hy`. Use `show A.valuation (z * y) < 1`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `hmul` using `[mul_inv_cancel₀ hJ0, coe_one]`. Use `hmul (Submodule.one_le.1 le_rfl)` as an intermediate fact. Conclude with `absurd this (by show ¬ A.valuation 1 < 1; simp)`.
-/
theorem main {Ω : Type} [Field Ω] (S : Type) [CommRing S] [IsDomain S] [IsDedekindDomain S]
    [Algebra S Ω] [IsFractionRing S Ω] (A : ValuationSubring Ω)
    (hS : ∀ s : S, algebraMap S Ω s ∈ A) {x : Ω} (hx : x ∈ A) :
    ∃ s t : S, A.valuation (algebraMap S Ω s) = 1 ∧ algebraMap S Ω s * x = algebraMap S Ω t := by
  by_contra hcon
  push_neg at hcon
  have hSle : ∀ c : S, A.valuation (algebraMap S Ω c) ≤ 1 := fun c => (A.valuation_le_one_iff _).2 (hS c)
  let M : Submodule S Ω :=
    { carrier := {z | A.valuation z < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq, Algebra.smul_def, map_mul] at hz ⊢
        calc A.valuation (algebraMap S Ω c) * A.valuation z ≤ 1 * A.valuation z := by
              gcongr; exact hSle c
          _ < 1 := by simpa using hz }
  let N : Submodule S Ω :=
    { carrier := {z | A.valuation z ≤ 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq, Algebra.smul_def, map_mul] at hz ⊢
        calc A.valuation (algebraMap S Ω c) * A.valuation z ≤ 1 * 1 := by
              gcongr; exact hSle c
          _ = 1 := one_mul 1 }
  let J : FractionalIdeal S⁰ Ω := 1 + spanSingleton S⁰ x
  have hJ1 : (1 : FractionalIdeal S⁰ Ω) ≤ J := by
    show (1 : FractionalIdeal S⁰ Ω) ≤ 1 + spanSingleton S⁰ x
    rw [← sup_eq_add]; exact le_sup_left
  have hJ0 : J ≠ 0 := by
    intro h
    rw [h] at hJ1
    exact one_ne_zero (le_antisymm hJ1 (zero_le _))
  have hJN : (J : Submodule S Ω) ≤ N := by
    simp only [J, coe_add, coe_one, coe_spanSingleton]
    refine sup_le ?_ ?_
    · intro z hz
      obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hz
      exact hSle c
    · rw [Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (A.valuation_le_one_iff _).2 hx
  have hinv : ((J⁻¹ : FractionalIdeal S⁰ Ω) : Submodule S Ω) ≤ M := by
    intro y hy
    have hy' := (mem_inv_iff hJ0).1 hy
    obtain ⟨s, hs⟩ := (mem_one_iff S⁰).1 (by simpa using hy' 1 (hJ1 (one_mem_one _)))
    have hxJ : x ∈ J := by
      show x ∈ (J : Submodule S Ω)
      simp only [J, coe_add, coe_one, coe_spanSingleton]
      exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    obtain ⟨t, ht⟩ := (mem_one_iff S⁰).1 (hy' x hxJ)
    show A.valuation y < 1
    rw [← hs] at ht ⊢
    exact lt_of_le_of_ne (hSle s) (fun h => hcon s t h ht.symm)
  have hmul : ((J * J⁻¹ : FractionalIdeal S⁰ Ω) : Submodule S Ω) ≤ M := by
    rw [coe_mul, Submodule.mul_le]
    intro z hz y hy
    show A.valuation (z * y) < 1
    rw [map_mul]
    calc A.valuation z * A.valuation y ≤ 1 * A.valuation y := by gcongr; exact hJN hz
      _ < 1 := by rw [one_mul]; exact hinv hy
  rw [mul_inv_cancel₀ hJ0, coe_one] at hmul
  have := hmul (Submodule.one_le.1 le_rfl)
  exact absurd this (by show ¬ A.valuation 1 < 1; simp)

end GlobalTheory.ClosingLemma
