import Mathlib
open Polynomial

namespace GlobalTheory.CompanionTheory.KillSum

/- English proof (translation)
Proceed by induction on `P using Multiset.induction_on with`. Consider the case `empty => exact ⟨0, by simp⟩`. Consider the case `cons a s ih`. Take `⟨q, hq⟩` from `ih`. Use `⟨(s.map f).prod + f a * q + w * q, ?_⟩` and prove the remaining obligations.

Simplify using `only [Multiset.map_cons, Multiset.prod_cons, hq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_map_add_eq {R α : Type*} [CommRing R] (P : Multiset α) (f : α → R) (w : R) :
    ∃ q, (P.map fun a => f a + w).prod = (P.map f).prod + w * q := by
  induction P using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons a s ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(s.map f).prod + f a * q + w * q, ?_⟩
    simp only [Multiset.map_cons, Multiset.prod_cons, hq]
    ring

/- English proof (translation)
Establish `key : ∀ b : ℂ, ∃ q, (P.map fun a => (x + y) - algebraMap ℂ R (a + b)).prod = (y - algebraMap ℂ R b) * q`. Introduce `b`. Take `⟨q, hq⟩` from `prod_map_add_eq P (fun c => x - algebraMap ℂ R c) (y - algebraMap ℂ R b)`. Use `⟨q, ?_⟩` and prove the remaining obligations. Rewrite `hq` using `[hP, zero_add]`.

Rewrite using `[← hq]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises. Introduce `a _`. Simplify using `only [map_add]`.

Expand and normalize the polynomial expressions, which then agree. Use `choose q hq using key`. Rewrite using `[Multiset.map_bind, Multiset.prod_bind]`. Simplify using `only [Multiset.map_map, Function.comp_def]`. Simplify using `only [hq]`.

Rewrite using `[Multiset.prod_map_mul, hQ, zero_mul]`.
-/
theorem add_killed {R : Type*} [CommRing R] [Algebra ℂ R] (x y : R) (P Q : Multiset ℂ)
    (hP : (P.map fun c => x - algebraMap ℂ R c).prod = 0)
    (hQ : (Q.map fun c => y - algebraMap ℂ R c).prod = 0) :
    ((Q.bind fun b => P.map fun a => a + b).map fun c => (x + y) - algebraMap ℂ R c).prod = 0 := by
  have key : ∀ b : ℂ, ∃ q, (P.map fun a => (x + y) - algebraMap ℂ R (a + b)).prod
      = (y - algebraMap ℂ R b) * q := by
    intro b
    obtain ⟨q, hq⟩ := prod_map_add_eq P (fun c => x - algebraMap ℂ R c) (y - algebraMap ℂ R b)
    refine ⟨q, ?_⟩
    rw [hP, zero_add] at hq
    rw [← hq]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp only [map_add]
    ring
  choose q hq using key
  rw [Multiset.map_bind, Multiset.prod_bind]
  simp only [Multiset.map_map, Function.comp_def]
  simp only [hq]
  rw [Multiset.prod_map_mul, hQ, zero_mul]

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact ⟨{0}, by simp, fun R _ _ h _ => by simp⟩`. Consider the case `insert τ s hτ ih`. Take `⟨l0, hc, hk⟩` from `ih`. Use `⟨l0.bind fun b => (l τ).map fun a => a + b, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.prod_insert hτ, ← hc]`. Simplify using `[Multiset.card_bind, mul_comm]`. Introduce `R _ _ h hh`. Rewrite using `[Finset.sum_insert hτ]`. Conclude with `add_killed _ _ _ _ (hh τ (Finset.mem_insert_self _ _)) (hk R h fun t ht => hh t (Finset.mem_insert_of_mem ht))`.
-/
theorem sum_killed {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ) :
    ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨{0}, by simp, fun R _ _ h _ => by simp⟩
  | insert τ s hτ ih =>
    obtain ⟨l0, hc, hk⟩ := ih
    refine ⟨l0.bind fun b => (l τ).map fun a => a + b, ?_, ?_⟩
    · rw [Finset.prod_insert hτ, ← hc]
      simp [Multiset.card_bind, mul_comm]
    · intro R _ _ h hh
      rw [Finset.sum_insert hτ]
      exact add_killed _ _ _ _ (hh τ (Finset.mem_insert_self _ _))
        (hk R h fun t ht => hh t (Finset.mem_insert_of_mem ht))

end GlobalTheory.CompanionTheory.KillSum
