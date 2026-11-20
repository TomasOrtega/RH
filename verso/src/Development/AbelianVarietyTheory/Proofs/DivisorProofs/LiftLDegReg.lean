import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotModEqOfLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `q l L hq hl hL`. Proceed by induction on `L with`. Consider the case `nil => simp [liftL, deg]`. Consider the case `cons p L ih`. Establish `hL' : ∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2` using `fun p' hp' => hL p' (List.mem_cons_of_mem _ hp')`.

Take `⟨ihd, ihm⟩` from `ih hL'`. Take `⟨hp0, hpd, hpr⟩` from `hL p List.mem_cons_self`. Take `⟨c, hc⟩` from `hpd`. Establish `hc0 : 0 < c`. Break down `Nat.eq_zero_or_pos c with h | h` into its components or cases.

Substitute `h` using the available equality. Simplify using `at hc`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hdiv : p.1 / l = c` using `by rw [hc]; exact Nat.mul_div_cancel_left c hl`.

Establish `hcons : liftL q l (p :: L) = (List.range l).map (fun i => (p.1 / l, p.2 * q ^ i)) ++ liftL q l L`. Simplify using `[liftL, List.flatMap_cons]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hcons]`. Simplify using `only [deg, List.map_append, List.sum_append, List.map_map] at ihd ⊢`.

Rewrite using `[ihd]`. Simplify using `[Function.comp_def, List.sum_replicate, hdiv, hc, Nat.mul_div_cancel_left c hl]`. Introduce `p' hp'`. Rewrite `hp'` using `[hcons, List.mem_append]`. Break down `hp' with hp' | hp'` into its components or cases.

Take `⟨i, -, rfl⟩` from `List.mem_map.1 hp'`. Use `⟨by simpa [hdiv] using hc0, ?_⟩` and prove the remaining obligations. Simplify using `only [hdiv]`. Rewrite `hpr` using `[hc]`. Conclude with `(GlobalTheory.Shin.reg_step_of_dvd q l c p.2 hq hl hc0 hpr).1 i`.

Conclude with `ihm p' hp'`.
-/
theorem liftL_deg_reg : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → 0 < l →
    (∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2) →
    deg (liftL q l L) = deg L ∧ ∀ p ∈ liftL q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  intro q l L hq hl hL
  induction L with
  | nil => simp [liftL, deg]
  | cons p L ih =>
    have hL' : ∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2 := fun p' hp' => hL p' (List.mem_cons_of_mem _ hp')
    obtain ⟨ihd, ihm⟩ := ih hL'
    obtain ⟨hp0, hpd, hpr⟩ := hL p List.mem_cons_self
    obtain ⟨c, hc⟩ := hpd
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    have hdiv : p.1 / l = c := by rw [hc]; exact Nat.mul_div_cancel_left c hl
    have hcons : liftL q l (p :: L) = (List.range l).map (fun i => (p.1 / l, p.2 * q ^ i)) ++ liftL q l L := by
      simp [liftL, List.flatMap_cons]
    refine ⟨?_, ?_⟩
    · rw [hcons]
      simp only [deg, List.map_append, List.sum_append, List.map_map] at ihd ⊢
      rw [ihd]
      simp [Function.comp_def, List.sum_replicate, hdiv, hc, Nat.mul_div_cancel_left c hl]
    · intro p' hp'
      rw [hcons, List.mem_append] at hp'
      rcases hp' with hp' | hp'
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp'
        refine ⟨by simpa [hdiv] using hc0, ?_⟩
        simp only [hdiv]
        rw [hc] at hpr
        exact (GlobalTheory.Shin.reg_step_of_dvd q l c p.2 hq hl hc0 hpr).1 i
      · exact ihm p' hp'

end GlobalTheory.Shin
