import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSpanStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ Ω _ y a q w hy hw hgen`. Take `⟨n₀, hn₀⟩` from `hS K ι Ω y a q w hy hw hgen`. Use `choose G hG using fun m : ℕ => hL K ι Ω y a m hy`. Use `set P : Finset (ℕ × Ω) := (Finset.range (n₀ + 1)).biUnion fun m => (G m).image fun g => (m, g) with hP`. Establish `memP : ∀ m g, m ≤ n₀ → g ∈ G m → (m, g) ∈ P`.

Introduce `m g hm hg`. Rewrite using `[hP, Finset.mem_biUnion]`. Conclude with `⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hm), Finset.mem_image.2 ⟨g, hg, rfl⟩⟩`. Establish `ofP : ∀ x ∈ P, x.2 ∈ chartLat y a x.1`. Introduce `x hx`.

Rewrite `hx` using `[hP, Finset.mem_biUnion]`. Take `⟨m, _, hx⟩` from `hx`. Take `⟨g, hg, rfl⟩` from `Finset.mem_image.1 hx`. Rewrite using `[← hG m]`. Conclude with `AddSubgroup.subset_closure hg`.

Set `f : Fin P.card → ℕ × Ω` to `fun i => (P.equivFin.symm i).1`. Set `T : ℕ → Set Ω` to `fun n => {s | ∃ (i : Fin P.card) (μ : Fin q → ℕ), (f i).1 + ∑ j, μ j = n ∧ s = (f i).2 * ∏ j, w j ^ μ j}`. Establish `base : ∀ n, n ≤ n₀ → chartLat y a n ≤ AddSubgroup.closure (T n)`. Introduce `n hn`. Rewrite using `[← hG n, AddSubgroup.closure_le]`.

Introduce `g hg`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Apply the tactic sequence `refine ⟨P.equivFin ⟨(n, g), memP n g hn hg⟩, 0, ?_, ?_⟩ <;> simp [f]`. Establish `step : ∀ n (j : Fin q), ∀ s ∈ AddSubgroup.closure (T n), s * w j ∈ AddSubgroup.closure (T (n + 1))`. Introduce `n j s hs`.

Proceed by induction on `hs using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨i, μ, hdeg, rfl⟩` from `hx`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Use `⟨i, μ + Pi.single j 1, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [Pi.add_apply, Finset.sum_add_distrib]`. Rewrite using `[← hdeg, Finset.sum_pi_single']`. Simplify using `[add_assoc]`. Establish `hprod : ∏ k, w k ^ ((μ + Pi.single j 1 : Fin q → ℕ) k) = (∏ k, w k ^ μ k) * w j`. Simplify using `only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]`.

Use `congr 1`. Rewrite using `[Fintype.prod_eq_single j]`. Simplify using the standard rewrite rules. Introduce `k hk`. Simplify using `[hk]`.

Rewrite using `[hprod, mul_assoc]`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [add_mul]`. Conclude with `add_mem hx hz`. Consider the case `neg x _ hx => rw [neg_mul]`.

Conclude with `neg_mem hx`. Use `⟨P.card, fun i => (f i).1, fun i => (f i).2, fun i => ofP _ (P.equivFin.symm i).2, ?_⟩` and prove the remaining obligations. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact base 0 (Nat.zero_le _)`.

Consider the case `succ n ih`. Distinguish the cases in `h : n + 1 ≤ n₀`. Conclude with `base _ h`. Establish `hn : n₀ ≤ n` using `by omega`. Use `(hn₀ n hn).trans ?_` and prove the remaining obligations.

Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `t ⟨s, hs, j, rfl⟩`. Conclude with `step n j s (ih hs)`.
-/
theorem SectionRingFinite.proof (hL : SectionLatticeFinite.Statement) (hS : SectionSpanStep.Statement) :
    SectionRingFinite.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  classical
  obtain ⟨n₀, hn₀⟩ := hS K ι Ω y a q w hy hw hgen
  choose G hG using fun m : ℕ => hL K ι Ω y a m hy
  set P : Finset (ℕ × Ω) :=
    (Finset.range (n₀ + 1)).biUnion fun m => (G m).image fun g => (m, g) with hP
  have memP : ∀ m g, m ≤ n₀ → g ∈ G m → (m, g) ∈ P := by
    intro m g hm hg
    rw [hP, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.2 (Nat.lt_succ_of_le hm), Finset.mem_image.2 ⟨g, hg, rfl⟩⟩
  have ofP : ∀ x ∈ P, x.2 ∈ chartLat y a x.1 := by
    intro x hx
    rw [hP, Finset.mem_biUnion] at hx
    obtain ⟨m, _, hx⟩ := hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    rw [← hG m]
    exact AddSubgroup.subset_closure hg
  let f : Fin P.card → ℕ × Ω := fun i => (P.equivFin.symm i).1
  let T : ℕ → Set Ω := fun n =>
    {s | ∃ (i : Fin P.card) (μ : Fin q → ℕ), (f i).1 + ∑ j, μ j = n ∧ s = (f i).2 * ∏ j, w j ^ μ j}
  have base : ∀ n, n ≤ n₀ → chartLat y a n ≤ AddSubgroup.closure (T n) := by
    intro n hn
    rw [← hG n, AddSubgroup.closure_le]
    intro g hg
    apply AddSubgroup.subset_closure
    refine ⟨P.equivFin ⟨(n, g), memP n g hn hg⟩, 0, ?_, ?_⟩ <;> simp [f]
  have step : ∀ n (j : Fin q), ∀ s ∈ AddSubgroup.closure (T n),
      s * w j ∈ AddSubgroup.closure (T (n + 1)) := by
    intro n j s hs
    induction hs using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, μ, hdeg, rfl⟩ := hx
      apply AddSubgroup.subset_closure
      refine ⟨i, μ + Pi.single j 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib]
        rw [← hdeg, Finset.sum_pi_single']
        simp [add_assoc]
      · have hprod : ∏ k, w k ^ ((μ + Pi.single j 1 : Fin q → ℕ) k) = (∏ k, w k ^ μ k) * w j := by
          simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
          congr 1
          rw [Fintype.prod_eq_single j]
          · simp
          · intro k hk
            simp [hk]
        rw [hprod, mul_assoc]
    | zero => simp
    | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
    | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  refine ⟨P.card, fun i => (f i).1, fun i => (f i).2, fun i => ofP _ (P.equivFin.symm i).2, ?_⟩
  intro n
  induction n with
  | zero => exact base 0 (Nat.zero_le _)
  | succ n ih =>
    by_cases h : n + 1 ≤ n₀
    · exact base _ h
    · have hn : n₀ ≤ n := by omega
      refine (hn₀ n hn).trans ?_
      rw [AddSubgroup.closure_le]
      rintro t ⟨s, hs, j, rfl⟩
      exact step n j s (ih hs)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
