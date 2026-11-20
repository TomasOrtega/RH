import Mathlib

namespace GlobalTheory.SummableExpNegAbsSum

/- English proof (translation)
Establish `h : Summable fun n : ℕ ↦ Real.exp (-(n : ℝ))` using `Real.summable_exp_neg_nat`. Use `Summable.of_nat_of_neg ?_ ?_` and prove the remaining obligations. Simplify using `using h`. Simplify using `using h`.
-/
theorem summable_int : Summable fun n : ℤ ↦ Real.exp (-|(n : ℝ)|) := by
  have h : Summable fun n : ℕ ↦ Real.exp (-(n : ℝ)) := Real.summable_exp_neg_nat
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using h
  · simpa using h

/- English proof (translation)
Use `set g : ℤ → ℝ := fun n ↦ Real.exp (-|(n : ℝ)|) with hg`. Establish `hgpos : ∀ n, 0 ≤ g n` using `fun n => (Real.exp_pos _).le`. Establish `hgs : Summable g` using `summable_int`. Establish `hprod : ∀ m : ι → ℤ, Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) = ∏ i : ι, g (m i)`. Introduce `m`.

Simplify using `only [hg]`. Rewrite using `[← Real.exp_sum, Finset.sum_neg_distrib]`. Repeatedly rewrite using `[hprod]`. Use `summable_of_sum_le (c := ∏ _i : ι, ∑' n : ℤ, g n) (fun m => Finset.prod_nonneg fun i _ => hgpos _) fun s => ?_` and prove the remaining obligations. Use `set T : ι → Finset ℤ := fun i => s.image (fun m : ι → ℤ => m i) with hT`.

Establish `hsub : s ⊆ Fintype.piFinset T`. Introduce `m hm`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `i`. Conclude with `Finset.mem_image_of_mem _ hm`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => hgpos _) fun i _ => ?_` and prove the remaining obligations. Conclude with `hgs.sum_le_tsum _ fun _ _ => hgpos _`.
-/
theorem summable_exp_neg_sum_abs {ι : Type} [inst : Fintype ι] :
    Summable fun (m : ι → ℤ) ↦ Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) := by
  classical
  set g : ℤ → ℝ := fun n ↦ Real.exp (-|(n : ℝ)|) with hg
  have hgpos : ∀ n, 0 ≤ g n := fun n => (Real.exp_pos _).le
  have hgs : Summable g := summable_int
  have hprod : ∀ m : ι → ℤ, Real.exp (-∑ i : ι, |(↑(m i) : ℝ)|) = ∏ i : ι, g (m i) := by
    intro m
    simp only [hg]
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  simp_rw [hprod]
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' n : ℤ, g n)
    (fun m => Finset.prod_nonneg fun i _ => hgpos _) fun s => ?_
  set T : ι → Finset ℤ := fun i => s.image (fun m : ι → ℤ => m i) with hT
  have hsub : s ⊆ Fintype.piFinset T := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image_of_mem _ hm
  calc ∑ m ∈ s, ∏ i : ι, g (m i)
      ≤ ∑ m ∈ Fintype.piFinset T, ∏ i : ι, g (m i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
          Finset.prod_nonneg fun i _ => hgpos _
    _ = ∏ i : ι, ∑ n ∈ T i, g n := (Finset.prod_univ_sum T (fun _ n => g n)).symm
    _ ≤ ∏ _i : ι, ∑' n : ℤ, g n := by
        refine Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => hgpos _)
          fun i _ => ?_
        exact hgs.sum_le_tsum _ fun _ _ => hgpos _

end GlobalTheory.SummableExpNegAbsSum
