import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (translation)
Introduce `z z' q d hz hzz hq hd`. Establish `hhalf : ∀ t : ℝ, Real.exp t ^ (1 / 2 : ℝ) = Real.exp (t / 2)`. Introduce `t`. Rewrite using `[← Real.exp_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [primePairSetFirst, PPset, primeSetTwoBounds, mem_filter, mem_Icc, hhalf] at hq hd`. Take `⟨⟨_, hq2⟩, hqp, hqm, hqg⟩` from `hq`. Take `⟨⟨_, hd2⟩, hdp, hdm, hdv, hdg⟩` from `hd`. Establish `hq0 : (0 : ℝ) < q` using `by exact_mod_cast hqp.pos`.

Establish `hd0 : (0 : ℝ) < d` using `by exact_mod_cast hdp.pos`. Establish `hqle : (q : ℝ) ≤ Real.exp z` using `(Nat.le_floor_iff (Real.exp_pos z).le).1 hq2`. Establish `hdle : (d : ℝ) ≤ Real.exp z'` using `(Nat.le_floor_iff (Real.exp_pos z').le).1 hd2`. Use `⟨hqp, by omega, (Real.lt_log_iff_exp_lt hq0).2 hqg, (Real.log_le_iff_le_exp hq0).2 hqle, hdp, hdm, (Real.lt_log_iff_exp_lt hd0).2 hdg, (Real.log_le_iff_le_exp hd0).2 hdle, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : Real.exp z ≤ Real.exp (z' / 2)` using `Real.exp_le_exp.2 (by linarith)`.

Establish `h2 : (q : ℝ) < d` using `lt_of_le_of_lt (hqle.trans h1) hdg`. Conclude with `h2` after adjusting the coercions. Introduce `p hp hp2 hpz`. Apply `Nat.mod_eq_zero_of_dvd` to reduce the goal to its premises. Use `Dvd.dvd.trans ?_ hdv` and prove the remaining obligations.

Unfold `oddM`. Break down `hpz with h | h` into its components or cases. Use `Dvd.dvd.mul_left ?_ _` and prove the remaining obligations. Use `Finset.dvd_prod_of_mem (fun p : ℕ => p) ?_` and prove the remaining obligations. Rewrite using `[mem_filter, mem_Icc]`.

Establish `h2` using `hp.two_le`. Conclude with `⟨⟨by omega, Nat.le_floor h⟩, hp⟩`. Rewrite using `[h]`. Conclude with `Dvd.intro _ rfl`.
-/
theorem rows_of_mem :
    ∀ (z z' : ℝ) (q d : ℕ), 0 < z → 2 * z ≤ z' → q ∈ primePairSetFirst z → d ∈ primeSetTwoBounds z z' q → Rows z z' q d := by
  intro z z' q d hz hzz hq hd
  have hhalf : ∀ t : ℝ, Real.exp t ^ (1 / 2 : ℝ) = Real.exp (t / 2) := by
    intro t
    rw [← Real.exp_mul]
    congr 1
    ring
  simp only [primePairSetFirst, PPset, primeSetTwoBounds, mem_filter, mem_Icc, hhalf] at hq hd
  obtain ⟨⟨_, hq2⟩, hqp, hqm, hqg⟩ := hq
  obtain ⟨⟨_, hd2⟩, hdp, hdm, hdv, hdg⟩ := hd
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hdp.pos
  have hqle : (q : ℝ) ≤ Real.exp z := (Nat.le_floor_iff (Real.exp_pos z).le).1 hq2
  have hdle : (d : ℝ) ≤ Real.exp z' := (Nat.le_floor_iff (Real.exp_pos z').le).1 hd2
  refine ⟨hqp, by omega, (Real.lt_log_iff_exp_lt hq0).2 hqg, (Real.log_le_iff_le_exp hq0).2 hqle,
    hdp, hdm, (Real.lt_log_iff_exp_lt hd0).2 hdg, (Real.log_le_iff_le_exp hd0).2 hdle, ?_, ?_⟩
  · have h1 : Real.exp z ≤ Real.exp (z' / 2) := Real.exp_le_exp.2 (by linarith)
    have h2 : (q : ℝ) < d := lt_of_le_of_lt (hqle.trans h1) hdg
    exact_mod_cast h2
  · intro p hp hp2 hpz
    apply Nat.mod_eq_zero_of_dvd
    refine Dvd.dvd.trans ?_ hdv
    unfold oddM
    rcases hpz with h | h
    · refine Dvd.dvd.mul_left ?_ _
      refine Finset.dvd_prod_of_mem (fun p : ℕ => p) ?_
      rw [mem_filter, mem_Icc]
      have h2 := hp.two_le
      exact ⟨⟨by omega, Nat.le_floor h⟩, hp⟩
    · rw [h]
      exact Dvd.intro _ rfl

end QH
