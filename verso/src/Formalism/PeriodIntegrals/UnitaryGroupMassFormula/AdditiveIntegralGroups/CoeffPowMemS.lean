import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GuLine

noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Simplify using `only [IsWq] at h`. Establish `h1` using `congrArg PowerSeries.constantCoeff h`. Simplify using `using h1`.
-/
theorem wq_const {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.constantCoeff wq = 1 := by
  simp only [IsWq] at h
  have h1 := congrArg PowerSeries.constantCoeff h
  simpa using h1

/- English proof (translation)
Rewrite using `[PowerSeries.coeff_mul]`. Use `S.sum_mem fun x hx => S.mul_mem (hf _ ?_) (hg _ ?_)` and prove the remaining obligations. Use `Finset.HasAntidiagonal.mem_antidiagonal.mp hx` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `Finset.HasAntidiagonal.mem_antidiagonal.mp hx` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem coeff_mul_memS {S : Subring ℂ_[p]} {f g : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (hg : ∀ i ≤ m, PowerSeries.coeff i g ∈ S) :
    PowerSeries.coeff m (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun x hx => S.mul_mem (hf _ ?_) (hg _ ?_)
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `i _`. Rewrite using `[pow_zero, PowerSeries.coeff_one]`. Use `split_ifs`.

Conclude with `S.one_mem`. Conclude with `S.zero_mem`. Consider the case `succ k ih`. Introduce `i hi`. Rewrite using `[pow_succ]`.

Conclude with `coeff_mul_memS (fun j hj => ih j (hj.trans hi)) (fun j hj => hf j (hj.trans hi))`.
-/
theorem coeff_pow_memS {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (k : ℕ) : ∀ i ≤ m, PowerSeries.coeff i (f ^ k) ∈ S := by
  induction k with
  | zero =>
    intro i _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | succ k ih =>
    intro i hi
    rw [pow_succ]
    exact coeff_mul_memS (fun j hj => ih j (hj.trans hi)) (fun j hj => hf j (hj.trans hi))

/- English proof (translation)
Rewrite using `[mul_assoc, ← Algebra.smul_def, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_mul']`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coeff_termS (a : ℂ_[p]) (k n : ℕ) (f : PowerSeries ℂ_[p]) :
    PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * f) =
      if k ≤ n then a * PowerSeries.coeff (n - k) f else 0 := by
  rw [mul_assoc, ← Algebra.smul_def, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

/- English proof (translation)
Establish `t1 : ∀ (a : ℂ_[p]) (f : PowerSeries ℂ_[p]) (n : ℕ), PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X * f) = if 1 ≤ n then a * PowerSeries.coeff (n - 1) f else 0`. Introduce `a f n`. Rewrite using `[← coeff_termS, pow_one]`. Simplify using `only [IsWq] at h`. Introduce `n`.

Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Establish `hc` using `congrArg (PowerSeries.coeff n) h`. Rewrite using `[hc]`. Simplify using `only [map_add, t1, coeff_termS, PowerSeries.coeff_one]`.

Use `S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem ?_ ?_) ?_) ?_) ?_) ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `S.one_mem`. Conclude with `S.zero_mem`. Use `split_ifs with hn`.

Conclude with `S.mul_mem h1 (ih _ (by omega))`. Conclude with `S.zero_mem`. Use `split_ifs with hn`. Conclude with `S.mul_mem h2 (ih _ (by omega))`. Conclude with `S.zero_mem`.

Use `split_ifs with hn`. Conclude with `S.mul_mem h3 (coeff_pow_memS (m := n - 3) (fun i hi => ih i (by omega)) 2 _ le_rfl)`. Conclude with `S.zero_mem`. Use `split_ifs with hn`. Conclude with `S.mul_mem h4 (coeff_pow_memS (m := n - 4) (fun i hi => ih i (by omega)) 2 _ le_rfl)`.

Conclude with `S.zero_mem`. Use `split_ifs with hn`. Conclude with `S.mul_mem h6 (coeff_pow_memS (m := n - 6) (fun i hi => ih i (by omega)) 3 _ le_rfl)`. Conclude with `S.zero_mem`.
-/
theorem wq_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, PowerSeries.coeff n wq ∈ S := by
  have t1 : ∀ (a : ℂ_[p]) (f : PowerSeries ℂ_[p]) (n : ℕ),
      PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X * f) =
        if 1 ≤ n then a * PowerSeries.coeff (n - 1) f else 0 := by
    intro a f n
    rw [← coeff_termS, pow_one]
  simp only [IsWq] at h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (PowerSeries.coeff n) h
    rw [hc]
    simp only [map_add, t1, coeff_termS, PowerSeries.coeff_one]
    refine S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem ?_ ?_) ?_) ?_) ?_) ?_
    · split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h1 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h2 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h3 (coeff_pow_memS (m := n - 3) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h4 (coeff_pow_memS (m := n - 4) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h6 (coeff_pow_memS (m := n - 6) (fun i hi => ih i (by omega)) 3 _ le_rfl)
      · exact S.zero_mem

/- English proof (translation)
Simplify using `only [IsWq] at h`. Unfold `G wser`. Rewrite using `[sub_eq_zero]`. Use `conv_rhs => rw [h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem G_wser {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    G W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) = 0 := by
  simp only [IsWq] at h
  unfold G wser
  rw [sub_eq_zero]
  conv_rhs => rw [h]
  ring

end PI.AddIntG.Wk
