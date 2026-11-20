import Mathlib

open Polynomial

/- English proof (translation)
Establish `hint : IsIntegral ℚ_[l] x` using `(Algebra.IsAlgebraic.isAlgebraic x).isIntegral`. Set `F` to `IntermediateField.adjoin ℚ_[l] {x}`. Establish `hF : FiniteDimensional ℚ_[l] F` using `IntermediateField.adjoin.finiteDimensional hint`. Set `V : Submodule ℚ_[l] (PadicAlgCl l)` to `F.toSubalgebra.toSubmodule`. Establish `hV : FiniteDimensional ℚ_[l] V` using `hF`.

Establish `hP : ProperSpace V` using `FiniteDimensional.proper ℚ_[l] V`. Establish `hxF : x ∈ F` using `IntermediateField.mem_adjoin_simple_self ℚ_[l] x`. Set `u : ℕ → V` to `fun n => ⟨x ^ n, pow_mem hxF n⟩`. Establish `hu : ∀ n, u n ∈ Metric.closedBall (0 : V) 1`. Introduce `n`.

Rewrite using `[mem_closedBall_zero_iff]`. Express the relevant statement in the definitionally equal form `‖x ^ n‖ ≤ 1`. Rewrite using `[norm_pow, hx, one_pow]`. Take `⟨a, -, φ, hφ, ha⟩` from `(isCompact_closedBall (0 : V) 1).tendsto_subseq hu`. Take `⟨N, hN⟩` from `Metric.cauchySeq_iff'.1 ha.cauchySeq 1 one_pos`.

Establish `h1` using `hN (N + 1) (Nat.le_succ N)`. Establish `hlt : φ N < φ (N + 1)` using `hφ (Nat.lt_succ_self N)`. Use `⟨φ (N + 1) - φ N, Nat.sub_pos_of_lt hlt, ?_⟩` and prove the remaining obligations. Establish `h2 : ‖x ^ φ (N + 1) - x ^ φ N‖ < 1`. Rewrite `h1` using `[dist_eq_norm]`.

Conclude with `h1`. Establish `h3 : x ^ φ (N + 1) - x ^ φ N = x ^ φ N * (x ^ (φ (N + 1) - φ N) - 1)`. Rewrite using `[mul_sub, ← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]`. Rewrite `h2` using `[h3, norm_mul, norm_pow, hx, one_pow, one_mul]`. Then use the resulting hypothesis.
-/
private theorem pow_congr {l : ℕ} [Fact (Nat.Prime l)] {x : PadicAlgCl l} (hx : ‖x‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ ‖x ^ n - 1‖ < 1 := by
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let F := IntermediateField.adjoin ℚ_[l] {x}
  have hF : FiniteDimensional ℚ_[l] F := IntermediateField.adjoin.finiteDimensional hint
  let V : Submodule ℚ_[l] (PadicAlgCl l) := F.toSubalgebra.toSubmodule
  have hV : FiniteDimensional ℚ_[l] V := hF
  have hP : ProperSpace V := FiniteDimensional.proper ℚ_[l] V
  have hxF : x ∈ F := IntermediateField.mem_adjoin_simple_self ℚ_[l] x
  let u : ℕ → V := fun n => ⟨x ^ n, pow_mem hxF n⟩
  have hu : ∀ n, u n ∈ Metric.closedBall (0 : V) 1 := by
    intro n
    rw [mem_closedBall_zero_iff]
    change ‖x ^ n‖ ≤ 1
    rw [norm_pow, hx, one_pow]
  obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_closedBall (0 : V) 1).tendsto_subseq hu
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 ha.cauchySeq 1 one_pos
  have h1 := hN (N + 1) (Nat.le_succ N)
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨φ (N + 1) - φ N, Nat.sub_pos_of_lt hlt, ?_⟩
  have h2 : ‖x ^ φ (N + 1) - x ^ φ N‖ < 1 := by
    rw [dist_eq_norm] at h1
    exact h1
  have h3 : x ^ φ (N + 1) - x ^ φ N = x ^ φ N * (x ^ (φ (N + 1) - φ N) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]
  rwa [h3, norm_mul, norm_pow, hx, one_pow, one_mul] at h2

/- English proof (translation)
Establish `hp : ‖(l : PadicAlgCl l)‖ < 1`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`. Use `set z := y - 1 with hz`. Establish `hz1 : ‖z‖ ≤ 1`.

Use `IsUltrametricDist.norm_add_le_max y (-1)` as an intermediate fact. Rewrite `this` using `[norm_neg, norm_one, hy, max_self, ← sub_eq_add_neg]`. Conclude with `this`. Establish `hyz : y = z + 1` using `by rw [hz]; ring`. Establish `e` using `add_pow_prime_eq' hl.out z 1`.

Use `set S := ∑ k ∈ Finset.Ioo 0 l, z ^ k * 1 ^ (l - k) * ((l.choose k / l : ℕ) : PadicAlgCl l) with hS`. Establish `hS1 : ‖S‖ ≤ 1`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one` to reduce the goal to its premises. Introduce `k _`. Rewrite using `[one_pow, mul_one, norm_mul, norm_pow]`.

Conclude with `mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hz1) (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)`. Establish `e2 : z ^ l = (y ^ l - 1) + -((l : PadicAlgCl l) * S)`. Rewrite using `[hyz, e]`. Expand and normalize the polynomial expressions, which then agree. Establish `h4 : ‖z ^ l‖ < 1`.

Rewrite using `[e2]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h ?_)` and prove the remaining obligations. Rewrite using `[norm_neg, norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hp hS1`. Rewrite `h4` using `[norm_pow]`.

Conclude with `(pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h4`.
-/
private theorem descend {l : ℕ} [hl : Fact (Nat.Prime l)] {y : PadicAlgCl l} (hy : ‖y‖ = 1)
    (h : ‖y ^ l - 1‖ < 1) : ‖y - 1‖ < 1 := by
  have hp : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  set z := y - 1 with hz
  have hz1 : ‖z‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max y (-1)
    rw [norm_neg, norm_one, hy, max_self, ← sub_eq_add_neg] at this
    exact this
  have hyz : y = z + 1 := by rw [hz]; ring
  have e := add_pow_prime_eq' hl.out z 1
  set S := ∑ k ∈ Finset.Ioo 0 l, z ^ k * 1 ^ (l - k) * ((l.choose k / l : ℕ) : PadicAlgCl l)
    with hS
  have hS1 : ‖S‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro k _
    rw [one_pow, mul_one, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hz1) (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one _ _)
  have e2 : z ^ l = (y ^ l - 1) + -((l : PadicAlgCl l) * S) := by
    rw [hyz, e]; ring
  have h4 : ‖z ^ l‖ < 1 := by
    rw [e2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h ?_)
    rw [norm_neg, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hp hS1
  rw [norm_pow] at h4
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h4

/- English proof (translation)
Take `⟨n, hn, h⟩` from `pow_congr hx`. Take `⟨k, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.out.ne_one`. Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Use `clear hn`. Proceed by induction on `k with`.

Consider the case `zero => simpa using h`. Consider the case `succ k ih`. Apply `ih` to reduce the goal to its premises. Apply `descend (by rw [norm_pow, hx, one_pow])` to reduce the goal to its premises. Rewrite using `[← pow_mul, mul_right_comm, ← pow_succ]` and apply the resulting hypothesis.
-/
private theorem coprime_pow_congr {l : ℕ} [hl : Fact (Nat.Prime l)] {x : PadicAlgCl l}
    (hx : ‖x‖ = 1) : ∃ m : ℕ, ¬l ∣ m ∧ ‖x ^ m - 1‖ < 1 := by
  obtain ⟨n, hn, h⟩ := pow_congr hx
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.out.ne_one
  refine ⟨m, hm, ?_⟩
  clear hn
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply descend (by rw [norm_pow, hx, one_pow])
    rwa [← pow_mul, mul_right_comm, ← pow_succ]

/- English proof (translation)
Introduce `l _ x hx`. Take `⟨m, hm, h⟩` from `coprime_pow_congr hx`. Establish `hm0 : 0 < m` using `Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))`. Use `haveI : NeZero m := ⟨hm0.ne'⟩`. Take `⟨μ, hμ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) m`.

Establish `e` using `congrArg (eval x) (X_pow_sub_one_eq_prod hm0 hμ)`. Simplify using `only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Rewrite `h` using `[e, norm_prod]`.

Use `absurd h (not_lt.2 ?_)` and prove the remaining obligations. Use `Finset.prod_induction _ (fun r : ℝ => 1 ≤ r) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl ?_` and prove the remaining obligations. Introduce `ζ hζ`. Conclude with `hcon m ζ hm ((mem_nthRootsFinset hm0 1).1 hζ)`.
-/
theorem UpperTheory.Reformulated.B.ExistsRootCongruence.exists_root_congr :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x : PadicAlgCl l},
    ‖x‖ = (1 : ℝ) → ∃ (m : ℕ) (ζ : PadicAlgCl l), ¬l ∣ m ∧ ζ ^ m = (1 : PadicAlgCl l) ∧ ‖x - ζ‖ < (1 : ℝ) := by
  intro l _ x hx
  obtain ⟨m, hm, h⟩ := coprime_pow_congr hx
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
  haveI : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm0 hμ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  by_contra hcon
  push Not at hcon
  rw [e, norm_prod] at h
  refine absurd h (not_lt.2 ?_)
  refine Finset.prod_induction _ (fun r : ℝ => 1 ≤ r)
    (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl ?_
  intro ζ hζ
  exact hcon m ζ hm ((mem_nthRootsFinset hm0 1).1 hζ)
