import Formalism.PeriodIntegrals.CubicExponentialFactor

noncomputable section

namespace PI.CubicExponentialFactor.Wk

open PI.CubicExponentialFactor

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)`.
-/
theorem norm_add_le_one {x y : ℂ_[p]} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

/- English proof (translation)
Introduce `j hj`. Rewrite using `[PowerSeries.coeff_mul]`. Establish `key : ∀ s : Finset (ℕ × ℕ), (∀ q ∈ s, q.1 + q.2 = j) → ‖∑ q ∈ s, PowerSeries.coeff q.1 f * PowerSeries.coeff q.2 g‖ ≤ 1`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => intro _`. Simplify using the standard rewrite rules. Consider the case `insert q s hq ih`. Introduce `hs`. Rewrite using `[Finset.sum_insert hq]`.

Establish `hq'` using `hs q (Finset.mem_insert_self q s)`. Use `norm_add_le_one ?_ (ih fun q' h' => hs q' (Finset.mem_insert_of_mem h'))` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ (hf _ (by omega)) (norm_nonneg _) (hg _ (by omega))`. Conclude with `key _ (fun q h => by simpa using h)`.
-/
theorem trunc_mul {f g : PowerSeries ℂ_[p]} {k : ℕ} (hf : ∀ j < k, ‖PowerSeries.coeff j f‖ ≤ 1)
    (hg : ∀ j < k, ‖PowerSeries.coeff j g‖ ≤ 1) : ∀ j < k, ‖PowerSeries.coeff j (f * g)‖ ≤ 1 := by
  classical
  intro j hj
  rw [PowerSeries.coeff_mul]
  have key : ∀ s : Finset (ℕ × ℕ), (∀ q ∈ s, q.1 + q.2 = j) →
      ‖∑ q ∈ s, PowerSeries.coeff q.1 f * PowerSeries.coeff q.2 g‖ ≤ 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert q s hq ih =>
      intro hs
      rw [Finset.sum_insert hq]
      have hq' := hs q (Finset.mem_insert_self q s)
      refine norm_add_le_one ?_ (ih fun q' h' => hs q' (Finset.mem_insert_of_mem h'))
      rw [norm_mul]
      exact mul_le_one₀ (hf _ (by omega)) (norm_nonneg _) (hg _ (by omega))
  exact key _ (fun q h => by simpa using h)

/- English proof (translation)
Rewrite using `[mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (PowerSeries.X ^ m) F, PowerSeries.coeff_mul_X_pow']`. Use `split_ifs with h`. Rewrite using `[norm_mul]`. Conclude with `mul_le_one₀ ha (norm_nonneg _) (hF _ (by omega))`. Simplify using the standard rewrite rules.
-/
theorem term_int {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) {m k : ℕ} (hm : 1 ≤ m) {F : PowerSeries ℂ_[p]}
    (hF : ∀ j < k, ‖PowerSeries.coeff j F‖ ≤ 1) :
    ‖PowerSeries.coeff k (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ m * F)‖ ≤ 1 := by
  rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm (PowerSeries.X ^ m) F,
    PowerSeries.coeff_mul_X_pow']
  split_ifs with h
  · rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) (hF _ (by omega))
  · simp

/- English proof (translation)
Establish `h` using `term_int ha (m := 1) le_rfl hF`. Rewrite `h` using `[pow_one]`. Then use the resulting hypothesis.
-/
theorem term_int1 {a : ℂ_[p]} (ha : ‖a‖ ≤ 1) {k : ℕ} {F : PowerSeries ℂ_[p]}
    (hF : ∀ j < k, ‖PowerSeries.coeff j F‖ ≤ 1) :
    ‖PowerSeries.coeff k (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X * F)‖ ≤ 1 := by
  have h := term_int ha (m := 1) le_rfl hF
  rwa [pow_one] at h

/- English proof (translation)
Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Establish `h2 : ∀ j < k, ‖PowerSeries.coeff j (wq ^ 2)‖ ≤ 1`. Rewrite using `[pow_two]`.

Conclude with `trunc_mul ih ih`. Establish `h3 : ∀ j < k, ‖PowerSeries.coeff j (wq ^ 3)‖ ≤ 1`. Establish `e : wq ^ 3 = wq ^ 2 * wq` using `by ring`. Rewrite using `[e]`. Conclude with `trunc_mul h2 ih`.

Simplify using `only [IsWq] at hW`. Rewrite using `[hW]`. Simplify using `only [map_add]`. Use `norm_add_le_one (norm_add_le_one (norm_add_le_one (norm_add_le_one (norm_add_le_one ?_ ?_) ?_) ?_) ?_) ?_` and prove the remaining obligations. Apply the tactic sequence `rw [PowerSeries.coeff_one] split_ifs <;> simp`.

Conclude with `term_int1 ha1 ih`. Conclude with `term_int ha2 (by norm_num) ih`. Conclude with `term_int ha3 (by norm_num) h2`. Conclude with `term_int ha4 (by norm_num) h2`. Conclude with `term_int ha6 (by norm_num) h3`.
-/
theorem wq_int {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (ha1 : IsIntP W.a₁)
    (ha2 : IsIntP W.a₂) (ha3 : IsIntP W.a₃) (ha4 : IsIntP W.a₄) (ha6 : IsIntP W.a₆)
    (hW : IsWq W wq) : ∀ k, ‖PowerSeries.coeff k wq‖ ≤ 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have h2 : ∀ j < k, ‖PowerSeries.coeff j (wq ^ 2)‖ ≤ 1 := by
      rw [pow_two]
      exact trunc_mul ih ih
    have h3 : ∀ j < k, ‖PowerSeries.coeff j (wq ^ 3)‖ ≤ 1 := by
      have e : wq ^ 3 = wq ^ 2 * wq := by ring
      rw [e]
      exact trunc_mul h2 ih
    dsimp only [IsWq] at hW
    rw [hW]
    simp only [map_add]
    refine norm_add_le_one (norm_add_le_one (norm_add_le_one (norm_add_le_one
      (norm_add_le_one ?_ ?_) ?_) ?_) ?_) ?_
    · rw [PowerSeries.coeff_one]
      split_ifs <;> simp
    · exact term_int1 ha1 ih
    · exact term_int ha2 (by norm_num) ih
    · exact term_int ha3 (by norm_num) h2
    · exact term_int ha4 (by norm_num) h2
    · exact term_int ha6 (by norm_num) h3

end PI.CubicExponentialFactor.Wk

end
