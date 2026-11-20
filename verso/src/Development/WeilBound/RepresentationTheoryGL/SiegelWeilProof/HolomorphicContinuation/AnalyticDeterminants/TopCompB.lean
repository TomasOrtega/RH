import Mathlib

noncomputable section

open Polynomial

namespace PositivityTheory.Rg.Sw.LVs.TC

/- English proof (translation)
Establish `h : (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) = fun i => ∑ w : Fin 3, z ^ (w : ℕ) • Y i w`. Use function extensionality and compare the values at `i`. Simplify using `[Fin.sum_univ_three]`. Rewrite using `[h, ContinuousMultilinearMap.map_sum]`. Use `Finset.sum_congr (by simp) fun f _ => ?_` and prove the remaining obligations.

Rewrite using `[ContinuousMultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum, smul_eq_mul]`.
-/
theorem ml_expand {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (Y : Fin k → Fin 3 → V) (z : ℂ) :
    A (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) =
      ∑ f : Fin k → Fin 3, z ^ (∑ i, (f i : ℕ)) * A (fun i => Y i (f i)) := by
  have h : (fun i => Y i 0 + z • Y i 1 + z ^ 2 • Y i 2) = fun i => ∑ w : Fin 3, z ^ (w : ℕ) • Y i w := by
    funext i; simp [Fin.sum_univ_three]
  rw [h, ContinuousMultilinearMap.map_sum]
  refine Finset.sum_congr (by simp) fun f _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_pow_eq_pow_sum, smul_eq_mul]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨i, hi⟩` from `hne`. Establish `hle : ∀ x, (f x : ℕ) ≤ 2` using `fun x => by omega`. Establish `hlt : (f i : ℕ) < 2`.

Break down `Nat.lt_or_ge (f i : ℕ) 2 with h' | h'` into its components or cases. Conclude with `h'`. Conclude with `absurd (Fin.ext (by simp; omega)) hi`. Establish `: ∑ x, (f x : ℕ) < ∑ _x : Fin k, 2` using `Finset.sum_lt_sum (fun x _ => hle x) ⟨i, Finset.mem_univ _, hlt⟩`. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers.
-/
theorem sum_eq_top {k : ℕ} (f : Fin k → Fin 3) (h : ∑ i, (f i : ℕ) = 2 * k) : ∀ i, f i = 2 := by
  by_contra hne
  push Not at hne
  obtain ⟨i, hi⟩ := hne
  have hle : ∀ x, (f x : ℕ) ≤ 2 := fun x => by omega
  have hlt : (f i : ℕ) < 2 := by
    rcases Nat.lt_or_ge (f i : ℕ) 2 with h' | h'
    · exact h'
    · exact absurd (Fin.ext (by simp; omega)) hi
  have : ∑ x, (f x : ℕ) < ∑ _x : Fin k, 2 :=
    Finset.sum_lt_sum (fun x _ => hle x) ⟨i, Finset.mem_univ _, hlt⟩
  simp at this
  omega

/- English proof (translation)
Establish `hinj : Function.Injective fun m : ℕ => Complex.exp (2 * ((1 : ℝ) / (m + 2) : ℝ) * Complex.I)`. Introduce `a b hab`. Establish `hre` using `congrArg Complex.re hab`. Simplify using `only at hre`. Establish `e1 : ∀ x : ℝ, (Complex.exp (2 * (x : ℂ) * Complex.I)).re = Real.cos (2 * x)`.

Introduce `x`. Rewrite using `[show 2 * (x : ℂ) * Complex.I = ((2 * x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]`. Rewrite `hre` using `[e1, e1]`. Establish `ha : 2 * ((1 : ℝ) / (a + 2)) ∈ Set.Icc 0 Real.pi`. Prove the components needed by the constructor for the conclusion.

Check the signs of the components of the expression. Establish `: (2 : ℝ) * (1 / (a + 2)) ≤ 1`. Rewrite using `[mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]`. Combine the linear relations using `[Real.pi_gt_three]`. Establish `hb : 2 * ((1 : ℝ) / (b + 2)) ∈ Set.Icc 0 Real.pi`.

Prove the components needed by the constructor for the conclusion. Check the signs of the components of the expression. Establish `: (2 : ℝ) * (1 / (b + 2)) ≤ 1`. Rewrite using `[mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]`. Combine the linear relations using `[Real.pi_gt_three]`.

Use `Real.injOn_cos ha hb hre` as an intermediate fact. Establish `h2 : (1 : ℝ) / (a + 2) = 1 / (b + 2)` using `by linarith`. Rewrite `h2` using `[div_eq_div_iff (by positivity) (by positivity)]`. Conclude with `(by linarith : (a : ℝ) = b)` after adjusting the coercions. Use `Set.infinite_of_injective_forall_mem hinj fun m => ⟨_, rfl⟩` and prove the remaining obligations.
-/
theorem infinite_circle : Set.Infinite (Set.range fun θ : ℝ => Complex.exp (2 * θ * Complex.I)) := by
  have hinj : Function.Injective fun m : ℕ => Complex.exp (2 * ((1 : ℝ) / (m + 2) : ℝ) * Complex.I) := by
    intro a b hab
    have hre := congrArg Complex.re hab
    simp only at hre
    have e1 : ∀ x : ℝ, (Complex.exp (2 * (x : ℂ) * Complex.I)).re = Real.cos (2 * x) := by
      intro x
      rw [show 2 * (x : ℂ) * Complex.I = ((2 * x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re]
    rw [e1, e1] at hre
    have ha : 2 * ((1 : ℝ) / (a + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (a + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]
        linarith [Real.pi_gt_three]
    have hb : 2 * ((1 : ℝ) / (b + 2)) ∈ Set.Icc 0 Real.pi := by
      constructor
      · positivity
      · have : (2 : ℝ) * (1 / (b + 2)) ≤ 1 := by
          rw [mul_one_div, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
        linarith [Real.pi_gt_three]
    have := Real.injOn_cos ha hb hre
    have h2 : (1 : ℝ) / (a + 2) = 1 / (b + 2) := by linarith
    rw [div_eq_div_iff (by positivity) (by positivity)] at h2
    exact_mod_cast (by linarith : (a : ℝ) = b)
  refine Set.infinite_of_injective_forall_mem hinj fun m => ⟨_, rfl⟩

/- English proof (translation)
Use `set Q : ℂ[X] := ∑ σ, C (sg σ) * ∑ f : Fin k → Fin 3, C (A (fun i => Y σ i (f i))) * X ^ (∑ i, (f i : ℕ)) with hQ`. Establish `heval : ∀ z : ℂ, Q.eval z = ∑ σ, sg σ * A (fun i => Y σ i 0 + z • Y σ i 1 + z ^ 2 • Y σ i 2)`. Introduce `z`. Simplify using `only [hQ, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[ml_expand]`. Use `congr 1`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hQ0 : Q = 0`.

Apply `Polynomial.eq_zero_of_infinite_isRoot` to reduce the goal to its premises. Use `Set.Infinite.mono ?_ infinite_circle` and prove the remaining obligations. Introduce and unpack `_ ⟨θ, rfl⟩`. Simplify using `only [Set.mem_ofPred_eq, IsRoot.def, heval, h θ]`. Establish `hc` using `congrArg (fun p : ℂ[X] => p.coeff (2 * k)) hQ0`.

Simplify using `only [hQ, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc`. Rewrite using `[← hc]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[Finset.sum_eq_single (fun _ => 2)]`.

Simplify using `only [Fin.isValue, Fin.val_two, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Rewrite using `[if_pos (by ring), mul_one]`. Introduce `f _ hf`. Rewrite using `[if_neg, mul_zero]`. Introduce `h2`.

Conclude with `hf (funext (sum_eq_top f h2.symm))`. Simplify using the standard rewrite rules.
-/
theorem top_vanish {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : ℕ} {ι : Type*} [Fintype ι]
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin k => V) ℂ) (sg : ι → ℂ) (Y : ι → Fin k → Fin 3 → V)
    (h : ∀ θ : ℝ, ∑ σ, sg σ * A (fun i => Y σ i 0 + Complex.exp (2 * θ * Complex.I) • Y σ i 1 +
      Complex.exp (2 * θ * Complex.I) ^ 2 • Y σ i 2) = 0) :
    ∑ σ, sg σ * A (fun i => Y σ i 2) = 0 := by
  set Q : ℂ[X] := ∑ σ, C (sg σ) * ∑ f : Fin k → Fin 3, C (A (fun i => Y σ i (f i))) * X ^ (∑ i, (f i : ℕ)) with hQ
  have heval : ∀ z : ℂ, Q.eval z = ∑ σ, sg σ * A (fun i => Y σ i 0 + z • Y σ i 1 + z ^ 2 • Y σ i 2) := by
    intro z
    simp only [hQ, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ml_expand]
    congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  have hQ0 : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ infinite_circle
    rintro _ ⟨θ, rfl⟩
    simp only [Set.mem_ofPred_eq, IsRoot.def, heval, h θ]
  have hc := congrArg (fun p : ℂ[X] => p.coeff (2 * k)) hQ0
  simp only [hQ, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  rw [← hc]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [Finset.sum_eq_single (fun _ => 2)]
  · simp only [Fin.isValue, Fin.val_two, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [if_pos (by ring), mul_one]
  · intro f _ hf
    rw [if_neg, mul_zero]
    intro h2
    exact hf (funext (sum_eq_top f h2.symm))
  · simp

end PositivityTheory.Rg.Sw.LVs.TC
