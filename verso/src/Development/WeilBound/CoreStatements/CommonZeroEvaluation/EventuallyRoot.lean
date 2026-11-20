import Mathlib

open Polynomial Filter Topology

namespace ModelDimension.Alg

def HenselN (K : Type) [NormedField K] : Prop :=
  ∀ (h : K[X]) (α : K), (∀ k, ‖h.coeff k‖ ≤ 1) → ‖α‖ ≤ 1 → ‖h.eval α‖ < ‖h.derivative.eval α‖ ^ 2 →
    ∃ β, h.eval β = 0 ∧ ‖β - α‖ ≤ ‖h.eval α‖ / ‖h.derivative.eval α‖ ^ 2

variable {K : Type} [NormedField K]

/- English proof (translation)
Distinguish the cases in `H : ∃ Q : ℤ[X], ‖aeval α Q‖ < ε * ‖aeval α (derivative Q)‖ ^ 2`. Conclude with `⟨1, one_pos, fun _ _ _ => H⟩`. Use `push_neg at H`. Establish `key : ∀ m : ℕ, ∀ c : ℝ, 0 < c → ∃ δ > 0, ∀ P : ℤ[X], ‖aeval α P‖ < δ → ‖aeval α (derivative^[m] P)‖ < c`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero`. Introduce `c hc`. Conclude with `⟨c, hc, fun P hP => by simpa using hP⟩`. Consider the case `succ m ih`.

Introduce `c hc`. Take `⟨δ₁, hδ₁, h₁⟩` from `ih c hc`. Use `⟨ε * δ₁ ^ 2, by positivity, fun P hP => ?_⟩` and prove the remaining obligations. Rewrite using `[Function.iterate_succ_apply]`. Apply `h₁` to reduce the goal to its premises.

Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Establish `h2 : δ₁ ^ 2 ≤ ‖aeval α (derivative P)‖ ^ 2` using `pow_le_pow_left₀ hδ₁.le hle 2`. Establish `h3` using `H P`. Establish `h4` using `mul_le_mul_of_nonneg_left h2 hε.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨δ, hδ, hP⟩` from `key m c hc`. Conclude with `⟨δ, hδ, fun P h1 h2 => absurd h1 (not_le.mpr (hP P h2))⟩`.
-/
theorem exists_deriv (α : K) (ε : ℝ) (hε : 0 < ε) (m : ℕ) (c : ℝ) (hc : 0 < c) : ∃ δ > 0, ∀ P : ℤ[X],
    c ≤ ‖aeval α (derivative^[m] P)‖ → ‖aeval α P‖ < δ →
      ∃ Q : ℤ[X], ‖aeval α Q‖ < ε * ‖aeval α (derivative Q)‖ ^ 2 := by
  by_cases H : ∃ Q : ℤ[X], ‖aeval α Q‖ < ε * ‖aeval α (derivative Q)‖ ^ 2
  · exact ⟨1, one_pos, fun _ _ _ => H⟩
  · push_neg at H
    have key : ∀ m : ℕ, ∀ c : ℝ, 0 < c → ∃ δ > 0, ∀ P : ℤ[X],
        ‖aeval α P‖ < δ → ‖aeval α (derivative^[m] P)‖ < c := by
      intro m
      induction m with
      | zero =>
        intro c hc
        exact ⟨c, hc, fun P hP => by simpa using hP⟩
      | succ m ih =>
        intro c hc
        obtain ⟨δ₁, hδ₁, h₁⟩ := ih c hc
        refine ⟨ε * δ₁ ^ 2, by positivity, fun P hP => ?_⟩
        rw [Function.iterate_succ_apply]
        apply h₁
        by_contra hle
        push_neg at hle
        have h2 : δ₁ ^ 2 ≤ ‖aeval α (derivative P)‖ ^ 2 := pow_le_pow_left₀ hδ₁.le hle 2
        have h3 := H P
        have h4 := mul_le_mul_of_nonneg_left h2 hε.le
        linarith
    obtain ⟨δ, hδ, hP⟩ := key m c hc
    exact ⟨δ, hδ, fun P h1 h2 => absurd h1 (not_le.mpr (hP P h2))⟩

/- English proof (translation)
Establish `h : ∀ k ∈ S, ∀ᶠ n in atTop, ‖π ^ n * z k‖ < 1`. Introduce `k _`. Establish `ht : Tendsto (fun n : ℕ => π ^ n * z k) atTop (𝓝 0)`. Use `(tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1).mul_const (z k)` as an intermediate fact. Rewrite `this` using `[zero_mul]`. Then use the resulting hypothesis.

Establish `hn` using `ht.norm`. Rewrite `hn` using `[norm_zero]`. Conclude with `hn.eventually (gt_mem_nhds one_pos)`. Establish `hall : ∀ᶠ n in atTop, ∀ k ∈ S, ‖π ^ n * z k‖ < 1` using `(Filter.eventually_all_finset S).2 h`. Take `⟨N, hN⟩` from `hall.exists`.

Conclude with `⟨N, pow_ne_zero N h0, hN⟩`.
-/
theorem exists_small {π : K} (h0 : π ≠ 0) (h1 : ‖π‖ < 1) {ι : Type} (S : Finset ι) (z : ι → K) :
    ∃ N : ℕ, π ^ N ≠ 0 ∧ ∀ k ∈ S, ‖π ^ N * z k‖ < 1 := by
  have h : ∀ k ∈ S, ∀ᶠ n in atTop, ‖π ^ n * z k‖ < 1 := by
    intro k _
    have ht : Tendsto (fun n : ℕ => π ^ n * z k) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h1).mul_const (z k)
      rwa [zero_mul] at this
    have hn := ht.norm
    rw [norm_zero] at hn
    exact hn.eventually (gt_mem_nhds one_pos)
  have hall : ∀ᶠ n in atTop, ∀ k ∈ S, ‖π ^ n * z k‖ < 1 := (Filter.eventually_all_finset S).2 h
  obtain ⟨N, hN⟩ := hall.exists
  exact ⟨N, pow_ne_zero N h0, hN⟩

/- English proof (translation)
Establish `hloc : ∀ α : K, ‖α‖ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ β : K, IsAlgebraic ℤ β ∧ ‖β - α‖ < ε`. Introduce `α hα ε hε`. Take `⟨m, hm⟩` from `hC α hα`. Establish `hε' : 0 < min ε 1` using `lt_min hε one_pos`. Establish `hfac : 0 < ‖(m.factorial : K)‖` using `norm_pos_iff.2 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))`.

Take `⟨δ, hδ, hQ⟩` from `ModelDimension.Alg.exists_deriv α (min ε 1) hε' m _ hfac`. Take `⟨P, hPm, hPd, hPδ⟩` from `hm δ hδ`. Establish `hcoeff : P.coeff m = 1`. Rewrite using `[← hPd]`. Conclude with `hPm.coeff_natDegree`.

Establish `hDP : derivative^[m] P = C ((m.factorial : ℕ) : ℤ)`. Establish `hdeg : (derivative^[m] P).natDegree ≤ 0`. Use `natDegree_iterate_derivative P m` as an intermediate fact. Rewrite `this` using `[hPd, Nat.sub_self]`. Conclude with `this`.

Rewrite using `[eq_C_of_natDegree_le_zero hdeg, coeff_iterate_derivative, zero_add, Nat.descFactorial_self, hcoeff]`. Simplify using the standard rewrite rules. Establish `hval : aeval α (derivative^[m] P) = (m.factorial : K)`. Rewrite using `[hDP]`. Simplify using the standard rewrite rules.

Take `⟨Q, hQ'⟩` from `hQ P (le_of_eq (by rw [hval])) hPδ`. Establish `hpos : 0 < ‖aeval α (derivative Q)‖ ^ 2` using `(mul_pos_iff_of_pos_left hε').1 (lt_of_le_of_lt (norm_nonneg _) hQ')`. Establish `hev : ∀ y : K, (Q.map (algebraMap ℤ K)).eval y = aeval y Q` using `fun y => eval_map_algebraMap Q y`. Establish `hev' : (Q.map (algebraMap ℤ K)).derivative.eval α = aeval α (derivative Q)`. Rewrite using `[derivative_map, eval_map_algebraMap]`.

Establish `hcoef : ∀ k, ‖(Q.map (algebraMap ℤ K)).coeff k‖ ≤ 1` using `fun k => by`. Rewrite using `[coeff_map]`. Simplify using `using hZ (Q.coeff k)`. Establish `hlt : ‖(Q.map (algebraMap ℤ K)).eval α‖ < ‖(Q.map (algebraMap ℤ K)).derivative.eval α‖ ^ 2`. Rewrite using `[hev, hev']`.

Conclude with `lt_of_lt_of_le hQ' (mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _))`. Take `⟨β, hβ, hβα⟩` from `hH _ α hcoef hα hlt`. Use `⟨β, ⟨Q, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hQ'`.

Rewrite using `[← hev]`. Conclude with `hβ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Metric.dense_iff]`. Introduce `x r hr`.

Establish `hν : ((N : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.2 hN0`. Take `⟨M, hM0, hM⟩` from `ModelDimension.Alg.exists_small hν hN ({()} : Finset Unit) (fun _ => x)`. Establish `hMx : ‖(N : K) ^ M * x‖ < 1` using `hM () (Finset.mem_singleton_self _)`. Establish `htpos : 0 < ‖(N : K) ^ M‖` using `norm_pos_iff.2 hM0`. Take `⟨β, hβ, hβx⟩` from `hloc _ hMx.le (r * ‖(N : K) ^ M‖) (mul_pos hr htpos)`.

Establish `hNa : IsAlgebraic ℤ ((N : K) ^ M)` using `(isAlgebraic_natCast N).pow M`. Use `⟨β / (N : K) ^ M, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_ball_iff_norm]`. Establish `h : β / (N : K) ^ M - x = (β - (N : K) ^ M * x) / (N : K) ^ M`. Rewrite using `[sub_div, mul_div_cancel_left₀ x hM0]`.

Rewrite using `[h, norm_div, div_lt_iff₀ htpos]`. Conclude with `hβx`. Use `show IsAlgebraic ℤ (β / (N : K) ^ M)`. Rewrite using `[div_eq_mul_inv]`. Conclude with `hβ.mul hNa.inv`.
-/
theorem dense_algebraic [CharZero K] (hH : HenselN K) (hZ : ∀ z : ℤ, ‖(z : K)‖ ≤ 1) (N : ℕ) (hN0 : N ≠ 0)
    (hN : ‖(N : K)‖ < 1)
    (hC : ∀ α : K, ‖α‖ ≤ 1 → ∃ m : ℕ, ∀ δ > 0, ∃ P : ℤ[X], P.Monic ∧ P.natDegree = m ∧ ‖aeval α P‖ < δ) :
    Dense {x : K | IsAlgebraic ℤ x} := by
  have hloc : ∀ α : K, ‖α‖ ≤ 1 → ∀ ε : ℝ, 0 < ε → ∃ β : K, IsAlgebraic ℤ β ∧ ‖β - α‖ < ε := by
    intro α hα ε hε
    obtain ⟨m, hm⟩ := hC α hα
    have hε' : 0 < min ε 1 := lt_min hε one_pos
    have hfac : 0 < ‖(m.factorial : K)‖ :=
      norm_pos_iff.2 (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
    obtain ⟨δ, hδ, hQ⟩ :=
      ModelDimension.Alg.exists_deriv α (min ε 1) hε' m _ hfac
    obtain ⟨P, hPm, hPd, hPδ⟩ := hm δ hδ
    have hcoeff : P.coeff m = 1 := by
      rw [← hPd]
      exact hPm.coeff_natDegree
    have hDP : derivative^[m] P = C ((m.factorial : ℕ) : ℤ) := by
      have hdeg : (derivative^[m] P).natDegree ≤ 0 := by
        have := natDegree_iterate_derivative P m
        rw [hPd, Nat.sub_self] at this
        exact this
      rw [eq_C_of_natDegree_le_zero hdeg, coeff_iterate_derivative, zero_add,
        Nat.descFactorial_self, hcoeff]
      simp
    have hval : aeval α (derivative^[m] P) = (m.factorial : K) := by
      rw [hDP]
      simp
    obtain ⟨Q, hQ'⟩ := hQ P (le_of_eq (by rw [hval])) hPδ
    have hpos : 0 < ‖aeval α (derivative Q)‖ ^ 2 :=
      (mul_pos_iff_of_pos_left hε').1 (lt_of_le_of_lt (norm_nonneg _) hQ')
    have hev : ∀ y : K, (Q.map (algebraMap ℤ K)).eval y = aeval y Q :=
      fun y => eval_map_algebraMap Q y
    have hev' : (Q.map (algebraMap ℤ K)).derivative.eval α = aeval α (derivative Q) := by
      rw [derivative_map, eval_map_algebraMap]
    have hcoef : ∀ k, ‖(Q.map (algebraMap ℤ K)).coeff k‖ ≤ 1 := fun k => by
      rw [coeff_map]
      simpa using hZ (Q.coeff k)
    have hlt : ‖(Q.map (algebraMap ℤ K)).eval α‖ <
        ‖(Q.map (algebraMap ℤ K)).derivative.eval α‖ ^ 2 := by
      rw [hev, hev']
      exact lt_of_lt_of_le hQ' (mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _))
    obtain ⟨β, hβ, hβα⟩ := hH _ α hcoef hα hlt
    refine ⟨β, ⟨Q, ?_, ?_⟩, ?_⟩
    · rintro rfl
      simp at hQ'
    · rw [← hev]
      exact hβ
    · calc ‖β - α‖ ≤ ‖(Q.map (algebraMap ℤ K)).eval α‖ /
              ‖(Q.map (algebraMap ℤ K)).derivative.eval α‖ ^ 2 := hβα
        _ = ‖aeval α Q‖ / ‖aeval α (derivative Q)‖ ^ 2 := by rw [hev, hev']
        _ < min ε 1 := (div_lt_iff₀ hpos).2 hQ'
        _ ≤ ε := min_le_left _ _
  rw [Metric.dense_iff]
  intro x r hr
  have hν : ((N : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hN0
  obtain ⟨M, hM0, hM⟩ :=
    ModelDimension.Alg.exists_small hν hN ({()} : Finset Unit) (fun _ => x)
  have hMx : ‖(N : K) ^ M * x‖ < 1 := hM () (Finset.mem_singleton_self _)
  have htpos : 0 < ‖(N : K) ^ M‖ := norm_pos_iff.2 hM0
  obtain ⟨β, hβ, hβx⟩ := hloc _ hMx.le (r * ‖(N : K) ^ M‖) (mul_pos hr htpos)
  have hNa : IsAlgebraic ℤ ((N : K) ^ M) := (isAlgebraic_natCast N).pow M
  refine ⟨β / (N : K) ^ M, ?_, ?_⟩
  · rw [mem_ball_iff_norm]
    have h : β / (N : K) ^ M - x = (β - (N : K) ^ M * x) / (N : K) ^ M := by
      rw [sub_div, mul_div_cancel_left₀ x hM0]
    rw [h, norm_div, div_lt_iff₀ htpos]
    exact hβx
  · show IsAlgebraic ℤ (β / (N : K) ^ M)
    rw [div_eq_mul_inv]
    exact hβ.mul hNa.inv

/- English proof (translation)
Establish `hcont : ∀ (p : A[X]) (y : K), Continuous fun t => p.eval₂ (ev t) y`. Introduce `p y`. Establish `h : ∀ t, p.eval₂ (ev t) y = ∑ n ∈ p.support, ev t (p.coeff n) * y ^ n` using `fun t => by`. Rewrite using `[eval₂_eq_sum, Polynomial.sum]`. Conclude with `(continuous_finsetSum _ fun n _ => (hev _).mul continuous_const).congr fun t => (h t).symm`.

Establish `hcoef : ∀ (q : K[X]) (k : ℕ), Continuous fun t => ((f.map (ev t)).comp q).coeff k`. Introduce `q k`. Establish `h : ∀ t, ((f.map (ev t)).comp q).coeff k = ∑ n ∈ f.support, ev t (f.coeff n) * (q ^ n).coeff k` using `fun t => by`. Rewrite using `[Polynomial.comp, eval₂_map, eval₂_eq_sum, Polynomial.sum, finset_sum_coeff]`. Simplify using `only [RingHom.coe_comp, RingHom.comp_apply, Function.comp_apply, coeff_C_mul]`.

Conclude with `(continuous_finsetSum _ fun n _ => (hev _).mul continuous_const).congr fun t => (h t).symm`. Take `⟨p, hp⟩ : ∃ p : T → K[X], ∀ t, p t = (f.map (ev t)).comp (C x₀ + X)` from `⟨_, fun _ => rfl⟩`. Establish `hpc : ∀ k, Continuous fun t => (p t).coeff k` using `fun k => (hcoef (C x₀ + X) k).congr fun t => by rw [hp]`. Establish `hpdeg : ∀ t, (p t).natDegree ≤ f.natDegree`. Introduce `t`.

Rewrite using `[hp]`. Use `natDegree_comp_le.trans ?_` and prove the remaining obligations. Establish `hq : (C x₀ + X : K[X]).natDegree ≤ 1` using `(natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)`. Combine the equalities or inequalities in the displayed calculation. Establish `hpeval : ∀ t y, (p t).eval y = f.eval₂ (ev t) (x₀ + y)`.

Introduce `t y`. Rewrite using `[hp, eval_comp, eval_map]`. Simplify using the standard rewrite rules. Establish `hpderiv : ∀ t, (derivative (p t)).eval 0 = f.derivative.eval₂ (ev t) x₀`. Introduce `t`.

Rewrite using `[hp, derivative_comp, eval_mul, eval_comp, derivative_map, eval_map]`. Simplify using the standard rewrite rules. Establish `hb0 : (p t₀).coeff 0 = 0`. Rewrite using `[coeff_zero_eq_eval_zero, hpeval, add_zero, hf]`. Take `⟨N, hN0, hN⟩` from `ModelDimension.Alg.exists_small h0 h1 (Finset.range (f.natDegree + 1)) (fun k => (p t₀).coeff k)`.

Establish `hl1 : ‖π ^ N‖ ≤ 1`. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) h1.le`. Generalize the expression as in `π ^ N = l at hN0 hN hl1`. Establish `hat : ∀ k ∈ Finset.range (f.natDegree + 1), ‖l ^ k * (p t₀).coeff k‖ < 1`.

Introduce `k hk`. Consider the cases of `k with`. Consider the case `zero => simp [hb0]`. Consider the case `succ j`. Rewrite using `[pow_succ, mul_assoc, norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `E1 : ∀ᶠ t in 𝓝 t₀, ∀ k ∈ Finset.range (f.natDegree + 1), ‖l ^ k * (p t).coeff k‖ < 1`. Use `(Filter.eventually_all_finset _).2 fun k hk => ?_` and prove the remaining obligations. Establish `hck : Continuous fun t => ‖l ^ k * (p t).coeff k‖` using `(continuous_const.mul (hpc k)).norm`. Conclude with `hck.continuousAt.eventually_lt continuousAt_const (hat k hk)`.

Establish `hu : Continuous fun t => ‖f.eval₂ (ev t) x₀‖` using `(hcont f x₀).norm`. Establish `hw : Continuous fun t => ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2` using `((continuous_const.mul (hcont _ x₀)).norm).pow 2`. Establish `hw0 : 0 < ‖l * f.derivative.eval₂ (ev t₀) x₀‖ ^ 2` using `pow_pos (norm_pos_iff.2 (mul_ne_zero hN0 hf')) 2`. Establish `E2 : ∀ᶠ t in 𝓝 t₀, ‖f.eval₂ (ev t) x₀‖ < ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2`. Use `hu.continuousAt.eventually_lt hw.continuousAt ?_` and prove the remaining obligations.

Use `show ‖f.eval₂ (ev t₀) x₀‖ < ‖l * f.derivative.eval₂ (ev t₀) x₀‖ ^ 2`. Rewrite using `[hf, norm_zero]`. Conclude with `hw0`. Establish `hu' : Continuous fun t => ‖f.eval₂ (ev t) x₀‖ * ‖l‖` using `hu.mul continuous_const`. Establish `hw' : Continuous fun t => r * ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2` using `continuous_const.mul hw`.

Establish `E3 : ∀ᶠ t in 𝓝 t₀, ‖f.eval₂ (ev t) x₀‖ * ‖l‖ < r * ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2`. Use `hu'.continuousAt.eventually_lt hw'.continuousAt ?_` and prove the remaining obligations. Use `show ‖f.eval₂ (ev t₀) x₀‖ * ‖l‖ < r * ‖l * f.derivative.eval₂ (ev t₀) x₀‖ ^ 2`. Rewrite using `[hf, norm_zero, zero_mul]`. Conclude with `mul_pos hr hw0`.

Use `filter_upwards [E1, E2, E3] with t hE1 hE2 hE3`. Take `⟨G, hG⟩ : ∃ G : K[X], G = (p t).comp (C l * X)` from `⟨_, rfl⟩`. Establish `hGc : ∀ k, ‖G.coeff k‖ ≤ 1`. Introduce `k`. Rewrite using `[hG, comp_C_mul_X_coeff, mul_comm]`.

Distinguish the cases in `hk : k ∈ Finset.range (f.natDegree + 1)`. Conclude with `(hE1 k hk).le`. Rewrite using `[coeff_eq_zero_of_natDegree_lt, mul_zero, norm_zero]`. Conclude with `zero_le_one`. Use `hpdeg t` as an intermediate fact.

Simplify using `only [Finset.mem_range, not_lt] at hk`. Use linear arithmetic over natural numbers and integers. Establish `hG0 : G.eval 0 = f.eval₂ (ev t) x₀`. Rewrite using `[hG, eval_comp, hpeval]`. Simplify using the standard rewrite rules.

Establish `hG1 : (derivative G).eval 0 = l * f.derivative.eval₂ (ev t) x₀`. Rewrite using `[hG, derivative_comp, eval_mul, eval_comp, derivative_C_mul_X, eval_C]`. Simplify using `[hpderiv]`. Establish `hlt : ‖G.eval 0‖ < ‖(derivative G).eval 0‖ ^ 2`. Rewrite using `[hG0, hG1]`.

Conclude with `hE2`. Take `⟨y, hy, hyb⟩` from `hH G 0 hGc (by simp) hlt`. Use `⟨x₀ + l * y, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hyb` using `[hG0, hG1, sub_zero]`. Establish `hwpos : 0 < ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2` using `lt_of_le_of_lt (norm_nonneg _) hE2`.

Rewrite `hyb` using `[le_div_iff₀ hwpos]`. Rewrite using `[add_sub_cancel_left, norm_mul]`. Assume the negation of the conclusion as `hge`. Use `push_neg at hge`. Establish `h1'` using `mul_le_mul_of_nonneg_right hge hwpos.le`.

Establish `h2'` using `mul_le_mul_of_nonneg_left hyb (norm_nonneg l)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hGy : G.eval y = (p t).eval (l * y)`. Rewrite using `[hG, eval_comp]`. Simplify using the standard rewrite rules.

Rewrite using `[← hpeval t (l * y), ← hGy]`. Conclude with `hy`.
-/
theorem eventually_root (hH : HenselN K) {π : K} (h0 : π ≠ 0) (h1 : ‖π‖ < 1) {T A : Type} [TopologicalSpace T]
    [CommRing A] (ev : T → (A →+* K)) (hev : ∀ r, Continuous fun t => ev t r) (f : A[X]) (t₀ : T) (x₀ : K)
    (hf : f.eval₂ (ev t₀) x₀ = 0) (hf' : f.derivative.eval₂ (ev t₀) x₀ ≠ 0) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ t in 𝓝 t₀, ∃ x, ‖x - x₀‖ < r ∧ f.eval₂ (ev t) x = 0 := by
  classical
  have hcont : ∀ (p : A[X]) (y : K), Continuous fun t => p.eval₂ (ev t) y := by
    intro p y
    have h : ∀ t, p.eval₂ (ev t) y = ∑ n ∈ p.support, ev t (p.coeff n) * y ^ n := fun t => by
      rw [eval₂_eq_sum, Polynomial.sum]
    exact (continuous_finsetSum _ fun n _ => (hev _).mul continuous_const).congr
      fun t => (h t).symm
  have hcoef : ∀ (q : K[X]) (k : ℕ), Continuous fun t => ((f.map (ev t)).comp q).coeff k := by
    intro q k
    have h : ∀ t, ((f.map (ev t)).comp q).coeff k =
        ∑ n ∈ f.support, ev t (f.coeff n) * (q ^ n).coeff k := fun t => by
      rw [Polynomial.comp, eval₂_map, eval₂_eq_sum, Polynomial.sum, finset_sum_coeff]
      simp only [RingHom.coe_comp, RingHom.comp_apply, Function.comp_apply, coeff_C_mul]
    exact (continuous_finsetSum _ fun n _ => (hev _).mul continuous_const).congr
      fun t => (h t).symm
  obtain ⟨p, hp⟩ : ∃ p : T → K[X], ∀ t, p t = (f.map (ev t)).comp (C x₀ + X) :=
    ⟨_, fun _ => rfl⟩
  have hpc : ∀ k, Continuous fun t => (p t).coeff k := fun k =>
    (hcoef (C x₀ + X) k).congr fun t => by rw [hp]
  have hpdeg : ∀ t, (p t).natDegree ≤ f.natDegree := by
    intro t
    rw [hp]
    refine natDegree_comp_le.trans ?_
    have hq : (C x₀ + X : K[X]).natDegree ≤ 1 :=
      (natDegree_add_le _ _).trans (max_le (by simp) natDegree_X_le)
    calc (f.map (ev t)).natDegree * (C x₀ + X).natDegree ≤ f.natDegree * 1 :=
          Nat.mul_le_mul natDegree_map_le hq
      _ = f.natDegree := mul_one _
  have hpeval : ∀ t y, (p t).eval y = f.eval₂ (ev t) (x₀ + y) := by
    intro t y
    rw [hp, eval_comp, eval_map]
    simp
  have hpderiv : ∀ t, (derivative (p t)).eval 0 = f.derivative.eval₂ (ev t) x₀ := by
    intro t
    rw [hp, derivative_comp, eval_mul, eval_comp, derivative_map, eval_map]
    simp
  have hb0 : (p t₀).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, hpeval, add_zero, hf]
  obtain ⟨N, hN0, hN⟩ := ModelDimension.Alg.exists_small h0 h1
    (Finset.range (f.natDegree + 1)) (fun k => (p t₀).coeff k)
  have hl1 : ‖π ^ N‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) h1.le
  generalize π ^ N = l at hN0 hN hl1
  have hat : ∀ k ∈ Finset.range (f.natDegree + 1), ‖l ^ k * (p t₀).coeff k‖ < 1 := by
    intro k hk
    cases k with
    | zero => simp [hb0]
    | succ j =>
      rw [pow_succ, mul_assoc, norm_mul]
      calc ‖l ^ j‖ * ‖l * (p t₀).coeff (j + 1)‖ ≤ ‖l * (p t₀).coeff (j + 1)‖ :=
            mul_le_of_le_one_left (norm_nonneg _)
              (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hl1)
        _ < 1 := hN _ hk
  have E1 : ∀ᶠ t in 𝓝 t₀, ∀ k ∈ Finset.range (f.natDegree + 1), ‖l ^ k * (p t).coeff k‖ < 1 := by
    refine (Filter.eventually_all_finset _).2 fun k hk => ?_
    have hck : Continuous fun t => ‖l ^ k * (p t).coeff k‖ := (continuous_const.mul (hpc k)).norm
    exact hck.continuousAt.eventually_lt continuousAt_const (hat k hk)
  have hu : Continuous fun t => ‖f.eval₂ (ev t) x₀‖ := (hcont f x₀).norm
  have hw : Continuous fun t => ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2 :=
    ((continuous_const.mul (hcont _ x₀)).norm).pow 2
  have hw0 : 0 < ‖l * f.derivative.eval₂ (ev t₀) x₀‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (mul_ne_zero hN0 hf')) 2
  have E2 : ∀ᶠ t in 𝓝 t₀, ‖f.eval₂ (ev t) x₀‖ < ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2 := by
    refine hu.continuousAt.eventually_lt hw.continuousAt ?_
    show ‖f.eval₂ (ev t₀) x₀‖ < ‖l * f.derivative.eval₂ (ev t₀) x₀‖ ^ 2
    rw [hf, norm_zero]
    exact hw0
  have hu' : Continuous fun t => ‖f.eval₂ (ev t) x₀‖ * ‖l‖ := hu.mul continuous_const
  have hw' : Continuous fun t => r * ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2 :=
    continuous_const.mul hw
  have E3 : ∀ᶠ t in 𝓝 t₀,
      ‖f.eval₂ (ev t) x₀‖ * ‖l‖ < r * ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2 := by
    refine hu'.continuousAt.eventually_lt hw'.continuousAt ?_
    show ‖f.eval₂ (ev t₀) x₀‖ * ‖l‖ < r * ‖l * f.derivative.eval₂ (ev t₀) x₀‖ ^ 2
    rw [hf, norm_zero, zero_mul]
    exact mul_pos hr hw0
  filter_upwards [E1, E2, E3] with t hE1 hE2 hE3
  obtain ⟨G, hG⟩ : ∃ G : K[X], G = (p t).comp (C l * X) := ⟨_, rfl⟩
  have hGc : ∀ k, ‖G.coeff k‖ ≤ 1 := by
    intro k
    rw [hG, comp_C_mul_X_coeff, mul_comm]
    by_cases hk : k ∈ Finset.range (f.natDegree + 1)
    · exact (hE1 k hk).le
    · rw [coeff_eq_zero_of_natDegree_lt, mul_zero, norm_zero]
      · exact zero_le_one
      · have := hpdeg t
        simp only [Finset.mem_range, not_lt] at hk
        omega
  have hG0 : G.eval 0 = f.eval₂ (ev t) x₀ := by
    rw [hG, eval_comp, hpeval]
    simp
  have hG1 : (derivative G).eval 0 = l * f.derivative.eval₂ (ev t) x₀ := by
    rw [hG, derivative_comp, eval_mul, eval_comp, derivative_C_mul_X, eval_C]
    simp [hpderiv]
  have hlt : ‖G.eval 0‖ < ‖(derivative G).eval 0‖ ^ 2 := by
    rw [hG0, hG1]
    exact hE2
  obtain ⟨y, hy, hyb⟩ := hH G 0 hGc (by simp) hlt
  refine ⟨x₀ + l * y, ?_, ?_⟩
  · rw [hG0, hG1, sub_zero] at hyb
    have hwpos : 0 < ‖l * f.derivative.eval₂ (ev t) x₀‖ ^ 2 :=
      lt_of_le_of_lt (norm_nonneg _) hE2
    rw [le_div_iff₀ hwpos] at hyb
    rw [add_sub_cancel_left, norm_mul]
    by_contra hge
    push_neg at hge
    have h1' := mul_le_mul_of_nonneg_right hge hwpos.le
    have h2' := mul_le_mul_of_nonneg_left hyb (norm_nonneg l)
    nlinarith
  · have hGy : G.eval y = (p t).eval (l * y) := by
      rw [hG, eval_comp]
      simp
    rw [← hpeval t (l * y), ← hGy]
    exact hy

/- English proof (translation)
Use `letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨π, h0, h1.ne⟩`. Introduce `hfin`. Establish `hU : IsOpen (Metric.ball x r \ (D ∩ Metric.ball x r))` using `Metric.isOpen_ball.sdiff hfin.isClosed`. Establish `hne : (Metric.ball x r \ (D ∩ Metric.ball x r)).Nonempty` using `((infinite_of_mem_nhds x (Metric.ball_mem_nhds x hr)).diff hfin).nonempty`. Take `⟨y, hyU, hyD⟩` from `hD.inter_open_nonempty _ hU hne`.

Conclude with `hyU.2 ⟨hyD, hyU.1⟩`.
-/
theorem infinite_inter {π : K} (h0 : π ≠ 0) (h1 : ‖π‖ < 1) {D : Set K} (hD : Dense D) (x : K) (r : ℝ)
    (hr : 0 < r) : (D ∩ Metric.ball x r).Infinite := by
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne ⟨π, h0, h1.ne⟩
  intro hfin
  have hU : IsOpen (Metric.ball x r \ (D ∩ Metric.ball x r)) :=
    Metric.isOpen_ball.sdiff hfin.isClosed
  have hne : (Metric.ball x r \ (D ∩ Metric.ball x r)).Nonempty :=
    ((infinite_of_mem_nhds x (Metric.ball_mem_nhds x hr)).diff hfin).nonempty
  obtain ⟨y, hyU, hyD⟩ := hD.inter_open_nonempty _ hU hne
  exact hyU.2 ⟨hyD, hyU.1⟩

end ModelDimension.Alg
