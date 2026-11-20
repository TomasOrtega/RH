import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurDefs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def newtonBall (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rwa [norm_neg]

/- English proof (translation)
Establish `hp : (↑P.coeffs : Set K) ⊆ newtonBall K`. Introduce `c hc`. Take `⟨i, -, rfl⟩` from `Polynomial.mem_coeffs_iff.mp (Finset.mem_coe.mp hc)`. Conclude with `hP i`. Conclude with `⟨P.toSubring (newtonBall K) hp, Polynomial.map_toSubring P (newtonBall K) hp⟩`.
-/
theorem newton_exists_poly (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) :
    ∃ Q : Polynomial (newtonBall K), Q.map (newtonBall K).subtype = P := by
  have hp : (↑P.coeffs : Set K) ⊆ newtonBall K := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp (Finset.mem_coe.mp hc)
    exact hP i
  exact ⟨P.toSubring (newtonBall K) hp, Polynomial.map_toSubring P (newtonBall K) hp⟩

/- English proof (translation)
Rewrite using `[Polynomial.eval_map]`. Conclude with `Polynomial.eval₂_at_apply (newtonBall K).subtype a`.
-/
theorem newton_eval_ball (Q : Polynomial (newtonBall K)) (a : newtonBall K) :
    (Q.map (newtonBall K).subtype).eval (a : K) = ((Q.eval a : newtonBall K) : K) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (newtonBall K).subtype a

/- English proof (translation)
Take `⟨Q, rfl⟩` from `newton_exists_poly P hP`. Take `⟨k, hk⟩` from `Polynomial.binomExpansion Q ⟨x, hx⟩ ⟨y, hy⟩`. Use `⟨k, k.2, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun z : newtonBall K => (z : K)) hk`. Establish `e1` using `newton_eval_ball Q (⟨x, hx⟩ + ⟨y, hy⟩)`.

Establish `e2` using `newton_eval_ball Q ⟨x, hx⟩`. Establish `e3` using `newton_eval_ball (Polynomial.derivative Q) ⟨x, hx⟩`. Rewrite using `[Polynomial.derivative_map]`. Simplify using `only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow] at h e1 e2 e3`. Rewrite using `[e1, e2, e3, h]`.
-/
theorem newton_expansion (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∃ k : K, ‖k‖ ≤ 1 ∧ P.eval (x + y) = P.eval x + P.derivative.eval x * y + k * y ^ 2 := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion Q ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨k, k.2, ?_⟩
  have h := congrArg (fun z : newtonBall K => (z : K)) hk
  have e1 := newton_eval_ball Q (⟨x, hx⟩ + ⟨y, hy⟩)
  have e2 := newton_eval_ball Q ⟨x, hx⟩
  have e3 := newton_eval_ball (Polynomial.derivative Q) ⟨x, hx⟩
  rw [Polynomial.derivative_map]
  simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_pow] at h e1 e2 e3
  rw [e1, e2, e3, h]

/- English proof (translation)
Take `⟨Q, rfl⟩` from `newton_exists_poly P hP`. Take `⟨k, hk⟩` from `Polynomial.evalSubFactor Q ⟨x, hx⟩ ⟨y, hy⟩`. Establish `h` using `congrArg (fun z : newtonBall K => (z : K)) hk`. Establish `e1` using `newton_eval_ball Q ⟨x, hx⟩`. Establish `e2` using `newton_eval_ball Q ⟨y, hy⟩`.

Simplify using `only [AddSubgroupClass.coe_sub, Subring.coe_mul] at h e1 e2`. Rewrite using `[e1, e2, h, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) k.2`.
-/
theorem newton_lipschitz (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x y : K)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖P.eval x - P.eval y‖ ≤ ‖x - y‖ := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  obtain ⟨k, hk⟩ := Polynomial.evalSubFactor Q ⟨x, hx⟩ ⟨y, hy⟩
  have h := congrArg (fun z : newtonBall K => (z : K)) hk
  have e1 := newton_eval_ball Q ⟨x, hx⟩
  have e2 := newton_eval_ball Q ⟨y, hy⟩
  simp only [AddSubgroupClass.coe_sub, Subring.coe_mul] at h e1 e2
  rw [e1, e2, h, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) k.2

/- English proof (translation)
Take `⟨Q, rfl⟩` from `newton_exists_poly P hP`. Rewrite using `[Polynomial.derivative_map, Polynomial.coeff_map]`. Conclude with `((Polynomial.derivative Q).coeff i).2`.
-/
theorem newton_derivative_coeff (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (i : ℕ) :
    ‖P.derivative.coeff i‖ ≤ 1 := by
  obtain ⟨Q, rfl⟩ := newton_exists_poly P hP
  rw [Polynomial.derivative_map, Polynomial.coeff_map]
  exact ((Polynomial.derivative Q).coeff i).2

/- English proof (translation)
Establish `hd : P.derivative.eval x ≠ 0`. Introduce `h`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`. Use `set t : K := -(P.eval x / P.derivative.eval x) with ht`.

Establish `hnt : ‖t‖ = ‖P.eval x‖` using `by rw [ht, norm_neg, norm_div, h1, div_one]`. Establish `ht1 : ‖t‖ ≤ 1` using `hnt ▸ h0.le`. Establish `hy : ‖x + t‖ ≤ 1` using `(IsUltrametricDist.norm_add_le_max x t).trans (max_le hx ht1)`. Take `⟨k, hk, he⟩` from `newton_expansion P hP x t hx ht1`. Use `⟨x + t, hy, ?_, ?_, ?_⟩` and prove the remaining obligations.

Establish `hl` using `newton_lipschitz P.derivative (newton_derivative_coeff P hP) (x + t) x hy hx`. Rewrite `hl` using `[add_sub_cancel_left, hnt]`. Establish `hlt : ‖P.derivative.eval (x + t) - P.derivative.eval x‖ < ‖P.derivative.eval x‖`. Rewrite using `[h1]`. Conclude with `lt_of_le_of_lt hl h0`.

Use `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, max_eq_right hlt.le, h1]`. Conclude with `this`. Establish `hz : P.eval x + P.derivative.eval x * t = 0`. Rewrite using `[ht]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he, hz, zero_add, norm_mul, norm_pow, hnt]`. Conclude with `mul_le_of_le_one_left (by positivity) hk`. Rewrite using `[add_sub_cancel_left, hnt]`.
-/
theorem newton_step (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x : K) (hx : ‖x‖ ≤ 1)
    (h0 : ‖P.eval x‖ < 1) (h1 : ‖P.derivative.eval x‖ = 1) :
    ∃ y : K, ‖y‖ ≤ 1 ∧ ‖P.derivative.eval y‖ = 1 ∧ ‖P.eval y‖ ≤ ‖P.eval x‖ ^ 2 ∧
      ‖y - x‖ ≤ ‖P.eval x‖ := by
  have hd : P.derivative.eval x ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  set t : K := -(P.eval x / P.derivative.eval x) with ht
  have hnt : ‖t‖ = ‖P.eval x‖ := by rw [ht, norm_neg, norm_div, h1, div_one]
  have ht1 : ‖t‖ ≤ 1 := hnt ▸ h0.le
  have hy : ‖x + t‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x t).trans (max_le hx ht1)
  obtain ⟨k, hk, he⟩ := newton_expansion P hP x t hx ht1
  refine ⟨x + t, hy, ?_, ?_, ?_⟩
  · have hl := newton_lipschitz P.derivative (newton_derivative_coeff P hP) (x + t) x hy hx
    rw [add_sub_cancel_left, hnt] at hl
    have hlt : ‖P.derivative.eval (x + t) - P.derivative.eval x‖ < ‖P.derivative.eval x‖ := by
      rw [h1]; exact lt_of_le_of_lt hl h0
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne
    rw [sub_add_cancel, max_eq_right hlt.le, h1] at this
    exact this
  · have hz : P.eval x + P.derivative.eval x * t = 0 := by
      rw [ht]; field_simp; ring
    rw [he, hz, zero_add, norm_mul, norm_pow, hnt]
    exact mul_le_of_le_one_left (by positivity) hk
  · rw [add_sub_cancel_left, hnt]

end Ball

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/- English proof (translation)
Use `set c : ℝ := ‖P.eval x₀‖ with hc`. Establish `hc0 : 0 ≤ c` using `norm_nonneg _`. Set `S : Type` to `{x : K // ‖x‖ ≤ 1 ∧ ‖P.eval x‖ < 1 ∧ ‖P.derivative.eval x‖ = 1}`. Establish `step : ∀ s : S, ∃ s' : S, ‖P.eval s'.1‖ ≤ ‖P.eval s.1‖ ^ 2 ∧ ‖s'.1 - s.1‖ ≤ ‖P.eval s.1‖`. Introduce `s`.

Take `⟨y, hy, hy1, hy2, hy3⟩` from `newton_step P hP s.1 s.2.1 s.2.2.1 s.2.2.2`. Establish `: ‖P.eval y‖ < 1` using `lt_of_le_of_lt hy2 (pow_lt_one₀ (norm_nonneg _) s.2.2.1 two_ne_zero)`. Conclude with `⟨⟨y, hy, this, hy1⟩, hy2, hy3⟩`. Use `choose g hg1 hg2 using step`. Set `u : ℕ → S` to `fun n => Nat.rec ⟨x₀, hx, h0, h1⟩ (fun _ s => g s) n`.

Establish `hu0 : (u 0).1 = x₀` using `rfl`. Establish `hus : ∀ n, u (n + 1) = g (u n)` using `fun _ => rfl`. Establish `hval : ∀ n, ‖P.eval (u n).1‖ ≤ c * c ^ n`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => rw [hu0, pow_zero, mul_one]`. Consider the case `succ n ih`. Establish `hle : ‖P.eval (u n).1‖ ≤ c` using `ih.trans (mul_le_of_le_one_right hc0 (pow_le_one₀ hc0 h0.le))`. Combine the equalities or inequalities in the displayed calculation. Establish `hdist : ∀ n, dist (u n).1 (u (n + 1)).1 ≤ c * c ^ n`.

Introduce `n`. Rewrite using `[dist_comm, dist_eq_norm, hus]`. Conclude with `(hg2 _).trans (hval n)`. Establish `hcau : CauchySeq (fun n => (u n).1)` using `cauchySeq_of_le_geometric c c h0 hdist`. Take `⟨x, hxl⟩` from `cauchySeq_tendsto_of_complete hcau`.

Establish `hnear : ∀ n, ‖(u n).1 - x₀‖ ≤ c`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [hu0, sub_self, norm_zero]`. Conclude with `hc0`.

Consider the case `succ n ih`. Establish `h2 : ‖(u (n + 1)).1 - (u n).1‖ ≤ c`. Rewrite using `[← dist_eq_norm, dist_comm]`. Conclude with `(hdist n).trans (mul_le_of_le_one_right hc0 (pow_le_one₀ hc0 h0.le))`. Use `IsUltrametricDist.norm_add_le_max ((u (n + 1)).1 - (u n).1) ((u n).1 - x₀)` as an intermediate fact.

Rewrite `this` using `[sub_add_sub_cancel]`. Conclude with `this.trans (max_le h2 ih)`. Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Establish `hl1 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop (nhds (P.eval x))` using `(P.continuous.tendsto x).comp hxl`. Establish `hl2 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop (nhds 0)`.

Apply `squeeze_zero_norm hval` to reduce the goal to its premises. Use `(tendsto_pow_atTop_nhds_zero_of_lt_one hc0 h0).const_mul c` as an intermediate fact. Rewrite `this` using `[mul_zero]`. Then use the resulting hypothesis. Conclude with `tendsto_nhds_unique hl1 hl2`. Establish `hl : Filter.Tendsto (fun n => ‖(u n).1 - x₀‖) Filter.atTop (nhds ‖x - x₀‖)` using `(hxl.sub_const x₀).norm`.

Conclude with `le_of_tendsto' hl hnear`.
-/
theorem newton_root (P : Polynomial K) (hP : ∀ i, ‖P.coeff i‖ ≤ 1) (x₀ : K) (hx : ‖x₀‖ ≤ 1)
    (h0 : ‖P.eval x₀‖ < 1) (h1 : ‖P.derivative.eval x₀‖ = 1) :
    ∃ x : K, P.eval x = 0 ∧ ‖x - x₀‖ ≤ ‖P.eval x₀‖ := by
  set c : ℝ := ‖P.eval x₀‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  let S : Type := {x : K // ‖x‖ ≤ 1 ∧ ‖P.eval x‖ < 1 ∧ ‖P.derivative.eval x‖ = 1}
  have step : ∀ s : S, ∃ s' : S, ‖P.eval s'.1‖ ≤ ‖P.eval s.1‖ ^ 2 ∧
      ‖s'.1 - s.1‖ ≤ ‖P.eval s.1‖ := by
    intro s
    obtain ⟨y, hy, hy1, hy2, hy3⟩ := newton_step P hP s.1 s.2.1 s.2.2.1 s.2.2.2
    have : ‖P.eval y‖ < 1 :=
      lt_of_le_of_lt hy2 (pow_lt_one₀ (norm_nonneg _) s.2.2.1 two_ne_zero)
    exact ⟨⟨y, hy, this, hy1⟩, hy2, hy3⟩
  choose g hg1 hg2 using step
  let u : ℕ → S := fun n => Nat.rec ⟨x₀, hx, h0, h1⟩ (fun _ s => g s) n
  have hu0 : (u 0).1 = x₀ := rfl
  have hus : ∀ n, u (n + 1) = g (u n) := fun _ => rfl
  have hval : ∀ n, ‖P.eval (u n).1‖ ≤ c * c ^ n := by
    intro n
    induction n with
    | zero => rw [hu0, pow_zero, mul_one]
    | succ n ih =>
      have hle : ‖P.eval (u n).1‖ ≤ c :=
        ih.trans (mul_le_of_le_one_right hc0 (pow_le_one₀ hc0 h0.le))
      calc ‖P.eval (u (n + 1)).1‖ ≤ ‖P.eval (u n).1‖ ^ 2 := by rw [hus]; exact hg1 _
        _ = ‖P.eval (u n).1‖ * ‖P.eval (u n).1‖ := sq _
        _ ≤ (c * c ^ n) * c := mul_le_mul ih hle (norm_nonneg _) (by positivity)
        _ = c * c ^ (n + 1) := by ring
  have hdist : ∀ n, dist (u n).1 (u (n + 1)).1 ≤ c * c ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, hus]
    exact (hg2 _).trans (hval n)
  have hcau : CauchySeq (fun n => (u n).1) := cauchySeq_of_le_geometric c c h0 hdist
  obtain ⟨x, hxl⟩ := cauchySeq_tendsto_of_complete hcau
  have hnear : ∀ n, ‖(u n).1 - x₀‖ ≤ c := by
    intro n
    induction n with
    | zero => rw [hu0, sub_self, norm_zero]; exact hc0
    | succ n ih =>
      have h2 : ‖(u (n + 1)).1 - (u n).1‖ ≤ c := by
        rw [← dist_eq_norm, dist_comm]
        exact (hdist n).trans (mul_le_of_le_one_right hc0 (pow_le_one₀ hc0 h0.le))
      have := IsUltrametricDist.norm_add_le_max ((u (n + 1)).1 - (u n).1) ((u n).1 - x₀)
      rw [sub_add_sub_cancel] at this
      exact this.trans (max_le h2 ih)
  refine ⟨x, ?_, ?_⟩
  · have hl1 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop (nhds (P.eval x)) :=
      (P.continuous.tendsto x).comp hxl
    have hl2 : Filter.Tendsto (fun n => P.eval (u n).1) Filter.atTop (nhds 0) := by
      apply squeeze_zero_norm hval
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 h0).const_mul c
      rwa [mul_zero] at this
    exact tendsto_nhds_unique hl1 hl2
  · have hl : Filter.Tendsto (fun n => ‖(u n).1 - x₀‖) Filter.atTop (nhds ‖x - x₀‖) :=
      (hxl.sub_const x₀).norm
    exact le_of_tendsto' hl hnear

end ReciprocityTheory.ChartRestriction.L1
