import Mathlib
import Formalism.SharpRestriction.ParConsts

open Formalism.MainNotions Formalism.BasicNotions Filter

namespace GlobalTheory

/- English proof (translation)
Take `⟨-, hM, hK, -, hT, hC, hQ, -, -, -, -, -, -, -, -, -, hD, -⟩` from `h`. Establish `hx1` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `he0` using `L.sc.eps_pos`. Establish `he1` using `L.sc.eps_lt`.

Establish `hL0 : 0 ≤ L.sc.L` using `by unfold Scale.L; positivity`. Establish `hb1 : 1 ≤ L.sc.b` using `Real.one_le_exp hL0`. Use `⟨?_, h2, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `h1.trans (le_trans ?_ hM.1)` and prove the remaining obligations. Establish `e : Real.sqrt (L.sc.x * L.sc.delta1) = L.sc.x ^ ((1 + -(L.sc.eps / 8)) * (1 / 2))`.

Rewrite using `[Real.sqrt_eq_rpow, Real.rpow_mul hx0.le, Real.rpow_add hx0, Real.rpow_one]`. Both sides reduce to the same expression. Rewrite using `[e, ← Real.rpow_add hx0]`. Apply `Real.rpow_le_rpow_of_exponent_le hx1.le` to reduce the goal to its premises. Unfold `szTh`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Use `D.R.m_add_three_le_k` as an intermediate fact. Conclude with `(by omega : 1 ≤ D.R.k)` after adjusting the coercions. Establish `hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ)`.

Use `hK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)` and prove the remaining obligations. Unfold `szTh`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0, mul_comm]`.

Use `_ ≤ L.sc.b := Real.exp_le_exp.mpr h3`. Establish `hr` using `hQ.2.2.2.2.2.2.2`. Establish `hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d`. Establish `hn : ∀ n : ℕ, Real.sqrt n ≤ n`. Introduce `n`.

Rewrite using `[Real.sqrt_le_left (by positivity)]`. Conclude with `Nat.le_self_pow two_ne_zero n` after adjusting the coercions. Conclude with `hn (D.host.q * D.host.d)` after adjusting the coercions. Establish `hn0 : (0 : ℝ) ≤ D.R.n` using `by positivity`. Establish `hqd : (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d` using `by positivity`.

Establish `hc : D.host.rdE ≤ szCond L`. Unfold `szCond`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hs hn0, mul_nonneg hn0 hqd]`. Use `hc.trans ?_` and prove the remaining obligations. Break down `le_total (szCond L) 1 with h | h` into its components or cases.

Conclude with `h.trans hb1`. Establish `ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150` using `one_le_pow₀ hT.1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.sqrt_le_left (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.

Use `le_trans ?_ hD.1` and prove the remaining obligations. Establish `: (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ)`. Conclude with `Nat.le_add_right _ _` after adjusting the coercions. Use `gcongr`.
-/
theorem sizes_large_of_power_bounds {D : D7} (L : SizeData₂ D) (h : SizesAt L) (M : ℝ)
    (h1 : M ≤ L.sc.x ^ (1 / 4 : ℝ)) (h2 : M ≤ L.sc.x ^ L.sc.eps)
    (h3 : 5 * |M| * Real.log L.sc.x ≤ L.sc.x ^ L.sc.eps) :
    M ≤ (D.R.m : ℝ) ∧ M ≤ L.sc.L ∧ (D.R.k : ℝ) ^ M ≤ L.sc.b ∧ D.host.rdE ≤ L.sc.b ∧
      (D.R.k : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ) := by
  obtain ⟨-, hM, hK, -, hT, hC, hQ, -, -, -, -, -, -, -, -, -, hD, -⟩ := h
  have hx1 := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hL0 : 0 ≤ L.sc.L := by unfold Scale.L; positivity
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp hL0
  refine ⟨?_, h2, ?_, ?_, ?_⟩
  · refine h1.trans (le_trans ?_ hM.1)
    have e : Real.sqrt (L.sc.x * L.sc.delta1) = L.sc.x ^ ((1 + -(L.sc.eps / 8)) * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_mul hx0.le, Real.rpow_add hx0, Real.rpow_one]
      rfl
    rw [e, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    unfold szTh
    linarith
  · have hk1 : (1 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ D.R.k)
    have hk5 : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := by
      refine hK.2.trans (Real.rpow_le_rpow_of_exponent_le hx1.le ?_)
      unfold szTh
      linarith
    calc (D.R.k : ℝ) ^ M ≤ (D.R.k : ℝ) ^ |M| := Real.rpow_le_rpow_of_exponent_le hk1 (le_abs_self M)
      _ ≤ (L.sc.x ^ (5 : ℝ)) ^ |M| := Real.rpow_le_rpow (by linarith) hk5 (abs_nonneg M)
      _ = Real.exp (5 * |M| * Real.log L.sc.x) := by
          rw [← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0, mul_comm]
      _ ≤ L.sc.b := Real.exp_le_exp.mpr h3
  · have hr := hQ.2.2.2.2.2.2.2
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
      have hn : ∀ n : ℕ, Real.sqrt n ≤ n := by
        intro n
        rw [Real.sqrt_le_left (by positivity)]
        exact_mod_cast Nat.le_self_pow two_ne_zero n
      exact_mod_cast hn (D.host.q * D.host.d)
    have hn0 : (0 : ℝ) ≤ D.R.n := by positivity
    have hqd : (0 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by positivity
    have hc : D.host.rdE ≤ szCond L := by
      unfold szCond
      nlinarith [mul_le_mul_of_nonneg_left hs hn0, mul_nonneg hn0 hqd]
    refine hc.trans ?_
    rcases le_total (szCond L) 1 with h | h
    · exact h.trans hb1
    · have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ hT.1
      calc szCond L ≤ szCond L ^ 36 := le_self_pow₀ h (by norm_num)
        _ ≤ szCond L ^ 36 * (D.R.t : ℝ) ^ 150 := le_mul_of_one_le_right (by positivity) ht
        _ ≤ Real.sqrt L.sc.b := hC
        _ ≤ L.sc.b := by
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
  · refine le_trans ?_ hD.1
    have : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    gcongr

/- English proof (translation)
Introduce `eps Fm M`. Establish `he : 0 < eps`. Take `⟨i⟩` from `Fm.Ix_zero`. Rewrite using `[← Fm.L_eps 0 i]`. Conclude with `(Fm.L 0 i).sc.eps_pos`.

Establish `e1 : ∀ᶠ x : ℝ in atTop, M ≤ x ^ (1 / 4 : ℝ)` using `(tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop M`. Establish `e2 : ∀ᶠ x : ℝ in atTop, M ≤ x ^ eps` using `(tendsto_rpow_atTop he).eventually_ge_atTop M`. Establish `e3 : ∀ᶠ x : ℝ in atTop, 5 * |M| * Real.log x ≤ x ^ eps`. Use `((isLittleO_log_rpow_atTop he).const_mul_left (5 * |M|)).bound one_pos` as an intermediate fact. Use `filter_upwards [this, eventually_ge_atTop 0] with x hx h0`.

Rewrite `hx` using `[one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)]`. Conclude with `(le_abs_self _).trans hx`. Take `⟨x0, hx0⟩` from `eventually_atTop.mp (e1.and (e2.and (e3.and (eventually_gt_atTop Fm.x1))))`. Use `⟨x0, fun x hx i => ?_⟩` and prove the remaining obligations. Take `⟨a1, a2, a3, a4⟩` from `hx0 x hx`.

Apply the tactic sequence `refine ⟨a4, sizes_large_of_power_bounds (Fm.L x i) (Fm.sizes x a4 i) M ?_ ?_ ?_⟩ <;>`. Apply the tactic sequence `simp only [Fm.L_x x i a4, Fm.L_eps x i] <;> assumption`.
-/
theorem family_sizes_eventually_large : ∀ (eps : ℝ) (Fm : FamP eps) (M : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Fm.x1 < x ∧ M ≤ ((Fm.D x i).R.m : ℝ) ∧ M ≤ (Fm.L x i).sc.L ∧ ((Fm.D x i).R.k : ℝ) ^ M ≤ (Fm.L x i).sc.b ∧ (Fm.D x i).host.rdE ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * ((Fm.D x i).R.m : ℝ) ^ 10 ≤ ((Fm.D x i).s.Del : ℝ) := by
  intro eps Fm M
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]
    exact (Fm.L 0 i).sc.eps_pos
  have e1 : ∀ᶠ x : ℝ in atTop, M ≤ x ^ (1 / 4 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop M
  have e2 : ∀ᶠ x : ℝ in atTop, M ≤ x ^ eps := (tendsto_rpow_atTop he).eventually_ge_atTop M
  have e3 : ∀ᶠ x : ℝ in atTop, 5 * |M| * Real.log x ≤ x ^ eps := by
    have := ((isLittleO_log_rpow_atTop he).const_mul_left (5 * |M|)).bound one_pos
    filter_upwards [this, eventually_ge_atTop 0] with x hx h0
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)] at hx
    exact (le_abs_self _).trans hx
  obtain ⟨x0, hx0⟩ := eventually_atTop.mp (e1.and (e2.and (e3.and (eventually_gt_atTop Fm.x1))))
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hx0 x hx
  refine ⟨a4, sizes_large_of_power_bounds (Fm.L x i) (Fm.sizes x a4 i) M ?_ ?_ ?_⟩ <;>
    simp only [Fm.L_x x i a4, Fm.L_eps x i] <;> assumption

end GlobalTheory
