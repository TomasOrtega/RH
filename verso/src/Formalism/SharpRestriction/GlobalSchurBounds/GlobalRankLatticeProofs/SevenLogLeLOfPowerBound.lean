import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

namespace Formalism.MainNotions.flipTwoThree

open Formalism.BasicNotions Formalism.MainNotions

/- English proof (translation)
Establish `hi' : i < R.k - 1` using `by omega`. Establish `h1` using `h.u_gt_v ⟨i, hi'⟩`. Establish `h2` using `h.v_gt_u ⟨i, hi'⟩`. Take `⟨a, ha⟩` from `h.u_half ⟨i + 1, hi⟩`. Take `⟨b, hb⟩` from `h.u_half ⟨i, by omega⟩`.

Take `⟨c, hc⟩` from `h.v_int ⟨i, hi'⟩`. Establish `e1 : (a : ℚ) + 1 / 2 < c`. Establish `h2' : h.u ⟨i + 1, hi⟩ < h.v ⟨i, hi'⟩` using `h2`. Rewrite `h2'` using `[ha, hc]`. Conclude with `h2'`.

Establish `e2 : (c : ℚ) < b + 1 / 2`. Establish `h1' : h.v ⟨i, hi'⟩ < h.u ⟨i, by omega⟩` using `h1`. Rewrite `h1'` using `[hb, hc]`. Conclude with `h1'`. Establish `f1 : a < c` using `by exact_mod_cast (show (a : ℚ) < c by linarith)`.

Establish `f2 : c < b + 1` using `by exact_mod_cast (show (c : ℚ) < b + 1 by linarith)`. Establish `f3 : ((a + 1 : ℤ) : ℚ) ≤ b` using `by exact_mod_cast (show a + 1 ≤ b by omega)`. Move the coercions through the operations in `at f3`. Rewrite using `[ha, hb]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hc_u_step {R : Ranks} (h : HCParam R) (i : ℕ) (hi : i + 1 < R.k) :
    h.u ⟨i + 1, hi⟩ + 1 ≤ h.u ⟨i, by omega⟩ := by
  have hi' : i < R.k - 1 := by omega
  have h1 := h.u_gt_v ⟨i, hi'⟩
  have h2 := h.v_gt_u ⟨i, hi'⟩
  obtain ⟨a, ha⟩ := h.u_half ⟨i + 1, hi⟩
  obtain ⟨b, hb⟩ := h.u_half ⟨i, by omega⟩
  obtain ⟨c, hc⟩ := h.v_int ⟨i, hi'⟩
  have e1 : (a : ℚ) + 1 / 2 < c := by
    have h2' : h.u ⟨i + 1, hi⟩ < h.v ⟨i, hi'⟩ := h2
    rw [ha, hc] at h2'
    exact h2'
  have e2 : (c : ℚ) < b + 1 / 2 := by
    have h1' : h.v ⟨i, hi'⟩ < h.u ⟨i, by omega⟩ := h1
    rw [hb, hc] at h1'
    exact h1'
  have f1 : a < c := by exact_mod_cast (show (a : ℚ) < c by linarith)
  have f2 : c < b + 1 := by exact_mod_cast (show (c : ℚ) < b + 1 by linarith)
  have f3 : ((a + 1 : ℤ) : ℚ) ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
  push_cast at f3
  rw [ha, hb]
  linarith

/- English proof (translation)
Rewrite using `[lamCol, dif_pos hi]`. Simplify using `only [hcToWeightQ, rhoVec, Fin.val_mk]`.
-/
theorem lamCol_eq (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (hi : i < D.R.k) :
    lamCol D u τ i = (D.hcW u τ).u ⟨i, hi⟩ - (((D.R.k : ℚ) - 1) / 2 - i) := by
  rw [lamCol, dif_pos hi]
  simp only [hcToWeightQ, rhoVec, Fin.val_mk]

/- English proof (translation)
Rewrite using `[wJ, dif_pos hj, wG, D.hcW_e]`. Apply the tactic sequence `push_cast <;> ring`.
-/
theorem wJ_eq (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    wJ D u τ j = (D.hc τ).e ⟨j, hj⟩ - (D.R.k : ℚ) / 2 - (2 * ((j : ℚ) + 1) - 1) * ((D.R.t : ℚ) + 1) / 2 := by
  rw [wJ, dif_pos hj, wG, D.hcW_e]
  push_cast <;> ring

/- English proof (translation)
Establish `h : j + 1 - 1 < D.R.m` using `by omega`. Rewrite using `[wj, dif_pos h]`. Establish `e : (⟨j + 1 - 1, h⟩ : Fin D.R.m) = ⟨j, hj⟩` using `Fin.ext (by simp)`. Rewrite using `[e]`.
-/
theorem wj_eq (D : D7) (τ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    wj D (j + 1) τ = (((D.hc τ).e ⟨j, hj⟩ : ℚ) : ℝ) := by
  have h : j + 1 - 1 < D.R.m := by omega
  rw [wj, dif_pos h]
  have e : (⟨j + 1 - 1, h⟩ : Fin D.R.m) = ⟨j, hj⟩ := Fin.ext (by simp)
  rw [e]

/- English proof (translation)
Rewrite using `[lamCol_eq D u τ (i + 1) hi, lamCol_eq D u τ i (by omega)]`. Use `hc_u_step (D.hcW u τ) i hi` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lamCol_step (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (hi : i + 1 < D.R.k) :
    lamCol D u τ (i + 1) ≤ lamCol D u τ i := by
  rw [lamCol_eq D u τ (i + 1) hi, lamCol_eq D u τ i (by omega)]
  have := hc_u_step (D.hcW u τ) i hi
  push_cast
  linarith

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hij`. Proceed by induction on `d with`. Consider the case `zero => exact le_rfl`. Consider the case `succ d ih`. Establish `h1` using `lamCol_step D u τ (i + d) (by omega)`.

Establish `h2` using `ih (by omega) (by omega)`. Conclude with `h1.trans h2`.
-/
theorem lamCol_anti (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i j : ℕ) (hij : i ≤ j) (hj : j < D.R.k) :
    lamCol D u τ j ≤ lamCol D u τ i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    have h1 := lamCol_step D u τ (i + d) (by omega)
    have h2 := ih (by omega) (by omega)
    exact h1.trans h2

/- English proof (translation)
Take `⟨z, hz⟩` from `(D.hcW u τ).u_half ⟨i, hi⟩`. Take `⟨r, hr⟩` from `D.R.k_even`. Establish `hk : (D.R.k : ℚ) = (r : ℚ) + r` using `by exact_mod_cast hr`. Use `⟨z + 1 - r + i, ?_⟩` and prove the remaining obligations. Rewrite using `[lamCol_eq D u τ i hi, hz, hk]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lamCol_int (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (hi : i < D.R.k) :
    ∃ z : ℤ, lamCol D u τ i = z := by
  obtain ⟨z, hz⟩ := (D.hcW u τ).u_half ⟨i, hi⟩
  obtain ⟨r, hr⟩ := D.R.k_even
  have hk : (D.R.k : ℚ) = (r : ℚ) + r := by exact_mod_cast hr
  refine ⟨z + 1 - r + i, ?_⟩
  rw [lamCol_eq D u τ i hi, hz, hk]
  push_cast
  ring

/- English proof (translation)
Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `ht1 : (1 : ℝ) ≤ D.R.t`. Use `D.R.three_m_lt_t` as an intermediate fact. Use `D.R.two_le_m` as an intermediate fact. Conclude with `(by omega : 1 ≤ D.R.t)` after adjusting the coercions.

Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Use `D.R.m_add_three_le_k` as an intermediate fact. Conclude with `(by omega : 1 ≤ D.R.k)` after adjusting the coercions. Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`.

Conclude with `this` after adjusting the coercions. Establish `hx` using `L.sc.one_lt_alt`. Establish `hη : 1 ≤ L.etaSz` using `le_trans ht1 P.t_le_eta`. Establish `hN0 : (0 : ℝ) ≤ D.R.N D.R.m` using `Nat.cast_nonneg _`. Establish `h1` using `P.h0_ge.2.2.2.2.2.2.2.2.1`.

Unfold `LevelStarExponents.h0 at h1`. Rewrite `h1` using `[le_div_iff₀ (by linarith)]`. Establish `h2` using `P.mteta`. Establish `hb' : 0 < L.sc.b'`. Unfold `Scale.b' Scale.a Scale.X' Scale.b`.

Establish `: 0 < L.sc.x` using `by linarith`. Check the signs of the components of the expression. Establish `hmη : (D.R.m : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n`. Use `le_trans ?_ h2` and prove the remaining obligations. Establish `: 0 ≤ (D.R.m : ℝ) * L.etaSz * D.R.t` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hW0 : 0 ≤ L.sc.w'' D.R.n` using `le_trans (by positivity) hmη`. Use `⟨?_, ?_, ?_, ?_, ?_, hη, hb'⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities.

Use `P.kS_le` as an intermediate fact. Establish `hS` using `L.Sc_pos`. Use the polynomial consequences of the given equalities and inequalities. Use `le_trans ?_ h2` and prove the remaining obligations. Establish `: (D.R.m : ℝ) * D.R.t ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)` using `by nlinarith`.

Establish `h3 : 0 ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Unfold `Scale.w''`. Clear the denominators using the available nonvanishing facts.
-/
theorem base_sizes {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) :
    (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 12 ≤ L.sc.w'' D.R.n ∧ L.etaSz ≤ L.sc.w'' D.R.n ∧
    L.Sc ≤ L.sc.w'' D.R.n ∧ (D.R.m : ℝ) * D.R.t ≤ L.sc.w'' D.R.n ∧
    L.sc.b' = L.sc.x * D.R.n * L.sc.w'' D.R.n ∧ 1 ≤ L.etaSz ∧ 0 < L.sc.b' := by
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hx := L.sc.one_lt_alt
  have hη : 1 ≤ L.etaSz := le_trans ht1 P.t_le_eta
  have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have h1 := P.h0_ge.2.2.2.2.2.2.2.2.1
  unfold LevelStarExponents.h0 at h1
  rw [le_div_iff₀ (by linarith)] at h1
  have h2 := P.mteta
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    have : 0 < L.sc.x := by linarith
    positivity
  have hmη : (D.R.m : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n := by
    refine le_trans ?_ h2
    have : 0 ≤ (D.R.m : ℝ) * L.etaSz * D.R.t := by positivity
    nlinarith
  have hW0 : 0 ≤ L.sc.w'' D.R.n := le_trans (by positivity) hmη
  refine ⟨?_, ?_, ?_, ?_, ?_, hη, hb'⟩
  · calc (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 12 = (D.R.m : ℝ) * ((D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 * D.R.m) := by ring
      _ ≤ (D.R.m : ℝ) * L.etaSz := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ _ := hmη
  · nlinarith
  · have := P.kS_le
    have hS := L.Sc_pos
    nlinarith
  · refine le_trans ?_ h2
    have : (D.R.m : ℝ) * D.R.t ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by nlinarith
    have h3 : 0 ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by positivity
    nlinarith
  · unfold Scale.w''
    field_simp

/- English proof (translation)
Unfold `IsTop Host.topPlaces at h`. Take `⟨t0, ht0, ht0e⟩` from `Finset.mem_image.mp h`. Conclude with `⟨⟨t0, ht0⟩, ht0e.symm⟩`.
-/
theorem top_is_tau_one_place (D : D7) (τ : D.what₂.Tau) (h : IsTop D τ) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold IsTop Host.topPlaces at h
  obtain ⟨t0, ht0, ht0e⟩ := Finset.mem_image.mp h
  exact ⟨⟨t0, ht0⟩, ht0e.symm⟩

/- English proof (translation)
Establish `h1` using `R.m_add_three_le_k`. Establish `h2` using `R.two_le_m`. Use linear arithmetic over natural numbers and integers.
-/
theorem five_le_k (R : Ranks) : 5 ≤ R.k := by
  have h1 := R.m_add_three_le_k
  have h2 := R.two_le_m
  omega

/- English proof (translation)
Rewrite using `[lamCol_eq D u τ i hi]`. Apply the tactic sequence `push_cast <;> ring`.
-/
theorem lamCol_real (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (hi : i < D.R.k) :
    ((lamCol D u τ i : ℚ) : ℝ) = (((D.hcW u τ).u ⟨i, hi⟩ : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2 - i) := by
  rw [lamCol_eq D u τ i hi]
  push_cast <;> ring

/- English proof (translation)
Conclude with `lamCol_anti D u τ i j hij hj` after adjusting the coercions.
-/
theorem lamCol_anti_real (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i j : ℕ) (hij : i ≤ j) (hj : j < D.R.k) :
    ((lamCol D u τ j : ℚ) : ℝ) ≤ ((lamCol D u τ i : ℚ) : ℝ) := by
  exact_mod_cast lamCol_anti D u τ i j hij hj

/- English proof (translation)
Rewrite using `[wJ_eq D u τ j hj, wj_eq D τ j hj]`. Apply the tactic sequence `push_cast <;> ring`.
-/
theorem wJ_real (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    ((wJ D u τ j : ℚ) : ℝ) = wj D (j + 1) τ -
      ((D.R.k : ℝ) / 2 + (2 * ((j : ℝ) + 1) - 1) * ((D.R.t : ℝ) + 1) / 2) := by
  rw [wJ_eq D u τ j hj, wj_eq D τ j hj]
  push_cast <;> ring

/- English proof (translation)
Take `⟨-, -, -, -, -, -, s7⟩` from `base_sizes P`. Establish `hx` using `L.sc.one_lt_alt`. Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast five_le_k D.R`. Establish `hS0` using `L.Sc_pos`. Establish `h1` using `P.bT_le t`.

Establish `h2` using `P.rho_le`. Unfold `LevelStarExponents.rhoP at h2`. Establish `hΛ : 0 < L.LaG`. Establish `h3` using `P.S_le`. Assume the negation of the conclusion as `hh`.

Establish `hh` using `not_lt.mp hh`. Establish `: L.LaG * L.sc.b' / D.R.k ≤ 0` using `div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hh s7.le) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k`. Use `Real.log_nonneg hx.le` as an intermediate fact.

Use `P.Crho_pos` as an intermediate fact. Check the signs of the components of the expression. Establish `h5 : L.sc.x ^ (-2 : ℝ) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)`. Establish `h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b'` using `by ring`. Establish `h7 : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k)` using `by ring`.

Rewrite `h1` using `[h6]`. Rewrite `h2` using `[h7]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem bT_le_five_quarters_alt {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  obtain ⟨-, -, -, -, -, -, s7⟩ := base_sizes P
  have hx := L.sc.one_lt_alt
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast five_le_k D.R
  have hS0 := L.Sc_pos
  have h1 := P.bT_le t
  have h2 := P.rho_le
  unfold LevelStarExponents.rhoP at h2
  have hΛ : 0 < L.LaG := by
    have h3 := P.S_le
    by_contra hh
    have hh := not_lt.mp hh
    have : L.LaG * L.sc.b' / D.R.k ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hh s7.le) (by linarith)
    linarith
  have h4 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k := by
    have := Real.log_nonneg hx.le
    have := P.Crho_pos
    positivity
  have h5 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  have h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h7 : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
      4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
  rw [h6] at h1
  rw [h7] at h2
  nlinarith

/- English proof (translation)
Establish `hk` using `five_le_k D.R`. Establish `h0 : 0 < D.R.k` using `by omega`. Take `⟨hu1, huk⟩` from `L.top_u τ t h0 ht`. Prove the components needed by the constructor for the conclusion. Rewrite using `[lamCol_real D u τ 0 h0, D.hcW_first u τ h0, hu1]`.

Apply the tactic sequence `push_cast <;> ring`. Rewrite using `[lamCol_real D u τ (D.R.k - 1) (by omega), D.hcW_last u τ h0, huk]`. Establish `hc : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1`. Rewrite using `[Nat.cast_sub (show 1 ≤ D.R.k by omega), Nat.cast_one]`. Rewrite using `[hc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lam_top {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (τ : D.what₂.Tau) (t : D.host.TT)
    (ht : (D.eTau τ : D.R.GG) = D.R.tau1 t) :
    ((lamCol D u τ 0 : ℚ) : ℝ) = L.aT t ∧ ((lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) = -(L.bT t : ℝ) := by
  have hk := five_le_k D.R
  have h0 : 0 < D.R.k := by omega
  obtain ⟨hu1, huk⟩ := L.top_u τ t h0 ht
  constructor
  · rw [lamCol_real D u τ 0 h0, D.hcW_first u τ h0, hu1]
    push_cast <;> ring
  · rw [lamCol_real D u τ (D.R.k - 1) (by omega), D.hcW_last u τ h0, huk]
    have hc : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ D.R.k by omega), Nat.cast_one]
    rw [hc]
    ring

/- English proof (translation)
Establish `hkN` using `five_le_k D.R`. Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hkN`. Establish `hk1c : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]; norm_num`. Establish `hT' : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces` using `hT`.

Prove the components needed by the constructor for the conclusion. Use `le_trans ?_ (lamCol_anti_real D u τ i (D.R.k - 1) (by omega) (by omega))` and prove the remaining obligations. Rewrite using `[lamCol_real D u τ (D.R.k - 1) (by omega), D.hcW_last u τ (by omega), P.uk_extreme τ (by omega) hT', hk1c]`. Use `(L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1` as an intermediate fact. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `le_trans (lamCol_anti_real D u τ 0 i (by omega) hi) ?_` and prove the remaining obligations. Rewrite using `[lamCol_real D u τ 0 (by omega), D.hcW_first u τ (by omega)]`. Establish `h1` using `P.cloud_place_bound τ (by omega) hT'`. Establish `h2` using `(L.cloud_v τ ⟨0, by omega⟩).2`.

Move the coercions through the operations in `at h1 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lam_off {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (hT : ¬ IsTop D τ) (i : ℕ) (hi : i < D.R.k) :
    0 ≤ ((lamCol D u τ i : ℚ) : ℝ) ∧ ((lamCol D u τ i : ℚ) : ℝ) ≤ 3 * L.Sc := by
  have hkN := five_le_k D.R
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hkN
  have hk1c : ((D.R.k - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hT' : (D.eTau τ : D.R.GG) ∉ D.host.topPlaces := hT
  constructor
  · refine le_trans ?_ (lamCol_anti_real D u τ i (D.R.k - 1) (by omega) (by omega))
    rw [lamCol_real D u τ (D.R.k - 1) (by omega), D.hcW_last u τ (by omega), P.uk_extreme τ (by omega) hT', hk1c]
    have := (L.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
    push_cast
    linarith
  · refine le_trans (lamCol_anti_real D u τ 0 i (by omega) hi) ?_
    rw [lamCol_real D u τ 0 (by omega), D.hcW_first u τ (by omega)]
    have h1 := P.cloud_place_bound τ (by omega) hT'
    have h2 := (L.cloud_v τ ⟨0, by omega⟩).2
    push_cast at h1 ⊢
    linarith

/- English proof (translation)
Establish `hkN` using `five_le_k D.R`. Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hkN`. Establish `c1` using `(L.cloud_u u τ ⟨1, by omega⟩ (le_refl _) (by simp only; omega)).2`. Establish `c2` using `(L.cloud_u u τ ⟨D.R.k - 2, by omega⟩ (by simp only; omega) (by simp only; omega)).1`. Establish `hk2c : ((D.R.k - 2 : ℕ) : ℝ) = (D.R.k : ℝ) - 2`.

Rewrite using `[Nat.cast_sub (by omega)]; norm_num`. Prove the components needed by the constructor for the conclusion. Use `le_trans ?_ (lamCol_anti_real D u τ i (D.R.k - 2) (by omega) (by omega))` and prove the remaining obligations. Rewrite using `[lamCol_real D u τ (D.R.k - 2) (by omega), hk2c]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `le_trans (lamCol_anti_real D u τ 1 i (by omega) (by omega)) ?_` and prove the remaining obligations. Rewrite using `[lamCol_real D u τ 1 (by omega)]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lam_mid {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (hi0 : 0 < i)
    (hik : i < D.R.k - 1) :
    0 ≤ ((lamCol D u τ i : ℚ) : ℝ) ∧ ((lamCol D u τ i : ℚ) : ℝ) ≤ L.Sc := by
  have hkN := five_le_k D.R
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hkN
  have c1 := (L.cloud_u u τ ⟨1, by omega⟩ (le_refl _) (by simp only; omega)).2
  have c2 := (L.cloud_u u τ ⟨D.R.k - 2, by omega⟩ (by simp only; omega) (by simp only; omega)).1
  have hk2c : ((D.R.k - 2 : ℕ) : ℝ) = (D.R.k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  constructor
  · refine le_trans ?_ (lamCol_anti_real D u τ i (D.R.k - 2) (by omega) (by omega))
    rw [lamCol_real D u τ (D.R.k - 2) (by omega), hk2c]
    linarith
  · refine le_trans (lamCol_anti_real D u τ 1 i (by omega) (by omega)) ?_
    rw [lamCol_real D u τ 1 (by omega)]
    push_cast
    linarith

/- English proof (translation)
Take `⟨s1, s2, s3, s4, s5, s6, s7⟩` from `base_sizes P`. Establish `hx` using `L.sc.one_lt_alt`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`.

Conclude with `this` after adjusting the coercions. Establish `hN0 : (0 : ℝ) ≤ D.R.N D.R.m` using `Nat.cast_nonneg _`. Establish `hNW : (D.R.N D.R.m : ℝ) ≤ L.sc.w'' D.R.n`. Use `le_trans ?_ s1` and prove the remaining obligations. Conclude with `le_mul_of_one_le_right hN0 (one_le_pow₀ (by linarith))`.

Establish `hW0 : 0 ≤ L.sc.w'' D.R.n` using `le_trans hN0 hNW`. Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Use `⟨hNW, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[s5, le_div_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.

Unfold `Scale.b' Scale.a`. Rewrite using `[div_le_iff₀ (show 0 < L.sc.X' from Real.exp_pos _)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem base_sizes2 {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hX : L.sc.x ≤ L.sc.X') :
    (D.R.N D.R.m : ℝ) ≤ L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x ∧ L.sc.b' ≤ L.sc.b := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := base_sizes P
  have hx := L.sc.one_lt_alt
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hNW : (D.R.N D.R.m : ℝ) ≤ L.sc.w'' D.R.n := by
    refine le_trans ?_ s1
    exact le_mul_of_one_le_right hN0 (one_le_pow₀ (by linarith))
  have hW0 : 0 ≤ L.sc.w'' D.R.n := le_trans hN0 hNW
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  refine ⟨hNW, ?_, ?_⟩
  · rw [s5, le_div_iff₀ (by linarith)]
    nlinarith
  · unfold Scale.b' Scale.a
    rw [div_le_iff₀ (show 0 < L.sc.X' from Real.exp_pos _)]
    nlinarith

/- English proof (translation)
Establish `hj0 : (0 : ℝ) ≤ j` using `Nat.cast_nonneg j`. Establish `hk0 : (0 : ℝ) ≤ R.k` using `Nat.cast_nonneg _`. Establish `ht : (0 : ℝ) ≤ (R.t : ℝ) + 1` using `by positivity`. Establish `h2 : (0 : ℝ) ≤ 2 * ((j : ℝ) + 1) - 1` using `by linarith`. Prove the components needed by the constructor for the conclusion.

Use polynomial arithmetic with `[mul_nonneg h2 ht]`. Introduce `hj`. Establish `hjm : (j : ℝ) + 1 ≤ R.m` using `by exact_mod_cast hj`. Establish `hA : (0 : ℝ) ≤ 2 * (R.m : ℝ) - (2 * ((j : ℝ) + 1) - 1)` using `by linarith`. Rewrite using `[Ranks.N]`.

Use `push_cast`. Use polynomial arithmetic with `[mul_nonneg hA ht]`.
-/
theorem sub_aux (R : Ranks) (j : ℕ) :
    0 ≤ (R.k : ℝ) / 2 + (2 * ((j : ℝ) + 1) - 1) * ((R.t : ℝ) + 1) / 2 ∧
    (j < R.m → (R.k : ℝ) / 2 + (2 * ((j : ℝ) + 1) - 1) * ((R.t : ℝ) + 1) / 2 ≤ R.N R.m) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk0 : (0 : ℝ) ≤ R.k := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ (R.t : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) ≤ 2 * ((j : ℝ) + 1) - 1 := by linarith
  constructor
  · nlinarith [mul_nonneg h2 ht]
  · intro hj
    have hjm : (j : ℝ) + 1 ≤ R.m := by exact_mod_cast hj
    have hA : (0 : ℝ) ≤ 2 * (R.m : ℝ) - (2 * ((j : ℝ) + 1) - 1) := by linarith
    rw [Ranks.N]
    push_cast
    nlinarith [mul_nonneg hA ht]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, s7⟩` from `base_sizes P`. Establish `hx` using `L.sc.one_lt_alt`. Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast five_le_k D.R`. Establish `hS0` using `L.Sc_pos`. Prove the components needed by the constructor for the conclusion.

Introduce `hT`. Take `⟨t, ht⟩` from `top_is_tau_one_place D τ hT`. Take `⟨h1, h2⟩` from `lam_top L u τ t ht`. Take `⟨a1, a2⟩` from `L.aT_win t`. Establish `ha : L.sc.a = L.sc.x * L.sc.b` using `rfl`.

Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `ha0 : 0 < L.sc.a` using `by rw [ha]; positivity`. Rewrite using `[h1, h2, neg_neg, ← ha]`. Use `⟨a1, ?_, L.bT_ge t, ?_, fun i hi0 hik => lam_mid L u τ i hi0 hik⟩` and prove the remaining obligations. Use `le_trans a2 ?_` and prove the remaining obligations.

Establish `: L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a`. Apply `div_le_self ha0.le` to reduce the goal to its premises. Establish `: (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2)` using `Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Use `bT_le_five_quarters_alt P t` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hT i hi`. Take `⟨h1, h2⟩` from `lam_off P u τ hT i hi`. Conclude with `⟨h1, le_trans h2 (by nlinarith)⟩`.
-/
theorem wts_lam {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (Cn : ℝ) (hCn : 3 ≤ Cn) (u : D.what₂.Word)
    (τ : D.what₂.Tau) :
    (IsTop D τ → L.sc.x * L.sc.b ≤ (lamCol D u τ 0 : ℝ) ∧ (lamCol D u τ 0 : ℝ) ≤ 2 * (L.sc.x * L.sc.b) ∧
      L.sc.b' ≤ -(lamCol D u τ (D.R.k - 1) : ℝ) ∧ -(lamCol D u τ (D.R.k - 1) : ℝ) < 2 * L.sc.b' ∧
      ∀ i, 0 < i → i < D.R.k - 1 → 0 ≤ (lamCol D u τ i : ℝ) ∧ (lamCol D u τ i : ℝ) ≤ L.Sc) ∧
    (¬ IsTop D τ → ∀ i < D.R.k, 0 ≤ (lamCol D u τ i : ℝ) ∧ (lamCol D u τ i : ℝ) ≤ Cn * L.Sc) := by
  obtain ⟨-, -, -, -, -, -, s7⟩ := base_sizes P
  have hx := L.sc.one_lt_alt
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast five_le_k D.R
  have hS0 := L.Sc_pos
  constructor
  · intro hT
    obtain ⟨t, ht⟩ := top_is_tau_one_place D τ hT
    obtain ⟨h1, h2⟩ := lam_top L u τ t ht
    obtain ⟨a1, a2⟩ := L.aT_win t
    have ha : L.sc.a = L.sc.x * L.sc.b := rfl
    have hb0 : 0 < L.sc.b := Real.exp_pos _
    have ha0 : 0 < L.sc.a := by rw [ha]; positivity
    rw [h1, h2, neg_neg, ← ha]
    refine ⟨a1, ?_, L.bT_ge t, ?_, fun i hi0 hik => lam_mid L u τ i hi0 hik⟩
    · refine le_trans a2 ?_
      have : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a := by
        apply div_le_self ha0.le
        have : (1 : ℝ) ≤ L.sc.x ^ (Scale.A / 2) :=
          Real.one_le_rpow hx.le (by unfold Scale.A; norm_num)
        nlinarith
      linarith
    · have := bT_le_five_quarters_alt P t
      linarith
  · intro hT i hi
    obtain ⟨h1, h2⟩ := lam_off P u τ hT i hi
    exact ⟨h1, le_trans h2 (by nlinarith)⟩

/- English proof (translation)
Take `⟨s1, s2, s3, s4, s5, s6, s7⟩` from `base_sizes P`. Take `⟨r1, r2, r3⟩` from `base_sizes2 P hX`. Establish `hx` using `L.sc.one_lt_alt`. Establish `hbx : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self s7.le hx.le`. Distinguish the cases in `hT : IsTop D τ`.

Take `⟨t, ht⟩` from `top_is_tau_one_place D τ hT`. Use `⟨(L.bT t : ℝ) + L.sc.b' / L.sc.x, ?_, fun j h1 h2 => ?_⟩` and prove the remaining obligations. Use `L.bT_ge t` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨a, b⟩` from `L.win_top j h1 h2 τ t ht`.

Conclude with `⟨a, by linarith⟩`. Distinguish the cases in `hTh : IsThick D τ`. Conclude with `⟨L.sc.b, by linarith, fun j h1 h2 => L.win_thick j h1 h2 τ hTh⟩`. Use `⟨L.sc.w'' D.R.n, le_refl _, fun j h1 h2 => ?_⟩` and prove the remaining obligations. Take `⟨a, b⟩` from `L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, hT, hTh⟩`.

Conclude with `⟨a, by linarith⟩`.
-/
theorem weights_in_short_window {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hX : L.sc.x ≤ L.sc.X') (τ : D.what₂.Tau) :
    ∃ lo : ℝ, L.sc.w'' D.R.n ≤ lo ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → lo ≤ wj D j τ ∧ wj D j τ ≤ lo + L.etaSz + 1) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := base_sizes P
  obtain ⟨r1, r2, r3⟩ := base_sizes2 P hX
  have hx := L.sc.one_lt_alt
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self s7.le hx.le
  by_cases hT : IsTop D τ
  · obtain ⟨t, ht⟩ := top_is_tau_one_place D τ hT
    refine ⟨(L.bT t : ℝ) + L.sc.b' / L.sc.x, ?_, fun j h1 h2 => ?_⟩
    · have := L.bT_ge t
      linarith
    · obtain ⟨a, b⟩ := L.win_top j h1 h2 τ t ht
      exact ⟨a, by linarith⟩
  · by_cases hTh : IsThick D τ
    · exact ⟨L.sc.b, by linarith, fun j h1 h2 => L.win_thick j h1 h2 τ hTh⟩
    · refine ⟨L.sc.w'' D.R.n, le_refl _, fun j h1 h2 => ?_⟩
      obtain ⟨a, b⟩ := L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, hT, hTh⟩
      exact ⟨a, by linarith⟩

/- English proof (translation)
Take `⟨s1, s2, s3, s4, s5, s6, s7⟩` from `base_sizes P`. Take `⟨r1, r2, r3⟩` from `base_sizes2 P hX`. Establish `hbx : L.sc.b' / L.sc.x ≤ L.sc.b' / 4` using `div_le_div_of_nonneg_left s7.le (by norm_num) hx`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j hj`.

Rewrite using `[wJ_eq D u τ j (by omega), wJ_eq D u τ (j + 1) hj]`. Establish `g1` using `(D.hc τ).gap_be ⟨j + 1, hj⟩`. Establish `g2` using `(D.hc τ).gap_eb ⟨j, by omega⟩ hj`. Use `push_cast`. Simplify using `only at g2`.

Use the polynomial consequences of the given equalities and inequalities. Introduce `hTh j hj`. Rewrite using `[wJ_real D u τ j hj]`. Use `(sub_aux D.R j).1` as an intermediate fact. Distinguish the cases in `hT : IsTop D τ`.

Take `⟨t, ht⟩` from `top_is_tau_one_place D τ hT`. Establish `h1` using `(L.win_top (j + 1) (by omega) (by omega) τ t ht).2`. Use `bT_le_five_quarters_alt P t` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `(L.win_thin (j + 1) (by omega) (by omega) τ ⟨(D.eTau τ).2, hT, hTh⟩).2`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hTh j hj`. Rewrite using `[wJ_real D u τ j hj]`. Take `⟨h1, h2⟩` from `L.win_thick (j + 1) (by omega) (by omega) τ hTh`. Use `(sub_aux D.R j).1` as an intermediate fact.

Use `(sub_aux D.R j).2 hj` as an intermediate fact. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem wts_w {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hx : 4 ≤ L.sc.x) (hX : L.sc.x ≤ L.sc.X')
    (u : D.what₂.Word) (τ : D.what₂.Tau) :
    (∀ j, j + 1 < D.R.m → wJ D u τ j ≤ wJ D u τ (j + 1)) ∧
    (¬ IsThick D τ → ∀ j < D.R.m, (wJ D u τ j : ℝ) ≤ 2 * L.sc.b') ∧
    (IsThick D τ → ∀ j < D.R.m, L.sc.b - D.R.N D.R.m ≤ (wJ D u τ j : ℝ) ∧ (wJ D u τ j : ℝ) ≤ L.sc.b + L.etaSz + 1) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := base_sizes P
  obtain ⟨r1, r2, r3⟩ := base_sizes2 P hX
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left s7.le (by norm_num) hx
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    rw [wJ_eq D u τ j (by omega), wJ_eq D u τ (j + 1) hj]
    have g1 := (D.hc τ).gap_be ⟨j + 1, hj⟩
    have g2 := (D.hc τ).gap_eb ⟨j, by omega⟩ hj
    push_cast
    simp only at g2
    nlinarith
  · intro hTh j hj
    rw [wJ_real D u τ j hj]
    have := (sub_aux D.R j).1
    by_cases hT : IsTop D τ
    · obtain ⟨t, ht⟩ := top_is_tau_one_place D τ hT
      have h1 := (L.win_top (j + 1) (by omega) (by omega) τ t ht).2
      have := bT_le_five_quarters_alt P t
      linarith
    · have h1 := (L.win_thin (j + 1) (by omega) (by omega) τ ⟨(D.eTau τ).2, hT, hTh⟩).2
      linarith
  · intro hTh j hj
    rw [wJ_real D u τ j hj]
    obtain ⟨h1, h2⟩ := L.win_thick (j + 1) (by omega) (by omega) τ hTh
    have := (sub_aux D.R j).1
    have := (sub_aux D.R j).2 hj
    constructor <;> linarith

/- English proof (translation)
Take `⟨r1, r2, r3⟩` from `base_sizes2 P hX`. Establish `hm` using `D.R.two_le_m`. Establish `hk` using `five_le_k D.R`. Establish `key : ((-lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) ≤ ((wJ D u τ 0 : ℚ) : ℝ)`. Rewrite using `[wJ_real D u τ 0 (by omega)]`.

Establish `hs` using `(sub_aux D.R 0).2 (by omega)`. Move the coercions through the operations in `at hs ⊢`. Distinguish the cases in `hT : IsTop D τ`. Take `⟨t, ht⟩` from `top_is_tau_one_place D τ hT`. Rewrite using `[(lam_top L u τ t ht).2]`.

Establish `h1` using `(L.win_top 1 (le_refl _) (by omega) τ t ht).1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0` using `(lam_off P u τ hT (D.R.k - 1) (by omega)).1`. Take `⟨lo, l1, l2⟩` from `weights_in_short_window P hX τ`. Establish `h1` using `(l2 1 (le_refl _) (by omega)).1`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `key` after adjusting the coercions.
-/
theorem wts_first {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hX : L.sc.x ≤ L.sc.X')
    (u : D.what₂.Word) (τ : D.what₂.Tau) : - lamCol D u τ (D.R.k - 1) ≤ wJ D u τ 0 := by
  obtain ⟨r1, r2, r3⟩ := base_sizes2 P hX
  have hm := D.R.two_le_m
  have hk := five_le_k D.R
  have key : ((-lamCol D u τ (D.R.k - 1) : ℚ) : ℝ) ≤ ((wJ D u τ 0 : ℚ) : ℝ) := by
    rw [wJ_real D u τ 0 (by omega)]
    have hs := (sub_aux D.R 0).2 (by omega)
    push_cast at hs ⊢
    by_cases hT : IsTop D τ
    · obtain ⟨t, ht⟩ := top_is_tau_one_place D τ hT
      rw [(lam_top L u τ t ht).2]
      have h1 := (L.win_top 1 (le_refl _) (by omega) τ t ht).1
      linarith
    · have h0 := (lam_off P u τ hT (D.R.k - 1) (by omega)).1
      obtain ⟨lo, l1, l2⟩ := weights_in_short_window P hX τ
      have h1 := (l2 1 (le_refl _) (by omega)).1
      linarith
  exact_mod_cast key

/- English proof (translation)
Establish `hm` using `D.R.two_le_m`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm`. Establish `ht0 : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Establish `hm1c : ((D.R.m - 1 : ℕ) : ℝ) = (D.R.m : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]; norm_num`.

Establish `hmm : D.R.m - 1 + 1 = D.R.m` using `by omega`. Use `push_cast`. Rewrite using `[wJ_real D u τ 0 (by omega), wJ_real D u τ (D.R.m - 1) (by omega), hm1c, hmm]`. Take `⟨lo, l1, l2⟩` from `weights_in_short_window P hX τ`. Establish `h1` using `(l2 1 (le_refl _) (by omega)).1`.

Establish `h2` using `(l2 D.R.m (by omega) (le_refl _)).2`. Establish `hprod : 1 ≤ ((D.R.m : ℝ) - 1) * ((D.R.t : ℝ) + 1)` using `by nlinarith`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem wts_last {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hX : L.sc.x ≤ L.sc.X')
    (u : D.what₂.Word) (τ : D.what₂.Tau) : ((wJ D u τ (D.R.m - 1) - wJ D u τ 0 : ℚ) : ℝ) ≤ L.etaSz := by
  have hm := D.R.two_le_m
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hm1c : ((D.R.m - 1 : ℕ) : ℝ) = (D.R.m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hmm : D.R.m - 1 + 1 = D.R.m := by omega
  push_cast
  rw [wJ_real D u τ 0 (by omega), wJ_real D u τ (D.R.m - 1) (by omega), hm1c, hmm]
  obtain ⟨lo, l1, l2⟩ := weights_in_short_window P hX τ
  have h1 := (l2 1 (le_refl _) (by omega)).1
  have h2 := (l2 D.R.m (by omega) (le_refl _)).2
  have hprod : 1 ≤ ((D.R.m : ℝ) - 1) * ((D.R.t : ℝ) + 1) := by nlinarith
  push_cast
  nlinarith

/- English proof (translation)
Introduce `τ`. Take `⟨a1, a2⟩` from `wts_lam P Cn hCn u τ`. Take `⟨b1, b2, b3⟩` from `wts_w P hx hX u τ`. Conclude with `⟨fun i hi => lamCol_int D u τ i hi, a1, a2, b1, b2, b3, wts_first P hX u τ, wts_last P hX u τ⟩`.
-/
theorem wts_of_params {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (Cn : ℝ) (hCn : 3 ≤ Cn)
    (hx : 4 ≤ L.sc.x) (hX : L.sc.x ≤ L.sc.X') (u : D.what₂.Word) :
    Wts D u Cn L.sc.x L.sc.b L.sc.b' L.Sc L.etaSz := by
  intro τ
  obtain ⟨a1, a2⟩ := wts_lam P Cn hCn u τ
  obtain ⟨b1, b2, b3⟩ := wts_w P hx hX u τ
  exact ⟨fun i hi => lamCol_int D u τ i hi, a1, a2, b1, b2, b3, wts_first P hX u τ, wts_last P hX u τ⟩

/- English proof (translation)
Establish `hm0 : 0 ≤ m` using `by linarith`. Establish `hl0 : 0 ≤ l` using `by linarith`. Establish `hN0 : 0 ≤ N` using `by linarith`. Establish `hcL0 : 0 ≤ cL` using `by linarith`. Establish `hCcm : Cc ≤ m` using `by linarith`.

Establish `hcLm : cL + Cc ≤ m` using `by linarith`. Establish `hml : 0 ≤ m * l` using `mul_nonneg hm0 hl0`. Establish `hmm : 0 ≤ m * m` using `mul_nonneg hm0 hm0`. Establish `hA1 : cL * l ≤ cL * m * l`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg hcL0 hl0) (sub_nonneg.mpr hm)]`.

Establish `hA2 : (cL + Cc) * (m * l) ≤ m * (m * l)` using `mul_le_mul_of_nonneg_right hcLm hml`. Establish `hA3 : m * m * l ≤ m * m * m` using `mul_le_mul_of_nonneg_left hlm hmm`. Establish `hA : cL * l + Cc * m * l ≤ m ^ 3` using `by nlinarith`. Establish `hm34 : m ^ 3 ≤ m ^ 4` using `by nlinarith [mul_nonneg (pow_nonneg hm0 3) (sub_nonneg.mpr hm)]`. Establish `hNm3 : N * m ^ 3 ≤ b'` using `by nlinarith [mul_le_mul_of_nonneg_left hm34 hN0]`.

Establish `hX : N * (cL * l + T) ≤ b'`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (show cL * l + T ≤ m ^ 3 by linarith) hN0]`. Establish `ga : N ^ 2 * (cL * l + T) ≤ N * b'`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hX hN0]`. Establish `hCml : 0 ≤ Cc * m * l` using `mul_nonneg (mul_nonneg hCc hm0) hl0`.

Establish `gb : N * (cL * l) + T ≤ b'`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hN) hCml, mul_le_mul_of_nonneg_left hA hN0]`. Establish `hB2 : Cc * m ≤ m * m` using `mul_le_mul_of_nonneg_right hCcm hm0`. Establish `hB : cL + Cc * m + 2 * Cn ≤ m ^ 2 * cL`. Use polynomial arithmetic with `[hB2, mul_nonneg hm0 (sub_nonneg.mpr hm), mul_nonneg (sub_nonneg.mpr hcL) hmm]`.

Establish `hY : cL * l + T + G ≤ m ^ 2 * (cL * l)`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hB hl0]`. Establish `hmN : 0 ≤ m ^ 2 * N ^ 2` using `by positivity`. Establish `hNcl : 0 ≤ N * (cL * l)` using `mul_nonneg hN0 (mul_nonneg hcL0 hl0)`. Establish `gc : m ^ 2 * N ^ 2 * (cL * l + T + G) ≤ N * b' * (cL * l)`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hY hmN, mul_le_mul_of_nonneg_right hb hNcl]`. Establish `gd : (1 + 2 * (2 * Cn + 4)) * m ^ 3 * N ≤ b'`. Use polynomial arithmetic with `[mul_nonneg (show (0 : ℝ) ≤ m - (1 + 2 * (2 * Cn + 4)) by linarith) (mul_nonneg (pow_nonneg hm0 3) hN0)]`. Conclude with `⟨ga, gb, gc, gd⟩`.
-/
theorem nums_alg (N m l b' cL Cc Cn T G : ℝ) (hN : 1 ≤ N) (hm : 1 ≤ m) (hl1 : 1 ≤ l) (hlm : l ≤ m)
    (hK : cL + Cc + 6 * Cn + 9 ≤ m) (hcL : 3 ≤ cL) (hCc : 0 ≤ Cc) (hCn : 1 ≤ Cn) (hT : T ≤ Cc * m * l)
    (hG : G ≤ 2 * Cn * l) (hb : N * m ^ 4 ≤ b') :
    N ^ 2 * (cL * l + T) ≤ N * b' ∧ N * (cL * l) + T ≤ b' ∧
    m ^ 2 * N ^ 2 * (cL * l + T + G) ≤ N * b' * (cL * l) ∧ (1 + 2 * (2 * Cn + 4)) * m ^ 3 * N ≤ b' := by
  have hm0 : 0 ≤ m := by linarith
  have hl0 : 0 ≤ l := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hcL0 : 0 ≤ cL := by linarith
  have hCcm : Cc ≤ m := by linarith
  have hcLm : cL + Cc ≤ m := by linarith
  have hml : 0 ≤ m * l := mul_nonneg hm0 hl0
  have hmm : 0 ≤ m * m := mul_nonneg hm0 hm0
  have hA1 : cL * l ≤ cL * m * l := by
    nlinarith [mul_nonneg (mul_nonneg hcL0 hl0) (sub_nonneg.mpr hm)]
  have hA2 : (cL + Cc) * (m * l) ≤ m * (m * l) := mul_le_mul_of_nonneg_right hcLm hml
  have hA3 : m * m * l ≤ m * m * m := mul_le_mul_of_nonneg_left hlm hmm
  have hA : cL * l + Cc * m * l ≤ m ^ 3 := by nlinarith
  have hm34 : m ^ 3 ≤ m ^ 4 := by nlinarith [mul_nonneg (pow_nonneg hm0 3) (sub_nonneg.mpr hm)]
  have hNm3 : N * m ^ 3 ≤ b' := by nlinarith [mul_le_mul_of_nonneg_left hm34 hN0]
  have hX : N * (cL * l + T) ≤ b' := by
    nlinarith [mul_le_mul_of_nonneg_left (show cL * l + T ≤ m ^ 3 by linarith) hN0]
  have ga : N ^ 2 * (cL * l + T) ≤ N * b' := by
    nlinarith [mul_le_mul_of_nonneg_left hX hN0]
  have hCml : 0 ≤ Cc * m * l := mul_nonneg (mul_nonneg hCc hm0) hl0
  have gb : N * (cL * l) + T ≤ b' := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) hCml, mul_le_mul_of_nonneg_left hA hN0]
  have hB2 : Cc * m ≤ m * m := mul_le_mul_of_nonneg_right hCcm hm0
  have hB : cL + Cc * m + 2 * Cn ≤ m ^ 2 * cL := by
    nlinarith [hB2, mul_nonneg hm0 (sub_nonneg.mpr hm), mul_nonneg (sub_nonneg.mpr hcL) hmm]
  have hY : cL * l + T + G ≤ m ^ 2 * (cL * l) := by
    nlinarith [mul_le_mul_of_nonneg_left hB hl0]
  have hmN : 0 ≤ m ^ 2 * N ^ 2 := by positivity
  have hNcl : 0 ≤ N * (cL * l) := mul_nonneg hN0 (mul_nonneg hcL0 hl0)
  have gc : m ^ 2 * N ^ 2 * (cL * l + T + G) ≤ N * b' * (cL * l) := by
    nlinarith [mul_le_mul_of_nonneg_left hY hmN, mul_le_mul_of_nonneg_right hb hNcl]
  have gd : (1 + 2 * (2 * Cn + 4)) * m ^ 3 * N ≤ b' := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ m - (1 + 2 * (2 * Cn + 4)) by linarith)
      (mul_nonneg (pow_nonneg hm0 3) hN0)]
  exact ⟨ga, gb, gc, gd⟩

/- English proof (translation)
Use `le_trans ?_ (factRd R H).1` and prove the remaining obligations. Establish `hd : 7 ≤ H.d` using `by have := H.hyp.2.2.2.1; omega`. Establish `hd' : (7 : ℝ) ≤ H.d` using `by exact_mod_cast hd`. Establish `h1 : (2 : ℝ) ≤ Real.sqrt (H.d : ℝ)`. Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((R.e : ℝ) + 1 - (2 : ℝ) ^ (-(R.e : ℝ)))`. Apply `Real.one_le_rpow (by norm_num)` to reduce the goal to its premises. Establish `: (2 : ℝ) ^ (-(R.e : ℝ)) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)`. Establish `: (0 : ℝ) ≤ R.e` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_le_rdE {R : Ranks} (H : Host R) : 2 ≤ H.rdE := by
  refine le_trans ?_ (factRd R H).1
  have hd : 7 ≤ H.d := by have := H.hyp.2.2.2.1; omega
  have hd' : (7 : ℝ) ≤ H.d := by exact_mod_cast hd
  have h1 : (2 : ℝ) ≤ Real.sqrt (H.d : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((R.e : ℝ) + 1 - (2 : ℝ) ^ (-(R.e : ℝ))) := by
    apply Real.one_le_rpow (by norm_num)
    have : (2 : ℝ) ^ (-(R.e : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
    have : (0 : ℝ) ≤ R.e := Nat.cast_nonneg _
    linarith
  nlinarith

/- English proof (translation)
Take `⟨Y, h1, -, h3, h4⟩` from `P.g_Y`. Establish `hl1 : 1 ≤ L.sc.L` using `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`. Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast five_le_k D.R`. Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hY : 0 < Y` using `lt_of_lt_of_le (by positivity) h1`.

Establish `hg : 0 < (D.host.g i : ℝ)` using `lt_of_lt_of_le hY (h4 i).1`. Use `⟨hg, ?_⟩` and prove the remaining obligations. Establish `h5 : Real.log (D.host.g i : ℝ) ≤ Real.log (2 * Y)` using `Real.log_le_log hg (h4 i).2`. Rewrite `h5` using `[Real.log_mul (by norm_num) hY.ne']`. Establish `h6 : Real.log 2 ≤ 1`.

Use `Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_g_le {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (i : Fin 2) :
    0 < (D.host.g i : ℝ) ∧ Real.log (D.host.g i : ℝ) ≤ (P.CYL + 1) * L.sc.L := by
  obtain ⟨Y, h1, -, h3, h4⟩ := P.g_Y
  have hl1 : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast five_le_k D.R
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) h1
  have hg : 0 < (D.host.g i : ℝ) := lt_of_lt_of_le hY (h4 i).1
  refine ⟨hg, ?_⟩
  have h5 : Real.log (D.host.g i : ℝ) ≤ Real.log (2 * Y) := Real.log_le_log hg (h4 i).2
  rw [Real.log_mul (by norm_num) hY.ne'] at h5
  have h6 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  nlinarith

/- English proof (translation)
Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hx0 : 0 < L.sc.x` using `by linarith [L.sc.one_lt_alt]`. Establish `hv0 : 0 < D.host.v`. Unfold `Host.v`. Use `two_le_rdE D.host` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Real.log_mul (by positivity) hv0.ne', Real.log_mul hx0.ne' hb0.ne']`. Establish `hlb : Real.log L.sc.b = L.sc.L` using `Real.log_exp _`. Establish `hq0 : 0 < (D.host.q : ℝ)` using `by exact_mod_cast D.host.hyp.1.pos`. Establish `hd0 : 0 < (D.host.d : ℝ)` using `by exact_mod_cast D.host.hyp.2.1.pos`.

Establish `hn0 : 0 < (D.R.n : ℝ)`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions. Establish `hv : D.host.v ≤ (D.R.n : ℝ) ^ 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d)`. Unfold `Host.v`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs0 : 0 < Real.sqrt ((D.host.q : ℝ) * D.host.d)` using `Real.sqrt_pos.mpr (by positivity)`. Establish `hlv` using `Real.log_le_log hv0 hv`. Rewrite `hlv` using `[Real.log_mul (pow_pos hn0 2).ne' hs0.ne', Real.log_pow, Real.log_sqrt (by positivity), Real.log_mul hq0.ne' hd0.ne']`. Rewrite using `[hlb]`.

Move the coercions through the operations in `at hlv`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_xbv_le {D : D7} (L : SizeData₂ D)
    (hlx : 7 * Real.log L.sc.x ≤ L.sc.L)
    (hln : Real.log D.R.n ≤ 3 * Real.log L.sc.x)
    (hq : Real.log D.host.q ≤ L.sc.L) (hd : Real.log D.host.d ≤ L.sc.L)
    (hrd : D.host.rdE ≤ 2 * (D.R.n : ℝ) ^ 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d)) :
    Real.log (L.sc.x * L.sc.b * D.host.v) ≤ 3 * L.sc.L := by
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hv0 : 0 < D.host.v := by
    unfold Host.v
    have := two_le_rdE D.host
    linarith
  rw [Real.log_mul (by positivity) hv0.ne', Real.log_mul hx0.ne' hb0.ne']
  have hlb : Real.log L.sc.b = L.sc.L := Real.log_exp _
  have hq0 : 0 < (D.host.q : ℝ) := by exact_mod_cast D.host.hyp.1.pos
  have hd0 : 0 < (D.host.d : ℝ) := by exact_mod_cast D.host.hyp.2.1.pos
  have hn0 : 0 < (D.R.n : ℝ) := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hv : D.host.v ≤ (D.R.n : ℝ) ^ 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    unfold Host.v
    linarith
  have hs0 : 0 < Real.sqrt ((D.host.q : ℝ) * D.host.d) := Real.sqrt_pos.mpr (by positivity)
  have hlv := Real.log_le_log hv0 hv
  rw [Real.log_mul (pow_pos hn0 2).ne' hs0.ne', Real.log_pow, Real.log_sqrt (by positivity),
    Real.log_mul hq0.ne' hd0.ne'] at hlv
  rw [hlb]
  push_cast at hlv
  linarith

/- English proof (translation)
Take `⟨s1, s2, s3, s4, s5, s6, s7⟩` from `base_sizes P`. Establish `hx` using `L.sc.one_lt_alt`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`. Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast five_le_k D.R`. Establish `hN1 : (1 : ℝ) ≤ D.R.N D.R.m`.

Establish `: 1 ≤ D.R.N D.R.m` using `by unfold Ranks.N; have := five_le_k D.R; omega`. Conclude with `this` after adjusting the coercions. Prove the components needed by the constructor for the conclusion. Rewrite using `[L.Sc_eq]`. Establish `h1` using `P.Del_ge.2.2.2`.

Establish `h2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10` using `one_le_pow₀ (by linarith)`. Establish `h3 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10` using `by nlinarith`. Establish `h4 : (1 : ℝ) ≤ (D.s.Del : ℝ)` using `le_trans h3 h1`. Use the polynomial consequences of the given equalities and inequalities. Establish `: L.sc.b' / L.sc.x = D.R.n * L.sc.w'' D.R.n`.

Rewrite using `[s5]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Establish `hW0 : 0 ≤ L.sc.w'' D.R.n` using `by linarith`. Establish `: 3 * L.sc.w'' D.R.n ≤ D.R.n * L.sc.w'' D.R.n` using `mul_le_mul_of_nonneg_right hn3 hW0`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nums_small {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (hn3 : (3 : ℝ) ≤ D.R.n) :
    1 ≤ L.Sc ∧ L.Sc + L.etaSz + D.R.m * D.R.t ≤ L.sc.b' / L.sc.x := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := base_sizes P
  have hx := L.sc.one_lt_alt
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast five_le_k D.R
  have hN1 : (1 : ℝ) ≤ D.R.N D.R.m := by
    have : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := five_le_k D.R; omega
    exact_mod_cast this
  constructor
  · rw [L.Sc_eq]
    have h1 := P.Del_ge.2.2.2
    have h2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by linarith)
    have h3 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 := by nlinarith
    have h4 : (1 : ℝ) ≤ (D.s.Del : ℝ) := le_trans h3 h1
    nlinarith
  · have : L.sc.b' / L.sc.x = D.R.n * L.sc.w'' D.R.n := by
      rw [s5]
      field_simp
    rw [this]
    have hW0 : 0 ≤ L.sc.w'' D.R.n := by linarith
    have : 3 * L.sc.w'' D.R.n ≤ D.R.n * L.sc.w'' D.R.n := mul_le_mul_of_nonneg_right hn3 hW0
    linarith

/- English proof (translation)
Take `⟨s1, -, -, -, -, s6, s7⟩` from `base_sizes P`. Take `⟨-, r2, r3⟩` from `base_sizes2 P hX`. Take `⟨t1, t2⟩` from `nums_small P hn3`. Establish `hl1 : 1 ≤ L.sc.L` using `Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`.

Establish `hb0 : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hN1 : (1 : ℝ) ≤ D.R.N D.R.m`. Establish `: 1 ≤ D.R.N D.R.m` using `by unfold Ranks.N; have := five_le_k D.R; omega`. Conclude with `this` after adjusting the coercions. Establish `hv1 : 1 ≤ D.host.v`.

Unfold `Host.v`. Use `two_le_rdE D.host` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbx : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self s7.le (by linarith)`. Establish `hNm4 : (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 4 ≤ L.sc.b'`.

Establish `: (D.R.m : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 12` using `pow_le_pow_right₀ (by linarith) (by norm_num)`. Establish `: (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 4 ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 12` using `mul_le_mul_of_nonneg_left this (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨g0p, g0l⟩` from `log_g_le P 0`. Take `⟨g1p, g1l⟩` from `log_g_le P 1`.

Establish `hYl : (P.CYL + 1) * L.sc.L ≤ Cn * L.sc.L` using `mul_le_mul_of_nonneg_right hCnY (by linarith)`. Establish `h3l : 3 * L.sc.L ≤ cL * L.sc.L` using `mul_le_mul_of_nonneg_right hcL (by linarith)`. Establish `hCl : Cn * L.sc.L ≤ Cn * (cL * L.sc.L)` using `mul_le_mul_of_nonneg_left (by linarith) (by linarith)`. Establish `hCl1 : L.sc.L ≤ Cn * L.sc.L` using `le_mul_of_one_le_left (by linarith) hCn1`. Establish `hG : Real.log ((D.host.g 0 : ℝ) * D.host.g 1) ≤ 2 * Cn * L.sc.L`.

Rewrite using `[Real.log_mul g0p.ne' g1p.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨a1, a2, a3, a4⟩` from `nums_alg (D.R.N D.R.m) D.R.m L.sc.L L.sc.b' cL Cc Cn _ _ hN1 (by linarith) hl1 hmL hmK hcL hCc hCn1 hT hG hNm4`. Use `⟨hb0, le_trans (log_xbv_le L hlx hln hq hd hrd) h3l, ?_, by linarith, by linarith, ?_, t1, s6, t2, a1, a2, a3, ?_, by linarith, hv1, a4⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `: L.sc.L ≤ cL * L.sc.L` using `by linarith`. Use `gcongr`. Rewrite using `[mul_div_cancel_left₀ _ (by linarith : L.sc.x ≠ 0)]`. Conclude with `r3`. Rewrite using `[← L.logDerivative_at_one_eq]`.

Use `le_trans hdl ?_` and prove the remaining obligations. Establish `: L.sc.x ^ L.sc.eps = L.sc.L` using `rfl`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nums_of_params {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (Cn cL Cc : ℝ) (hcL : 3 ≤ cL) (hCc : 0 ≤ Cc)
    (hCn1 : 1 ≤ Cn) (hCnc : Cc ≤ Cn) (hCnY : P.CYL + 1 ≤ Cn)
    (hx : 4 ≤ L.sc.x) (hX : L.sc.x ≤ L.sc.X') (hlx : 7 * Real.log L.sc.x ≤ L.sc.L)
    (hn3 : (3 : ℝ) ≤ D.R.n) (hln : Real.log D.R.n ≤ 3 * Real.log L.sc.x)
    (hq : Real.log D.host.q ≤ L.sc.L) (hd : Real.log D.host.d ≤ L.sc.L)
    (hrd : D.host.rdE ≤ 2 * (D.R.n : ℝ) ^ 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d))
    (hdl : |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps)
    (hmL : L.sc.L ≤ D.R.m) (hmK : cL + Cc + 6 * Cn + 9 ≤ D.R.m)
    (u : D.what₂.Word) (hT : Real.log ((D.mem u).A.T : ℝ) ≤ Cc * D.R.m * L.sc.L) :
    Nums D (Tu D u) (D.host.g 0) (D.host.g 1) Cn L.sc.x L.sc.b (cL * L.sc.L) L.sc.b' L.Sc L.etaSz := by
  obtain ⟨s1, -, -, -, -, s6, s7⟩ := base_sizes P
  obtain ⟨-, r2, r3⟩ := base_sizes2 P hX
  obtain ⟨t1, t2⟩ := nums_small P hn3
  have hl1 : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hN1 : (1 : ℝ) ≤ D.R.N D.R.m := by
    have : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := five_le_k D.R; omega
    exact_mod_cast this
  have hv1 : 1 ≤ D.host.v := by
    unfold Host.v
    have := two_le_rdE D.host
    linarith
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self s7.le (by linarith)
  have hNm4 : (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 4 ≤ L.sc.b' := by
    have : (D.R.m : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 12 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have : (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 4 ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 12 :=
      mul_le_mul_of_nonneg_left this (by linarith)
    linarith
  obtain ⟨g0p, g0l⟩ := log_g_le P 0
  obtain ⟨g1p, g1l⟩ := log_g_le P 1
  have hYl : (P.CYL + 1) * L.sc.L ≤ Cn * L.sc.L := mul_le_mul_of_nonneg_right hCnY (by linarith)
  have h3l : 3 * L.sc.L ≤ cL * L.sc.L := mul_le_mul_of_nonneg_right hcL (by linarith)
  have hCl : Cn * L.sc.L ≤ Cn * (cL * L.sc.L) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hCl1 : L.sc.L ≤ Cn * L.sc.L := le_mul_of_one_le_left (by linarith) hCn1
  have hG : Real.log ((D.host.g 0 : ℝ) * D.host.g 1) ≤ 2 * Cn * L.sc.L := by
    rw [Real.log_mul g0p.ne' g1p.ne']
    linarith
  obtain ⟨a1, a2, a3, a4⟩ := nums_alg (D.R.N D.R.m) D.R.m L.sc.L L.sc.b' cL Cc Cn _ _ hN1 (by linarith) hl1 hmL hmK
    hcL hCc hCn1 hT hG hNm4
  refine ⟨hb0, le_trans (log_xbv_le L hlx hln hq hd hrd) h3l, ?_, by linarith, by linarith, ?_, t1, s6, t2, a1, a2, a3,
    ?_, by linarith, hv1, a4⟩
  · calc Real.log (Tu D u : ℝ) ≤ Cc * D.R.m * L.sc.L := hT
      _ ≤ Cn * D.R.m * (cL * L.sc.L) := by
        have : L.sc.L ≤ cL * L.sc.L := by linarith
        gcongr
  · rw [mul_div_cancel_left₀ _ (by linarith : L.sc.x ≠ 0)]
    exact r3
  · rw [← L.logDerivative_at_one_eq]
    refine le_trans hdl ?_
    have : L.sc.x ^ L.sc.eps = L.sc.L := rfl
    rw [this]
    linarith

/- English proof (translation)
Use `le_trans (factRd R H).2.1 ?_` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)` to reduce the goal to its premises. Establish `h1 : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2` using `by exact_mod_cast H.QS_le`. Establish `h2 : (0 : ℝ) ≤ (R.n : ℝ) ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rdE_le {R : Ranks} (H : Host R) : H.rdE ≤ 2 * (R.n : ℝ) ^ 2 * Real.sqrt ((H.q : ℝ) * H.d) := by
  refine le_trans (factRd R H).2.1 ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have h1 : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast H.QS_le
  have h2 : (0 : ℝ) ≤ (R.n : ℝ) ^ 2 := by positivity
  linarith

/- English proof (translation)
Establish `h1 : Filter.Tendsto (fun y : ℝ => y ^ ((K : ℝ) / e) * Real.exp (-1 * y)) Filter.atTop (nhds 0)` using `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ one_pos`. Establish `h2` using `h1.comp (tendsto_rpow_atTop he)`. Establish `h3` using `(h2.eventually (ge_mem_nhds one_pos)).and (Filter.eventually_ge_atTop (0 : ℝ))`. Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.1 h3`. Use `⟨x0, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨h5, h6⟩` from `hx0 x hx`. Express the relevant statement in the definitionally equal form `(x ^ e) ^ ((K : ℝ) / e) * Real.exp (-1 * x ^ e) ≤ 1 at h5`. Establish `hek : e * ((K : ℝ) / e) = K` using `by field_simp`. Establish `h7 : (x ^ e) ^ ((K : ℝ) / e) = x ^ K`. Rewrite using `[← Real.rpow_mul h6, hek, Real.rpow_natCast]`.

Rewrite `h5` using `[h7]`. Establish `h9 : Real.exp (-1 * x ^ e) * Real.exp (x ^ e) = 1`. Rewrite using `[← Real.exp_add]`. Simplify using the standard rewrite rules. Establish `h8` using `Real.exp_pos (x ^ e)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem pow_le_exp_rpow_for_large_x (K : ℕ) (e : ℝ) (he : 0 < e) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → x ^ K ≤ Real.exp (x ^ e) := by
  have h1 : Filter.Tendsto (fun y : ℝ => y ^ ((K : ℝ) / e) * Real.exp (-1 * y)) Filter.atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ one_pos
  have h2 := h1.comp (tendsto_rpow_atTop he)
  have h3 := (h2.eventually (ge_mem_nhds one_pos)).and (Filter.eventually_ge_atTop (0 : ℝ))
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 h3
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h5, h6⟩ := hx0 x hx
  change (x ^ e) ^ ((K : ℝ) / e) * Real.exp (-1 * x ^ e) ≤ 1 at h5
  have hek : e * ((K : ℝ) / e) = K := by field_simp
  have h7 : (x ^ e) ^ ((K : ℝ) / e) = x ^ K := by
    rw [← Real.rpow_mul h6, hek, Real.rpow_natCast]
  rw [h7] at h5
  have h9 : Real.exp (-1 * x ^ e) * Real.exp (x ^ e) = 1 := by
    rw [← Real.exp_add]
    simp
  have h8 := Real.exp_pos (x ^ e)
  calc x ^ K = x ^ K * Real.exp (-1 * x ^ e) * Real.exp (x ^ e) := by rw [mul_assoc, h9, mul_one]
    _ ≤ 1 * Real.exp (x ^ e) := by gcongr
    _ = Real.exp (x ^ e) := one_mul _

/- English proof (translation)
Conclude with `Filter.eventually_atTop.1 ((tendsto_rpow_atTop hθ).eventually_ge_atTop C)`.
-/
theorem le_rpow_for_large_x (θ : ℝ) (hθ : 0 < θ) (C : ℝ) : ∃ x0 : ℝ, ∀ x, x0 ≤ x → C ≤ x ^ θ := by
  exact Filter.eventually_atTop.1 ((tendsto_rpow_atTop hθ).eventually_ge_atTop C)

/- English proof (translation)
Establish `hx1 : 1 < s.x` using `s.one_lt_alt`. Establish `hx0 : 0 < s.x` using `by linarith`. Establish `hlog : 0 < Real.log s.x` using `Real.log_pos hx1`. Establish `h14 : 14 * Real.log s.x ≤ s.x ^ (s.eps / 3)`. Use `Real.log_le_log (pow_pos hx0 14) h` as an intermediate fact.

Rewrite `this` using `[Real.log_pow, Scale.X', Real.log_exp]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : s.x ^ (s.eps / 3) ≤ s.x ^ s.eps` using `Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [s.eps_pos])`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[Scale.X']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Scale.L]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem index_scalar_multiple_eq (s : Scale) (h : s.x ^ 14 ≤ s.X') : s.x ≤ s.X' ∧ 4 * Real.log s.x ≤ s.L := by
  have hx1 : 1 < s.x := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hlog : 0 < Real.log s.x := Real.log_pos hx1
  have h14 : 14 * Real.log s.x ≤ s.x ^ (s.eps / 3) := by
    have := Real.log_le_log (pow_pos hx0 14) h
    rw [Real.log_pow, Scale.X', Real.log_exp] at this
    push_cast at this
    linarith
  have hle : s.x ^ (s.eps / 3) ≤ s.x ^ s.eps :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [s.eps_pos])
  constructor
  · rw [Scale.X']
    calc s.x = Real.exp (Real.log s.x) := (Real.exp_log hx0).symm
      _ ≤ Real.exp (s.x ^ (s.eps / 3)) := Real.exp_le_exp.mpr (by linarith)
  · rw [Scale.L]
    linarith

/- English proof (translation)
Establish `hx1 : 1 < s.x` using `s.one_lt_alt`. Establish `hx0 : 0 < s.x` using `by linarith`. Establish `hlog : 0 < Real.log s.x` using `Real.log_pos hx1`. Establish `h14 : 14 * Real.log s.x ≤ s.x ^ (s.eps / 3)`. Use `Real.log_le_log (pow_pos hx0 14) h` as an intermediate fact.

Rewrite `this` using `[Real.log_pow, Scale.X', Real.log_exp]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : s.x ^ (s.eps / 3) ≤ s.x ^ s.eps` using `Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [s.eps_pos])`. Rewrite using `[Scale.L]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem seven_log_le_L_of_power_bound (s : Scale) (h : s.x ^ 14 ≤ s.X') : 7 * Real.log s.x ≤ s.L := by
  have hx1 : 1 < s.x := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hlog : 0 < Real.log s.x := Real.log_pos hx1
  have h14 : 14 * Real.log s.x ≤ s.x ^ (s.eps / 3) := by
    have := Real.log_le_log (pow_pos hx0 14) h
    rw [Real.log_pow, Scale.X', Real.log_exp] at this
    push_cast at this
    linarith
  have hle : s.x ^ (s.eps / 3) ≤ s.x ^ s.eps :=
    Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [s.eps_pos])
  rw [Scale.L]
  linarith

/- English proof (translation)
Establish `he0` using `L.sc.eps_pos`. Establish `he1` using `L.sc.eps_lt`. Establish `hx1 : 1 ≤ L.sc.x` using `by linarith`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Take `⟨hn1, hn2⟩` from `S.1`.

Establish `hm` using `S.2.1.1`. Establish `hQD` using `S.2.2.2.2.2.2.1`. Establish `hq` using `hQD.2.2.1`. Establish `hd` using `hQD.2.2.2.2.1`. Unfold `szTh at *`.

Establish `hn0 : 0 < (D.R.n : ℝ)`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `le_trans ?_ hm` and prove the remaining obligations.

Unfold `Scale.delta1`. Establish `h1 : L.sc.x * L.sc.x ^ (-(L.sc.eps / 8)) = L.sc.x ^ (1 + -(L.sc.eps / 8))`. Rewrite using `[Real.rpow_add hx0, Real.rpow_one]`. Rewrite using `[h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]`. Apply `Real.rpow_le_rpow_of_exponent_le hx1` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion. Unfold `Scale.L`. Apply `Real.rpow_le_rpow_of_exponent_le hx1` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_trans ?_ hn1` and prove the remaining obligations.

Establish `h1 : L.sc.x ^ (2 : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps - L.sc.eps / 100)`. Apply `Real.rpow_le_rpow_of_exponent_le hx1` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use `le_trans ?_ h1` and prove the remaining obligations. Rewrite using `[Real.rpow_two]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h1` using `Real.log_le_log hn0 hn2`. Rewrite `h1` using `[Real.log_rpow hx0]`. Establish `h2` using `Real.log_nonneg hx1`. Establish `h3 : (2 + 8 * L.sc.eps + L.sc.eps / 100) * Real.log L.sc.x ≤ 3 * Real.log L.sc.x` using `mul_le_mul_of_nonneg_right (by linarith) h2`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `le_trans hq ?_` and prove the remaining obligations. Unfold `Scale.L`. Apply `Real.rpow_le_rpow_of_exponent_le hx1` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Use `le_trans hd ?_` and prove the remaining obligations. Unfold `Scale.L`. Apply `Real.rpow_le_rpow_of_exponent_le hx1` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem size_bounds_of_scale {D : D7} (L : SizeData₂ D) (S : SizesAt L) (hx : 4 ≤ L.sc.x) :
    L.sc.x ^ ((2 : ℝ) / 5) ≤ D.R.m ∧ L.sc.L ≤ L.sc.x ^ ((2 : ℝ) / 5) ∧ (3 : ℝ) ≤ D.R.n ∧
    Real.log D.R.n ≤ 3 * Real.log L.sc.x ∧ Real.log D.host.q ≤ L.sc.L ∧ Real.log D.host.d ≤ L.sc.L := by
  have he0 := L.sc.eps_pos
  have he1 := L.sc.eps_lt
  have hx1 : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  obtain ⟨hn1, hn2⟩ := S.1
  have hm := S.2.1.1
  have hQD := S.2.2.2.2.2.2.1
  have hq := hQD.2.2.1
  have hd := hQD.2.2.2.2.1
  unfold szTh at *
  have hn0 : 0 < (D.R.n : ℝ) := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ hm
    unfold Scale.delta1
    have h1 : L.sc.x * L.sc.x ^ (-(L.sc.eps / 8)) = L.sc.x ^ (1 + -(L.sc.eps / 8)) := by
      rw [Real.rpow_add hx0, Real.rpow_one]
    rw [h1, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    linarith
  · unfold Scale.L
    apply Real.rpow_le_rpow_of_exponent_le hx1
    linarith
  · refine le_trans ?_ hn1
    have h1 : L.sc.x ^ (2 : ℝ) ≤ L.sc.x ^ (2 + 8 * L.sc.eps - L.sc.eps / 100) := by
      apply Real.rpow_le_rpow_of_exponent_le hx1
      linarith
    refine le_trans ?_ h1
    rw [Real.rpow_two]
    nlinarith
  · have h1 := Real.log_le_log hn0 hn2
    rw [Real.log_rpow hx0] at h1
    have h2 := Real.log_nonneg hx1
    have h3 : (2 + 8 * L.sc.eps + L.sc.eps / 100) * Real.log L.sc.x ≤ 3 * Real.log L.sc.x :=
      mul_le_mul_of_nonneg_right (by linarith) h2
    linarith
  · refine le_trans hq ?_
    unfold Scale.L
    apply Real.rpow_le_rpow_of_exponent_le hx1
    linarith
  · refine le_trans hd ?_
    unfold Scale.L
    apply Real.rpow_le_rpow_of_exponent_le hx1
    linarith

/- English proof (translation)
Use `congrArg (fun l => l.getD 19 0) (Fm.params_K x hx i)` as an intermediate fact. Simplify `this` using `[parConsts]`.
-/
theorem cyl_eq {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    (Fm.params x hx i).CYL = Fm.PK.getD 19 0 := by
  have := congrArg (fun l => l.getD 19 0) (Fm.params_K x hx i)
  simpa [parConsts] using this

/- English proof (translation)
Establish `heps : 0 < eps`. Take `⟨i0⟩` from `Fm.Ix_zero`. Use `(Fm.L 0 i0).sc.eps_pos` as an intermediate fact. Rewrite `this` using `[Fm.L_eps]`. Then use the resulting hypothesis. Take `⟨Cc, xT, hT⟩` from `hT`.

Take `⟨xD, hDl⟩` from `hDl`. Take `⟨xA, hA⟩` from `pow_le_exp_rpow_for_large_x 14 (eps / 3) (by positivity)`. Use `⟨max (max 3 (max Cc 0)) (Fm.PK.getD 19 0 + 1), fun Cn hCn cL hcL => ?_⟩` and prove the remaining obligations. Establish `hCn3 : 3 ≤ Cn` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCn`. Establish `hCnc : max Cc 0 ≤ Cn` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCn`.

Establish `hCnY : Fm.PK.getD 19 0 + 1 ≤ Cn` using `le_trans (le_max_right _ _) hCn`. Take `⟨xK, hK⟩` from `le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) (cL + max Cc 0 + 6 * Cn + 9)`. Use `⟨max (max xT xD) (max (max xA xK) (max 4 (Fm.x1 + 1))), fun x hx i => ?_⟩` and prove the remaining obligations. Establish `hxT : xT ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hxD : xD ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`.

Establish `hxA : xA ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx`. Establish `hxK : xK ≤ x` using `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx`. Establish `hx4 : 4 ≤ x` using `le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx`. Establish `hx1 : Fm.x1 < x`. Use `le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsx : (Fm.L x i).sc.x = x` using `Fm.L_x x i hx1`. Establish `hse : (Fm.L x i).sc.eps = eps` using `Fm.L_eps x i`. Establish `hX : (Fm.L x i).sc.x ^ 14 ≤ (Fm.L x i).sc.X'`. Unfold `Scale.X'`.

Rewrite using `[hsx, hse]`. Conclude with `hA x hxA`. Establish `hx4' : 4 ≤ (Fm.L x i).sc.x` using `by rw [hsx]; exact hx4`. Take `⟨c1, -⟩` from `index_scalar_multiple_eq _ hX`. Establish `c2` using `seven_log_le_L_of_power_bound _ hX`.

Take `⟨z1, z2, z3, z4, z5, z6⟩` from `size_bounds_of_scale (Fm.L x i) (Fm.sizes x hx1 i) hx4'`. Establish `hKm : cL + max Cc 0 + 6 * Cn + 9 ≤ ((Fm.D x i).R.m : ℝ)`. Use `le_trans ?_ z1` and prove the remaining obligations. Rewrite using `[hsx]`. Conclude with `hK x hxK`.

Use `⟨fun u => ?_, fun u => wts_of_params (Fm.params x hx1 i) Cn hCn3 hx4' c1 u⟩` and prove the remaining obligations. Use `nums_of_params (Fm.params x hx1 i) Cn cL (max Cc 0) hcL (le_max_right _ _) (by linarith) hCnc (by rw [cyl_eq]; exact hCnY) hx4' c1 c2 z3 z4 z5 z6 (rdE_le _) (hDl x hxD i) (le_trans z2 z1) hKm u ?_` and prove the remaining obligations. Use `le_trans (hT x hxT i u) ?_` and prove the remaining obligations. Establish `hL0 : 0 ≤ (Fm.L x i).sc.L` using `Real.rpow_nonneg (le_trans zero_le_one (Fm.L x i).sc.one_lt_alt.le) _`. Establish `hm0 : 0 ≤ ((Fm.D x i).R.m : ℝ)` using `Nat.cast_nonneg _`.

Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hm0) hL0`.
-/
theorem nums_wts_of_fam {eps : ℝ} (Fm : FamP eps)
    (hT : ∃ Cc x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
      Real.log (((Fm.D x i).mem u).A.T : ℝ) ≤ Cc * (Fm.D x i).R.m * (Fm.L x i).sc.L)
    (hDl : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) :
    ∃ Cn₀ : ℝ, ∀ Cn ≥ Cn₀, ∀ cL ≥ (3 : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∀ u, Nums (Fm.D x i) (Tu (Fm.D x i) u) ((Fm.D x i).host.g 0) ((Fm.D x i).host.g 1) Cn (Fm.L x i).sc.x
        (Fm.L x i).sc.b (cL * (Fm.L x i).sc.L) (Fm.L x i).sc.b' (Fm.L x i).Sc (Fm.L x i).etaSz) ∧
      (∀ u, Wts (Fm.D x i) u Cn (Fm.L x i).sc.x (Fm.L x i).sc.b (Fm.L x i).sc.b' (Fm.L x i).Sc (Fm.L x i).etaSz) := by
  have heps : 0 < eps := by
    obtain ⟨i0⟩ := Fm.Ix_zero
    have := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at this
  obtain ⟨Cc, xT, hT⟩ := hT
  obtain ⟨xD, hDl⟩ := hDl
  obtain ⟨xA, hA⟩ := pow_le_exp_rpow_for_large_x 14 (eps / 3) (by positivity)
  refine ⟨max (max 3 (max Cc 0)) (Fm.PK.getD 19 0 + 1), fun Cn hCn cL hcL => ?_⟩
  have hCn3 : 3 ≤ Cn := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hCn
  have hCnc : max Cc 0 ≤ Cn := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hCn
  have hCnY : Fm.PK.getD 19 0 + 1 ≤ Cn := le_trans (le_max_right _ _) hCn
  obtain ⟨xK, hK⟩ := le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) (cL + max Cc 0 + 6 * Cn + 9)
  refine ⟨max (max xT xD) (max (max xA xK) (max 4 (Fm.x1 + 1))), fun x hx i => ?_⟩
  have hxT : xT ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxD : xD ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxA : xA ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hxK : xK ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hx4 : 4 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
    linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hX : (Fm.L x i).sc.x ^ 14 ≤ (Fm.L x i).sc.X' := by
    unfold Scale.X'
    rw [hsx, hse]
    exact hA x hxA
  have hx4' : 4 ≤ (Fm.L x i).sc.x := by rw [hsx]; exact hx4
  obtain ⟨c1, -⟩ := index_scalar_multiple_eq _ hX
  have c2 := seven_log_le_L_of_power_bound _ hX
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := size_bounds_of_scale (Fm.L x i) (Fm.sizes x hx1 i) hx4'
  have hKm : cL + max Cc 0 + 6 * Cn + 9 ≤ ((Fm.D x i).R.m : ℝ) := by
    refine le_trans ?_ z1
    rw [hsx]
    exact hK x hxK
  refine ⟨fun u => ?_, fun u => wts_of_params (Fm.params x hx1 i) Cn hCn3 hx4' c1 u⟩
  refine nums_of_params (Fm.params x hx1 i) Cn cL (max Cc 0) hcL (le_max_right _ _) (by linarith) hCnc
    (by rw [cyl_eq]; exact hCnY) hx4' c1 c2 z3 z4 z5 z6 (rdE_le _) (hDl x hxD i) (le_trans z2 z1) hKm u ?_
  refine le_trans (hT x hxT i u) ?_
  have hL0 : 0 ≤ (Fm.L x i).sc.L := Real.rpow_nonneg (le_trans zero_le_one (Fm.L x i).sc.one_lt_alt.le) _
  have hm0 : 0 ≤ ((Fm.D x i).R.m : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hm0) hL0

/- English proof (translation)
Take `⟨x0, h⟩` from `hT`. Conclude with `nums_wts_of_fam Fm ⟨Fm.CTu, x0, fun x hx i u => (h x hx i).2 u⟩ hDl`.
-/
theorem nums_wts_of_tuSize {eps : ℝ} (Fm : FamP eps) (hT : TuSize Fm)
    (hDl : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, |(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) :
    ∃ Cn₀ : ℝ, ∀ Cn ≥ Cn₀, ∀ cL ≥ (3 : ℝ), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∀ u, Nums (Fm.D x i) (Tu (Fm.D x i) u) ((Fm.D x i).host.g 0) ((Fm.D x i).host.g 1) Cn (Fm.L x i).sc.x
        (Fm.L x i).sc.b (cL * (Fm.L x i).sc.L) (Fm.L x i).sc.b' (Fm.L x i).Sc (Fm.L x i).etaSz) ∧
      (∀ u, Wts (Fm.D x i) u Cn (Fm.L x i).sc.x (Fm.L x i).sc.b (Fm.L x i).sc.b' (Fm.L x i).Sc (Fm.L x i).etaSz) := by
  obtain ⟨x0, h⟩ := hT
  exact nums_wts_of_fam Fm ⟨Fm.CTu, x0, fun x hx i u => (h x hx i).2 u⟩ hDl

end Formalism.MainNotions.flipTwoThree

end
