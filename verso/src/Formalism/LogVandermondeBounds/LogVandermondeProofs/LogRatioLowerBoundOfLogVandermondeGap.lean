import Formalism.LogVandermondeBounds.VandPlace

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

/- English proof (translation)
Establish `h` using `(hasSum_nat_add_iff' 1).mpr hasSum_zeta_two`. Simplify using `using h`.
-/
lemma hasSum_inv_succ_sq : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

/- English proof (translation)
Establish `hle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ^ M ≤ 1 / ((n : ℝ) + 1) ^ 2`. Introduce `n`. Establish `h1 : (1 : ℝ) ≤ (n : ℝ) + 1` using `by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]`. Apply `one_div_le_one_div_of_le (by positivity)` to reduce the goal to its premises. Conclude with `pow_le_pow_right₀ h1 hM`.

Establish `hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) ^ M` using `fun n => by positivity`. Establish `hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ M)` using `Summable.of_nonneg_of_le hnn hle hasSum_inv_succ_sq.summable`. Use `⟨tsum_nonneg hnn, ?_⟩` and prove the remaining obligations. Establish `h3 : zetaR M ≤ Real.pi ^ 2 / 6` using `hasSum_le hle hs.hasSum hasSum_inv_succ_sq`. Establish `hp` using `Real.pi_lt_d2`.

Establish `hp0` using `Real.pi_pos`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma zetaR_nonneg_le_two (M : ℕ) (hM : 2 ≤ M) : 0 ≤ zetaR M ∧ zetaR M ≤ 2 := by
  have hle : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ^ M ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ h1 hM
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) ^ M := fun n => by positivity
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ M) :=
    Summable.of_nonneg_of_le hnn hle hasSum_inv_succ_sq.summable
  refine ⟨tsum_nonneg hnn, ?_⟩
  have h3 : zetaR M ≤ Real.pi ^ 2 / 6 := hasSum_le hle hs.hasSum hasSum_inv_succ_sq
  have hp := Real.pi_lt_d2
  have hp0 := Real.pi_pos
  nlinarith

/- English proof (translation)
Take `⟨h0, h2⟩` from `zetaR_nonneg_le_two M hM`. Break down `h0.eq_or_lt with h | h` into its components or cases. Rewrite using `[← h, Real.log_zero]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation.
-/
lemma log_zetaR_le_one (M : ℕ) (hM : 2 ≤ M) : Real.log (zetaR M) ≤ 1 := by
  obtain ⟨h0, h2⟩ := zetaR_nonneg_le_two M hM
  rcases h0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; norm_num
  · calc Real.log (zetaR M) ≤ Real.log 2 := Real.log_le_log h h2
      _ ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num

/- English proof (translation)
Proceed by induction on `r, hkr using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hn ih`. Rewrite using `[Finset.sum_Ico_succ_top (by omega : k + 1 ≤ n + 1), Finset.sum_range_succ, ← ih]`. Simplify using `only [Nat.add_sub_cancel]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_log_factorial (k r : ℕ) (hkr : k ≤ r) :
    ∑ M ∈ Ico (k + 1) (r + 1), Real.log (((M - 1).factorial : ℕ) : ℝ)
      + ∑ i ∈ range k, Real.log ((i.factorial : ℕ) : ℝ)
      = ∑ i ∈ range r, Real.log ((i.factorial : ℕ) : ℝ) := by
  induction r, hkr using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top (by omega : k + 1 ≤ n + 1), Finset.sum_range_succ, ← ih]
    simp only [Nat.add_sub_cancel]
    ring

/- English proof (translation)
Establish `hF : 0 < ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)` using `prod_pos (fun i _ => by positivity)`. Use `⟨div_pos h hF, ?_⟩` and prove the remaining obligations. Unfold `dimVN`. Rewrite using `[Real.log_div h.ne' hF.ne', Real.log_prod (fun i _ => by positivity)]`.
-/
lemma log_dimVN (x : ℕ → ℝ) (N : ℕ) (h : 0 < vandN x N) :
    0 < dimVN x N ∧ Real.log (dimVN x N)
      = Real.log (vandN x N) - ∑ i ∈ range N, Real.log ((i.factorial : ℕ) : ℝ) := by
  have hF : 0 < ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) := prod_pos (fun i _ => by positivity)
  refine ⟨div_pos h hF, ?_⟩
  unfold dimVN
  rw [Real.log_div h.ne' hF.ne', Real.log_prod (fun i _ => by positivity)]

/- English proof (translation)
Take `⟨hu, hl, hVb⟩` from `hV ε x hε hx k m Δ u v b w hk hm hΔ hP`. Take `⟨-, -, -, -, -, hbw, hbb, hb0, hwtop⟩` from `hP`. Use `set L := x ^ ε with hLdef`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hL1 : 1 ≤ L` using `Real.one_le_rpow hx hε.le`.

Establish `hk0 : (0 : ℝ) < k` using `by exact_mod_cast (by omega : 0 < k)`. Establish `hk2 : (2 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hlogx : Real.log x ≤ L / ε`. Establish `h1` using `Real.add_one_le_exp (Real.log x * ε)`. Rewrite `h1` using `[← Real.rpow_def_of_pos hx0]`.

Rewrite using `[le_div_iff₀ hε]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogk : Real.log k ≤ C₀ * (L / ε)`. Establish `h1 : Real.log k ≤ Real.log (x ^ C₀)` using `Real.log_le_log hk0 hkx`. Rewrite `h1` using `[Real.log_rpow hx0]`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hlogx hC₀]`. Establish `hexp0 : 0 < Real.exp L` using `Real.exp_pos L`. Establish `hxe : 0 < x * Real.exp L` using `mul_pos hx0 hexp0`. Establish `hlog8a : Real.log (8 * (x * Real.exp L)) ≤ 7 + L / ε + L`. Rewrite using `[Real.log_mul (by norm_num) hxe.ne', Real.log_mul hx0.ne' hexp0.ne', Real.log_exp]`.

Establish `: Real.log 8 ≤ 8 - 1` using `Real.log_le_sub_one_of_pos (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog2 : Real.log 2 ≤ 1`. Use `Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith` as an intermediate fact. Establish `hΔk : (8 : ℝ) ≤ k * (4 * Δ)` using `by nlinarith`.

Establish `hb0x : 8 * x ≤ b 0`. Use `(le_div_iff₀ hx0).mp hb0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hb0' : 1 ≤ b 0` using `by nlinarith`. Establish `hbmono : ∀ j, j < m → b 0 ≤ b j`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro _`. Conclude with `le_refl _`. Consider the case `succ n ih`.

Introduce `hn`. Establish `h1` using `(hbb n hn).2`. Establish `h2` using `ih (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbpos : ∀ j, j < m → 0 < b j` using `fun j hj => by linarith [hbmono j hj]`.

Establish `hwpos : ∀ j, j < m → 0 < w j` using `fun j hj => by linarith [hbpos j hj, (hbw j hj).1]`. Establish `hwstep : ∀ j, j + 1 < m → w j ≤ w (j + 1)`. Introduce `j hj`. Establish `h1` using `(hbb j hj).1`. Establish `h2` using `(hbw (j + 1) hj).1`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hwmono : ∀ i j, i ≤ j → j < m → w i ≤ w j`. Introduce `i j hij`. Proceed by induction on `j, hij using Nat.le_induction with`. Consider the case `base => intro _`.

Conclude with `le_refl _`. Consider the case `succ n hn ih`. Introduce `h`. Conclude with `le_trans (ih (by omega)) (hwstep n h)`. Establish `hwtop' : ∀ j, j < m → w j ≤ 2 * Real.exp L` using `fun j hj => le_trans (hwmono j (m - 1) (by omega) (by omega)) hwtop`.

Establish `hlogtop : Real.log (2 * Real.exp L) = Real.log 2 + L`. Rewrite using `[Real.log_mul (by norm_num) hexp0.ne', Real.log_exp]`. Establish `hlogb : ∀ j, j < m → Real.log (b j) ≤ 1 + L`. Introduce `j hj`. Establish `h1 : Real.log (b j) ≤ Real.log (2 * Real.exp L)` using `Real.log_le_log (hbpos j hj) (le_trans (hbw j hj).1.le (hwtop' j hj))`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsumb : ∑ j ∈ range m, Real.log (b j) ≤ m * (1 + L)`. Use `Finset.sum_le_sum (fun j hj => hlogb j (Finset.mem_range.mp hj))` as an intermediate fact. Simplify using `only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `htele : ∀ n, 1 ≤ n → n ≤ m → ∑ j ∈ range n, (Real.log (w j) - Real.log (b j)) ≤ Real.log (w (n - 1)) - Real.log (b 0)`. Introduce `n hn`. Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base => intro _`. Simplify using the standard rewrite rules.

Consider the case `succ n hn ih`. Introduce `h`. Rewrite using `[Finset.sum_range_succ]`. Establish `h1` using `ih (by omega)`. Establish `h2 : Real.log (w (n - 1)) ≤ Real.log (b n)`.

Establish `h3` using `(hbb (n - 1) (by omega)).1`. Rewrite `h3` using `[show n - 1 + 1 = n by omega]`. Conclude with `Real.log_le_log (hwpos (n - 1) (by omega)) h3.le`. Simplify using `only [Nat.add_sub_cancel]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `htel` using `htele m hm le_rfl`. Establish `hwlast : Real.log (w (m - 1)) ≤ 1 + L`. Establish `h1 : Real.log (w (m - 1)) ≤ Real.log (2 * Real.exp L)` using `Real.log_le_log (hwpos (m - 1) (by omega)) hwtop`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlb0 : 0 ≤ Real.log (b 0)` using `Real.log_nonneg hb0'`.

Establish `hsplit : ∑ j ∈ range m, Real.log (w j) = ∑ j ∈ range m, Real.log (b j) + ∑ j ∈ range m, (Real.log (w j) - Real.log (b j))`. Rewrite using `[Finset.sum_sub_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hkA : (k : ℝ) * (L / ε) * 2 + 2 * k * (C₀ * (L / ε)) = k * L * ((2 + 2 * C₀) / ε)`. Clear the denominators using the available nonvanishing facts.

Establish `hm0 : (1 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hkL : (k : ℝ) * 1 ≤ k * L` using `mul_le_mul_of_nonneg_left hL1 hk0.le`. Establish `hmL : (m : ℝ) * 1 ≤ m * L` using `mul_le_mul_of_nonneg_left hL1 (by linarith)`. Establish `e1 : (k : ℝ) * Real.log (8 * (x * Real.exp L)) ≤ k * (7 + L / ε + L)` using `mul_le_mul_of_nonneg_left hlog8a hk0.le`. Establish `e2 : (k : ℝ) * Real.log k ≤ k * (C₀ * (L / ε))` using `mul_le_mul_of_nonneg_left hlogk hk0.le`.

Establish `e3 : (k : ℝ) * ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) ≤ k * (1 + L)`. Apply `mul_le_mul_of_nonneg_left _ hk0.le` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hu, hl, hwpos, ?_⟩` and prove the remaining obligations. Rewrite using `[hsplit]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma place_bound (hV : VandPlace) (ε x C₀ : ℝ) (hε : 0 < ε) (hx : 1 ≤ x) (hC₀ : 0 ≤ C₀)
    (k m : ℕ) (Δ : ℝ) (u v b w : ℕ → ℝ) (hk : 2 ≤ k) (hm : 1 ≤ m) (hΔ : 1 ≤ Δ)
    (hkx : (k : ℝ) ≤ x ^ C₀)
    (hP : PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m u v b w) :
    0 < vandN u k ∧ 0 < vandN (rowPar k v b) (k - 1 + m) ∧ (∀ j, j < m → 0 < w j) ∧
    (k : ℝ) * ∑ j ∈ range m, Real.log (w j)
      ≤ (Real.log (vandN (rowPar k v b) (k - 1 + m)) - Real.log (vandN u k))
        + k * x ^ ε * (20 + (2 + 2 * C₀) / ε) + 2 * m * x ^ ε := by
  obtain ⟨hu, hl, hVb⟩ := hV ε x hε hx k m Δ u v b w hk hm hΔ hP
  obtain ⟨-, -, -, -, -, hbw, hbb, hb0, hwtop⟩ := hP
  set L := x ^ ε with hLdef
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ L := Real.one_le_rpow hx hε.le
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogx : Real.log x ≤ L / ε := by
    have h1 := Real.add_one_le_exp (Real.log x * ε)
    rw [← Real.rpow_def_of_pos hx0] at h1
    rw [le_div_iff₀ hε]; linarith
  have hlogk : Real.log k ≤ C₀ * (L / ε) := by
    have h1 : Real.log k ≤ Real.log (x ^ C₀) := Real.log_le_log hk0 hkx
    rw [Real.log_rpow hx0] at h1
    nlinarith [mul_le_mul_of_nonneg_left hlogx hC₀]
  have hexp0 : 0 < Real.exp L := Real.exp_pos L
  have hxe : 0 < x * Real.exp L := mul_pos hx0 hexp0
  have hlog8a : Real.log (8 * (x * Real.exp L)) ≤ 7 + L / ε + L := by
    rw [Real.log_mul (by norm_num) hxe.ne', Real.log_mul hx0.ne' hexp0.ne', Real.log_exp]
    have : Real.log 8 ≤ 8 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hΔk : (8 : ℝ) ≤ k * (4 * Δ) := by nlinarith
  have hb0x : 8 * x ≤ b 0 := by
    have := (le_div_iff₀ hx0).mp hb0; nlinarith
  have hb0' : 1 ≤ b 0 := by nlinarith
  have hbmono : ∀ j, j < m → b 0 ≤ b j := by
    intro j
    induction j with
    | zero => intro _; exact le_refl _
    | succ n ih =>
      intro hn
      have h1 := (hbb n hn).2
      have h2 := ih (by omega)
      linarith
  have hbpos : ∀ j, j < m → 0 < b j := fun j hj => by linarith [hbmono j hj]
  have hwpos : ∀ j, j < m → 0 < w j := fun j hj => by linarith [hbpos j hj, (hbw j hj).1]
  have hwstep : ∀ j, j + 1 < m → w j ≤ w (j + 1) := by
    intro j hj
    have h1 := (hbb j hj).1
    have h2 := (hbw (j + 1) hj).1
    linarith
  have hwmono : ∀ i j, i ≤ j → j < m → w i ≤ w j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; exact le_refl _
    | succ n hn ih =>
      intro h
      exact le_trans (ih (by omega)) (hwstep n h)
  have hwtop' : ∀ j, j < m → w j ≤ 2 * Real.exp L := fun j hj =>
    le_trans (hwmono j (m - 1) (by omega) (by omega)) hwtop
  have hlogtop : Real.log (2 * Real.exp L) = Real.log 2 + L := by
    rw [Real.log_mul (by norm_num) hexp0.ne', Real.log_exp]
  have hlogb : ∀ j, j < m → Real.log (b j) ≤ 1 + L := by
    intro j hj
    have h1 : Real.log (b j) ≤ Real.log (2 * Real.exp L) :=
      Real.log_le_log (hbpos j hj) (le_trans (hbw j hj).1.le (hwtop' j hj))
    linarith
  have hsumb : ∑ j ∈ range m, Real.log (b j) ≤ m * (1 + L) := by
    have := Finset.sum_le_sum (fun j hj => hlogb j (Finset.mem_range.mp hj))
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  have htele : ∀ n, 1 ≤ n → n ≤ m →
      ∑ j ∈ range n, (Real.log (w j) - Real.log (b j)) ≤ Real.log (w (n - 1)) - Real.log (b 0) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; simp
    | succ n hn ih =>
      intro h
      rw [Finset.sum_range_succ]
      have h1 := ih (by omega)
      have h2 : Real.log (w (n - 1)) ≤ Real.log (b n) := by
        have h3 := (hbb (n - 1) (by omega)).1
        rw [show n - 1 + 1 = n by omega] at h3
        exact Real.log_le_log (hwpos (n - 1) (by omega)) h3.le
      simp only [Nat.add_sub_cancel]
      linarith
  have htel := htele m hm le_rfl
  have hwlast : Real.log (w (m - 1)) ≤ 1 + L := by
    have h1 : Real.log (w (m - 1)) ≤ Real.log (2 * Real.exp L) :=
      Real.log_le_log (hwpos (m - 1) (by omega)) hwtop
    linarith
  have hlb0 : 0 ≤ Real.log (b 0) := Real.log_nonneg hb0'
  have hsplit : ∑ j ∈ range m, Real.log (w j) = ∑ j ∈ range m, Real.log (b j)
      + ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) := by
    rw [Finset.sum_sub_distrib]; ring
  have hkA : (k : ℝ) * (L / ε) * 2 + 2 * k * (C₀ * (L / ε)) = k * L * ((2 + 2 * C₀) / ε) := by
    field_simp
  have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkL : (k : ℝ) * 1 ≤ k * L := mul_le_mul_of_nonneg_left hL1 hk0.le
  have hmL : (m : ℝ) * 1 ≤ m * L := mul_le_mul_of_nonneg_left hL1 (by linarith)
  have e1 : (k : ℝ) * Real.log (8 * (x * Real.exp L)) ≤ k * (7 + L / ε + L) :=
    mul_le_mul_of_nonneg_left hlog8a hk0.le
  have e2 : (k : ℝ) * Real.log k ≤ k * (C₀ * (L / ε)) := mul_le_mul_of_nonneg_left hlogk hk0.le
  have e3 : (k : ℝ) * ∑ j ∈ range m, (Real.log (w j) - Real.log (b j)) ≤ k * (1 + L) := by
    apply mul_le_mul_of_nonneg_left _ hk0.le; linarith
  refine ⟨hu, hl, hwpos, ?_⟩
  rw [hsplit]
  linarith

/- English proof (translation)
Introduce `ε C₀ hε _ hC₀`. Use `⟨30 + (2 + 2 * C₀) / ε, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `only`. Introduce `f m k vE Δ g₁ g₂ u v b w Dstar dstar massk massr Isig Ipi Lval hf hm hk hkx hπ hvE hΔ hg₁ hg₂ hP hmk hmr hIs hIp hLv hmass hidx hD hd`.

Establish `hpl : ∀ ρ, ρ < f → _` using `fun ρ hρ => place_bound hV ε x C₀ hε hx hC₀ k m Δ (u ρ) (v ρ) (b ρ) (w ρ) hk hm hΔ hkx (hP ρ hρ)`. Use `set L := x ^ ε with hLdef`. Use `set K := (2 + 2 * C₀) / ε with hKdef`. Establish `hK0 : 0 ≤ K` using `by positivity`. Establish `hx0 : 0 < x` using `by linarith`.

Establish `hL1 : 1 ≤ L` using `Real.one_le_rpow hx hε.le`. Establish `hf0 : (0 : ℝ) < f` using `by exact_mod_cast (by omega : 0 < f)`. Establish `hf1 : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hk0 : (0 : ℝ) < k` using `by exact_mod_cast (by omega : 0 < k)`. Establish `hk2 : (2 : ℝ) ≤ k` using `by exact_mod_cast hk`.

Establish `hm1 : (1 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hvE0 : 0 < vE` using `by linarith [Real.pi_pos]`. Establish `hvp : 0 < vE / Real.pi` using `div_pos hvE0 Real.pi_pos`. Use `set lv := Real.log (vE / Real.pi) with hlvdef`. Establish `hlv0 : 0 ≤ lv` using `Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith)`.

Establish `hlvL : lv ≤ L`. Rewrite using `[hlvdef, Real.log_div hvE0.ne' Real.pi_pos.ne']`. Establish `: 0 ≤ Real.log Real.pi` using `Real.log_nonneg (by linarith [Real.pi_gt_three])`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog2 : Real.log 2 ≤ 1`.

Use `Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith` as an intermediate fact. Establish `hl2vE : Real.log (2 * vE) ≤ 1 + L`. Rewrite using `[Real.log_mul (by norm_num) hvE0.ne']; linarith`. Establish `hl23 : -(1 / 2 : ℝ) ≤ Real.log (2 / 3)`. Use `Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2 / 3); norm_num at this ⊢; linarith` as an intermediate fact.

Establish `hwpos : ∀ ρ, ρ < f → ∀ j, j < m → 0 < w ρ j` using `fun ρ hρ => (hpl ρ hρ).2.2.1`. Establish `hsum : (k : ℝ) * ∑ ρ ∈ range f, ∑ j ∈ range m, Real.log (w ρ j) ≤ ∑ ρ ∈ range f, (Real.log (vandN (rowPar k (v ρ) (b ρ)) (k - 1 + m)) - Real.log (vandN (u ρ) k)) + f * (k * L * (20 + K) + 2 * m * L)`. Establish `h` using `Finset.sum_le_sum (fun ρ hρ => (hpl ρ (Finset.mem_range.mp hρ)).2.2.2)`. Rewrite `h` using `[Finset.sum_add_distrib, Finset.sum_add_distrib]`. Simplify using `only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h`.

Rewrite using `[Finset.mul_sum]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hterm : ∀ M ∈ Ico (k + 1) (k - 1 + m + 1), 0 < ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M ∧ Real.log (((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M) = f * Real.log (((M - 1).factorial …`. Introduce `M hM`. Establish `hLM` using `(hLv M hM).1`.

Establish `hfac : (0 : ℝ) < (((M - 1).factorial : ℕ) : ℝ)` using `by positivity`. Establish `hpw : 0 < (vE / Real.pi) ^ M` using `pow_pos hvp M`. Establish `hA : 0 < (((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M` using `mul_pos hfac hpw`. Establish `hAf : 0 < ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f` using `pow_pos hA f`. Establish `h2v : 0 < (2 * vE) ^ f` using `pow_pos (by linarith) f`.

Establish `hS : 0 < Real.sqrt ((2 * vE) ^ f)` using `Real.sqrt_pos.mpr h2v`. Establish `hQ : 0 < ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f)` using `div_pos hAf hS`. Use `⟨mul_pos hQ hLM, ?_⟩` and prove the remaining obligations. Rewrite using `[Real.log_mul hQ.ne' hLM.ne', Real.log_div hAf.ne' hS.ne', Real.log_pow, Real.log_sqrt h2v.le, Real.log_pow, Real.log_mul hfac.ne' hpw.ne', Real.log_pow]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hrestM : ∀ M ∈ Ico (k + 1) (k - 1 + m + 1), (f : ℝ) * k * lv - f / 2 * (1 + L) - f ≤ f * M * lv - f / 2 * Real.log (2 * vE) + Real.log (Lval M)`. Introduce `M hM`. Establish `hM'` using `Finset.mem_Ico.mp hM`. Establish `hMk : (k : ℝ) ≤ M` using `by exact_mod_cast (by omega : k ≤ M)`. Establish `h1 : (f : ℝ) * k * lv ≤ f * M * lv`.

Use `mul_nonneg (mul_nonneg hf0.le hlv0) (sub_nonneg.mpr hMk)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (f : ℝ) / 2 * Real.log (2 * vE) ≤ f / 2 * (1 + L)` using `mul_le_mul_of_nonneg_left hl2vE (by positivity)`. Establish `h3 : -(f : ℝ) ≤ Real.log (Lval M)`. Establish `ha` using `(hLv M hM).2`.

Establish `hz` using `log_zetaR_le_one M (by omega)`. Establish `hz' : (f : ℝ) * Real.log (zetaR M) ≤ f * 1` using `mul_le_mul_of_nonneg_left hz hf0.le`. Use `neg_abs_le (Real.log (Lval M))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hrest : ((m : ℝ) - 1) * ((f : ℝ) * k * lv - f / 2 * (1 + L) - f) ≤ ∑ M ∈ Ico (k + 1) (k - 1 + m + 1), (f * M * lv - f / 2 * Real.log (2 * vE) + Real.log (Lval M))`. Establish `h` using `Finset.sum_le_sum hrestM`. Rewrite `h` using `[Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]`. Establish `hc : ((k - 1 + m + 1 - (k + 1) : ℕ) : ℝ) = (m : ℝ) - 1`. Rewrite using `[show k - 1 + m + 1 - (k + 1) = m - 1 by omega, Nat.cast_sub hm, Nat.cast_one]`.

Rewrite `h` using `[hc]`. Conclude with `h`. Establish `hprodM : 0 < ∏ M ∈ Ico (k + 1) (k - 1 + m + 1), ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M` using `prod_pos (fun M hM => (hterm M hM).1)`. Establish `hlogmass : Real.log massr = Real.log massk + (f * ∑ M ∈ Ico (k + 1) (k - 1 + m + 1), Real.log (((M - 1).factorial : ℕ) : ℝ) + ∑ M ∈ Ico (k + 1) (k - 1 + m + 1), (f * M * lv - f / 2 * Real.log (2 * vE) + Real.log (Lval M)))`. Rewrite using `[hmass, Real.log_mul hmk.ne' hprodM.ne', Real.log_prod (fun M hM => (hterm M hM).1.ne'), Finset.sum_congr rfl (fun M hM => (hterm M hM).2), Finset.sum_add_distrib, Finset.mul_sum]`.

Establish `hfact` using `sum_log_factorial k (k - 1 + m) (by omega)`. Establish `hdimR : ∀ ρ ∈ range f, 0 < dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m) ∧ Real.log (dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m)) = Real.log (vandN (rowPar k (v ρ) (b ρ)) (k - 1 + m)) - ∑ i ∈ range (k - 1 + m), Real.log ((i.factorial : ℕ) : ℝ)` using `fun ρ hρ => log_dimVN _ _ (hpl ρ (Finset.mem_range.mp hρ)).2.1`. Establish `hdimu : ∀ ρ ∈ range f, 0 < dimVN (u ρ) k ∧ Real.log (dimVN (u ρ) k) = Real.log (vandN (u ρ) k) - ∑ i ∈ range k, Real.log ((i.factorial : ℕ) : ℝ)` using `fun ρ hρ => log_dimVN _ _ (hpl ρ (Finset.mem_range.mp hρ)).1`. Establish `hPR : 0 < ∏ ρ ∈ range f, dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m)` using `prod_pos (fun ρ hρ => (hdimR ρ hρ).1)`. Establish `hPu : 0 < ∏ ρ ∈ range f, dimVN (u ρ) k` using `prod_pos (fun ρ hρ => (hdimu ρ hρ).1)`.

Establish `h23 : (0 : ℝ) < (2 / 3 : ℝ) ^ f` using `by positivity`. Establish `hA1 : 0 < (2 / 3 : ℝ) ^ f * massr` using `mul_pos h23 hmr`. Establish `hA2 : 0 < (2 / 3 : ℝ) ^ f * massr * Isig` using `mul_pos hA1 hIs`. Establish `hLD : 0 < (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m)` using `mul_pos hA2 hPR`. Establish `hmI : 0 < massk * Ipi` using `mul_pos hmk hIp`.

Establish `hd0 : 0 < dstar` using `by rw [hd]; exact mul_pos hmI hPu`. Establish `hD0 : 0 < Dstar` using `lt_of_lt_of_le hLD hD`. Establish `hlD` using `Real.log_le_log hLD hD`. Rewrite `hlD` using `[Real.log_mul hA2.ne' hPR.ne', Real.log_mul hA1.ne' hIs.ne', Real.log_mul h23.ne' hmr.ne', Real.log_pow, Real.log_prod (fun ρ hρ => (hdimR ρ hρ).1.ne'), Finset.sum_congr rfl (fun ρ hρ => (hdimR ρ hρ).2), Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Establish `hld : Real.log dstar = Real.log massk + Real.log Ipi + (∑ ρ ∈ range f, Real.log (vandN (u ρ) k) - f * ∑ i ∈ range k, Real.log ((i.factorial : ℕ) : ℝ))`.

Rewrite using `[hd, Real.log_mul hmI.ne' hPu.ne', Real.log_mul hmk.ne' hIp.ne', Real.log_prod (fun ρ hρ => (hdimu ρ hρ).1.ne'), Finset.sum_congr rfl (fun ρ hρ => (hdimu ρ hρ).2), Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Establish `hDd : Real.log (Dstar / dstar) = Real.log Dstar - Real.log dstar` using `Real.log_div hD0.ne' hd0.ne'`. Establish `hVd : ∑ ρ ∈ range f, (Real.log (vandN (rowPar k (v ρ) (b ρ)) (k - 1 + m)) - Real.log (vandN (u ρ) k)) = ∑ ρ ∈ range f, Real.log (vandN (rowPar k (v ρ) (b ρ)) (k - 1 + m)) - ∑ ρ ∈ range f, Real.log (vandN (u ρ) k)` using `by rw [Finset.sum_sub_distrib]`. Establish `hfact' : (f : ℝ) * ∑ M ∈ Ico (k + 1) (k - 1 + m + 1), Real.log (((M - 1).factorial : ℕ) : ℝ) + f * ∑ i ∈ range k, Real.log ((i.factorial : ℕ) : ℝ) = f * ∑ i ∈ range (k - 1 + m), Real.log ((i.factorial : ℕ) : ℝ)`. Rewrite using `[← mul_add, hfact]`.

Establish `hG0 : 0 ≤ Real.log g₁ + Real.log g₂`. Use `Real.log_nonneg hg₁` as an intermediate fact. Use `Real.log_nonneg hg₂` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg0 : 0 < g₁ * g₂` using `by positivity`.

Establish `hI : -(2 * f * Real.log 2) + f * k * m * (Real.log g₁ + Real.log g₂) ≤ Real.log Isig - Real.log Ipi`. Establish `hi1 : (0 : ℝ) < ((2 : ℝ) ^ (2 * f))⁻¹` using `by positivity`. Establish `hi2 : 0 < (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2)` using `Real.rpow_pos_of_pos hg0 _`. Establish `h1` using `Real.log_le_log (mul_pos hi1 hi2) hidx`. Rewrite `h1` using `[Real.log_div hIs.ne' hIp.ne', Real.log_mul hi1.ne' hi2.ne', Real.log_inv, Real.log_pow, Real.log_rpow hg0, Real.log_mul (by positivity) (by positivity)]`.

Move the coercions through the operations in `at h1`. Establish `hm0 : 0 ≤ (m : ℝ) - 1` using `by linarith`. Establish `hx1 : 0 ≤ (f : ℝ) * m * ((m : ℝ) - 1) * (Real.log g₁ + Real.log g₂)` using `by positivity`. Establish `he : (f : ℝ) * m * (2 * k + m - 1) / 2 * (Real.log g₁ + Real.log g₂) = f * k * m * (Real.log g₁ + Real.log g₂) + (f : ℝ) * m * ((m : ℝ) - 1) * (Real.log g₁ + Real.log g₂) / 2`. Expand and normalize the polynomial expressions, which then agree.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hwl : ∀ ρ ∈ range f, ∀ j ∈ range m, Real.log (w ρ j * vE / Real.pi) = Real.log (w ρ j) + lv`. Introduce `ρ hρ j hj`. Rewrite using `[mul_div_assoc, Real.log_mul (hwpos ρ (Finset.mem_range.mp hρ) j (Finset.mem_range.mp hj)).ne' hvp.ne']`. Establish `hLHS : ∑ j ∈ range m, (1 / (f : ℝ)) * ∑ ρ ∈ range f, Real.log (w ρ j * vE / Real.pi) = (1 / (f : ℝ)) * ∑ ρ ∈ range f, ∑ j ∈ range m, Real.log (w ρ j) + m * lv`.

Establish `e : ∀ j ∈ range m, (1 / (f : ℝ)) * ∑ ρ ∈ range f, Real.log (w ρ j * vE / Real.pi) = (1 / (f : ℝ)) * ∑ ρ ∈ range f, Real.log (w ρ j) + lv`. Introduce `j hj`. Rewrite using `[Finset.sum_congr rfl (fun ρ hρ => hwl ρ hρ j hj), Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_add, ← mul_assoc, one_div_mul_cancel hf0.ne', one_mul]`. Rewrite using `[Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`. Rewrite using `[hLHS]`.

Use `set T := ∑ ρ ∈ range f, ∑ j ∈ range m, Real.log (w ρ j) with hT`. Use `set G := Real.log g₁ + Real.log g₂ with hGdef`. Rewrite using `[show (1 : ℝ) / (f * k) * Real.log (Dstar / dstar) = Real.log (Dstar / dstar) / (f * k) by ring, le_div_iff₀ (by positivity)]`. Establish `hexp : (1 / (f : ℝ) * T + m * lv + m * G - (30 + K) * (L + (m : ℝ) ^ 2 * L / k)) * (f * k) = k * T + f * k * m * lv + f * k * m * G - (30 + K) * (f * k * L + f * (m : ℝ) ^ 2 * L)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hexp]`. Establish `hfk : (0 : ℝ) ≤ f * k` using `by positivity`. Establish `P1 : (f : ℝ) * k * lv ≤ f * k * L` using `mul_le_mul_of_nonneg_left hlvL hfk`. Establish `hmm : (m : ℝ) ≤ (m : ℝ) ^ 2` using `by rw [sq]; exact le_mul_of_one_le_right (by linarith) hm1`. Establish `hm2L : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * L` using `le_mul_of_one_le_right (sq_nonneg _) hL1`.

Establish `q1 : ((m : ℝ) - 1) * (1 + L) ≤ (m : ℝ) ^ 2 * (2 * L)` using `mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)`. Establish `P2 : (f : ℝ) * (((m : ℝ) - 1) * (1 + L)) ≤ f * ((m : ℝ) ^ 2 * (2 * L))` using `mul_le_mul_of_nonneg_left q1 hf0.le`. Establish `q2 : (m : ℝ) - 1 ≤ (m : ℝ) ^ 2 * L` using `by linarith`. Establish `P3 : (f : ℝ) * ((m : ℝ) - 1) ≤ f * ((m : ℝ) ^ 2 * L)` using `mul_le_mul_of_nonneg_left q2 hf0.le`. Establish `hkL1 : (1 : ℝ) ≤ k * L` using `one_le_mul_of_one_le_of_one_le (by linarith) hL1`.

Establish `P4 : (f : ℝ) * 1 ≤ f * (k * L)` using `mul_le_mul_of_nonneg_left hkL1 hf0.le`. Establish `P5 : (f : ℝ) * Real.log 2 ≤ f * 1` using `mul_le_mul_of_nonneg_left hlog2 hf0.le`. Establish `hmL2 : (m : ℝ) * L ≤ (m : ℝ) ^ 2 * L` using `mul_le_mul_of_nonneg_right hmm (by linarith)`. Establish `P6 : (f : ℝ) * ((m : ℝ) * L) ≤ f * ((m : ℝ) ^ 2 * L)` using `mul_le_mul_of_nonneg_left hmL2 hf0.le`. Establish `P7 : 0 ≤ K * (f * ((m : ℝ) ^ 2 * L))` using `by positivity`.

Establish `P8 : 0 ≤ (f : ℝ) * ((m : ℝ) ^ 2 * L)` using `by positivity`. Establish `P9 : (f : ℝ) * (-(1 / 2)) ≤ f * Real.log (2 / 3)` using `mul_le_mul_of_nonneg_left hl23 hf0.le`. Rewrite using `[hDd]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem logRatioLowerBound_of_logVandermondeGap (hV : VandPlace) : LogRatioLowerBound := by
  intro ε C₀ hε _ hC₀
  refine ⟨30 + (2 + 2 * C₀) / ε, ?_⟩
  intro x hx
  dsimp only
  intro f m k vE Δ g₁ g₂ u v b w Dstar dstar massk massr Isig Ipi Lval hf hm hk hkx hπ hvE hΔ
    hg₁ hg₂ hP hmk hmr hIs hIp hLv hmass hidx hD hd
  have hpl : ∀ ρ, ρ < f → _ := fun ρ hρ =>
    place_bound hV ε x C₀ hε hx hC₀ k m Δ (u ρ) (v ρ) (b ρ) (w ρ) hk hm hΔ hkx (hP ρ hρ)
  set L := x ^ ε with hLdef
  set K := (2 + 2 * C₀) / ε with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ L := Real.one_le_rpow hx hε.le
  have hf0 : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hvE0 : 0 < vE := by linarith [Real.pi_pos]
  have hvp : 0 < vE / Real.pi := div_pos hvE0 Real.pi_pos
  set lv := Real.log (vE / Real.pi) with hlvdef
  have hlv0 : 0 ≤ lv := Real.log_nonneg (by rw [le_div_iff₀ Real.pi_pos]; linarith)
  have hlvL : lv ≤ L := by
    rw [hlvdef, Real.log_div hvE0.ne' Real.pi_pos.ne']
    have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hl2vE : Real.log (2 * vE) ≤ 1 + L := by
    rw [Real.log_mul (by norm_num) hvE0.ne']; linarith
  have hl23 : -(1 / 2 : ℝ) ≤ Real.log (2 / 3) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2 / 3); norm_num at this ⊢; linarith

  have hwpos : ∀ ρ, ρ < f → ∀ j, j < m → 0 < w ρ j := fun ρ hρ => (hpl ρ hρ).2.2.1
  have hsum : (k : ℝ) * ∑ ρ ∈ range f, ∑ j ∈ range m, Real.log (w ρ j) ≤
      ∑ ρ ∈ range f, (Real.log (vandN (rowPar k (v ρ) (b ρ)) (k - 1 + m)) - Real.log (vandN (u ρ) k))
        + f * (k * L * (20 + K) + 2 * m * L) := by
    have h := Finset.sum_le_sum (fun ρ hρ => (hpl ρ (Finset.mem_range.mp hρ)).2.2.2)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    rw [Finset.mul_sum]
    linarith

  have hterm : ∀ M ∈ Ico (k + 1) (k - 1 + m + 1),
      0 < ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M ∧
      Real.log (((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f)
        * Lval M) = f * Real.log (((M - 1).factorial : ℕ) : ℝ)
          + (f * M * lv - f / 2 * Real.log (2 * vE) + Real.log (Lval M)) := by
    intro M hM
    have hLM := (hLv M hM).1
    have hfac : (0 : ℝ) < (((M - 1).factorial : ℕ) : ℝ) := by positivity
    have hpw : 0 < (vE / Real.pi) ^ M := pow_pos hvp M
    have hA : 0 < (((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M := mul_pos hfac hpw
    have hAf : 0 < ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f := pow_pos hA f
    have h2v : 0 < (2 * vE) ^ f := pow_pos (by linarith) f
    have hS : 0 < Real.sqrt ((2 * vE) ^ f) := Real.sqrt_pos.mpr h2v
    have hQ : 0 < ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) :=
      div_pos hAf hS
    refine ⟨mul_pos hQ hLM, ?_⟩
    rw [Real.log_mul hQ.ne' hLM.ne', Real.log_div hAf.ne' hS.ne', Real.log_pow,
      Real.log_sqrt h2v.le, Real.log_pow, Real.log_mul hfac.ne' hpw.ne', Real.log_pow]
    ring
  have hrestM : ∀ M ∈ Ico (k + 1) (k - 1 + m + 1),
      (f : ℝ) * k * lv - f / 2 * (1 + L) - f
        ≤ f * M * lv - f / 2 * Real.log (2 * vE) + Real.log (Lval M) := by
    intro M hM
    have hM' := Finset.mem_Ico.mp hM
    have hMk : (k : ℝ) ≤ M := by exact_mod_cast (by omega : k ≤ M)
    have h1 : (f : ℝ) * k * lv ≤ f * M * lv := by
      have := mul_nonneg (mul_nonneg hf0.le hlv0) (sub_nonneg.mpr hMk)
      nlinarith
    have h2 : (f : ℝ) / 2 * Real.log (2 * vE) ≤ f / 2 * (1 + L) :=
      mul_le_mul_of_nonneg_left hl2vE (by positivity)
    have h3 : -(f : ℝ) ≤ Real.log (Lval M) := by
      have ha := (hLv M hM).2
      have hz := log_zetaR_le_one M (by omega)
      have hz' : (f : ℝ) * Real.log (zetaR M) ≤ f * 1 := mul_le_mul_of_nonneg_left hz hf0.le
      have := neg_abs_le (Real.log (Lval M))
      linarith
    linarith
  have hrest : ((m : ℝ) - 1) * ((f : ℝ) * k * lv - f / 2 * (1 + L) - f)
      ≤ ∑ M ∈ Ico (k + 1) (k - 1 + m + 1), (f * M * lv - f / 2 * Real.log (2 * vE) + Real.log (Lval M)) := by
    have h := Finset.sum_le_sum hrestM
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h
    have hc : ((k - 1 + m + 1 - (k + 1) : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [show k - 1 + m + 1 - (k + 1) = m - 1 by omega, Nat.cast_sub hm, Nat.cast_one]
    rw [hc] at h
    exact h
  have hprodM : 0 < ∏ M ∈ Ico (k + 1) (k - 1 + m + 1),
      ((((M - 1).factorial : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f / Real.sqrt ((2 * vE) ^ f) * Lval M :=
    prod_pos (fun M hM => (hterm M hM).1)
  have hlogmass : Real.log massr = Real.log massk
      + (f * ∑ M ∈ Ico (k + 1) (k - 1 + m + 1), Real.log (((M - 1).factorial : ℕ) : ℝ)
        + ∑ M ∈ Ico (k + 1) (k - 1 + m + 1), (f * M * lv - f / 2 * Real.log (2 * vE) + Real.log (Lval M))) := by
    rw [hmass, Real.log_mul hmk.ne' hprodM.ne', Real.log_prod (fun M hM => (hterm M hM).1.ne'),
      Finset.sum_congr rfl (fun M hM => (hterm M hM).2), Finset.sum_add_distrib, Finset.mul_sum]
  have hfact := sum_log_factorial k (k - 1 + m) (by omega)

  have hdimR : ∀ ρ ∈ range f, 0 < dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m) ∧
      Real.log (dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m)) = Real.log (vandN (rowPar k (v ρ) (b ρ)) (k - 1 + m))
        - ∑ i ∈ range (k - 1 + m), Real.log ((i.factorial : ℕ) : ℝ) :=
    fun ρ hρ => log_dimVN _ _ (hpl ρ (Finset.mem_range.mp hρ)).2.1
  have hdimu : ∀ ρ ∈ range f, 0 < dimVN (u ρ) k ∧
      Real.log (dimVN (u ρ) k) = Real.log (vandN (u ρ) k)
        - ∑ i ∈ range k, Real.log ((i.factorial : ℕ) : ℝ) :=
    fun ρ hρ => log_dimVN _ _ (hpl ρ (Finset.mem_range.mp hρ)).1
  have hPR : 0 < ∏ ρ ∈ range f, dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m) :=
    prod_pos (fun ρ hρ => (hdimR ρ hρ).1)
  have hPu : 0 < ∏ ρ ∈ range f, dimVN (u ρ) k := prod_pos (fun ρ hρ => (hdimu ρ hρ).1)
  have h23 : (0 : ℝ) < (2 / 3 : ℝ) ^ f := by positivity
  have hA1 : 0 < (2 / 3 : ℝ) ^ f * massr := mul_pos h23 hmr
  have hA2 : 0 < (2 / 3 : ℝ) ^ f * massr * Isig := mul_pos hA1 hIs
  have hLD : 0 < (2 / 3 : ℝ) ^ f * massr * Isig * ∏ ρ ∈ range f, dimVN (rowPar k (v ρ) (b ρ)) (k - 1 + m) :=
    mul_pos hA2 hPR
  have hmI : 0 < massk * Ipi := mul_pos hmk hIp
  have hd0 : 0 < dstar := by rw [hd]; exact mul_pos hmI hPu
  have hD0 : 0 < Dstar := lt_of_lt_of_le hLD hD
  have hlD := Real.log_le_log hLD hD
  rw [Real.log_mul hA2.ne' hPR.ne', Real.log_mul hA1.ne' hIs.ne', Real.log_mul h23.ne' hmr.ne',
    Real.log_pow, Real.log_prod (fun ρ hρ => (hdimR ρ hρ).1.ne'),
    Finset.sum_congr rfl (fun ρ hρ => (hdimR ρ hρ).2), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hlD
  have hld : Real.log dstar = Real.log massk + Real.log Ipi
      + (∑ ρ ∈ range f, Real.log (vandN (u ρ) k) - f * ∑ i ∈ range k, Real.log ((i.factorial : ℕ) : ℝ)) := by
    rw [hd, Real.log_mul hmI.ne' hPu.ne', Real.log_mul hmk.ne' hIp.ne',
      Real.log_prod (fun ρ hρ => (hdimu ρ hρ).1.ne'),
      Finset.sum_congr rfl (fun ρ hρ => (hdimu ρ hρ).2), Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hDd : Real.log (Dstar / dstar) = Real.log Dstar - Real.log dstar := Real.log_div hD0.ne' hd0.ne'
  have hVd : ∑ ρ ∈ range f, (Real.log (vandN (rowPar k (v ρ) (b ρ)) (k - 1 + m)) - Real.log (vandN (u ρ) k))
      = ∑ ρ ∈ range f, Real.log (vandN (rowPar k (v ρ) (b ρ)) (k - 1 + m))
        - ∑ ρ ∈ range f, Real.log (vandN (u ρ) k) := by rw [Finset.sum_sub_distrib]
  have hfact' : (f : ℝ) * ∑ M ∈ Ico (k + 1) (k - 1 + m + 1), Real.log (((M - 1).factorial : ℕ) : ℝ)
      + f * ∑ i ∈ range k, Real.log ((i.factorial : ℕ) : ℝ)
      = f * ∑ i ∈ range (k - 1 + m), Real.log ((i.factorial : ℕ) : ℝ) := by
    rw [← mul_add, hfact]

  have hG0 : 0 ≤ Real.log g₁ + Real.log g₂ := by
    have := Real.log_nonneg hg₁; have := Real.log_nonneg hg₂; linarith
  have hg0 : 0 < g₁ * g₂ := by positivity
  have hI : -(2 * f * Real.log 2) + f * k * m * (Real.log g₁ + Real.log g₂)
      ≤ Real.log Isig - Real.log Ipi := by
    have hi1 : (0 : ℝ) < ((2 : ℝ) ^ (2 * f))⁻¹ := by positivity
    have hi2 : 0 < (g₁ * g₂) ^ ((f : ℝ) * m * (2 * k + m - 1) / 2) := Real.rpow_pos_of_pos hg0 _
    have h1 := Real.log_le_log (mul_pos hi1 hi2) hidx
    rw [Real.log_div hIs.ne' hIp.ne', Real.log_mul hi1.ne' hi2.ne', Real.log_inv, Real.log_pow,
      Real.log_rpow hg0, Real.log_mul (by positivity) (by positivity)] at h1
    push_cast at h1
    have hm0 : 0 ≤ (m : ℝ) - 1 := by linarith
    have hx1 : 0 ≤ (f : ℝ) * m * ((m : ℝ) - 1) * (Real.log g₁ + Real.log g₂) := by positivity
    have he : (f : ℝ) * m * (2 * k + m - 1) / 2 * (Real.log g₁ + Real.log g₂)
        = f * k * m * (Real.log g₁ + Real.log g₂) + (f : ℝ) * m * ((m : ℝ) - 1) * (Real.log g₁ + Real.log g₂) / 2 := by
      ring
    linarith

  have hwl : ∀ ρ ∈ range f, ∀ j ∈ range m,
      Real.log (w ρ j * vE / Real.pi) = Real.log (w ρ j) + lv := by
    intro ρ hρ j hj
    rw [mul_div_assoc, Real.log_mul (hwpos ρ (Finset.mem_range.mp hρ) j (Finset.mem_range.mp hj)).ne' hvp.ne']
  have hLHS : ∑ j ∈ range m, (1 / (f : ℝ)) * ∑ ρ ∈ range f, Real.log (w ρ j * vE / Real.pi)
      = (1 / (f : ℝ)) * ∑ ρ ∈ range f, ∑ j ∈ range m, Real.log (w ρ j) + m * lv := by
    have e : ∀ j ∈ range m, (1 / (f : ℝ)) * ∑ ρ ∈ range f, Real.log (w ρ j * vE / Real.pi)
        = (1 / (f : ℝ)) * ∑ ρ ∈ range f, Real.log (w ρ j) + lv := by
      intro j hj
      rw [Finset.sum_congr rfl (fun ρ hρ => hwl ρ hρ j hj), Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_add, ← mul_assoc, one_div_mul_cancel hf0.ne', one_mul]
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hLHS]
  set T := ∑ ρ ∈ range f, ∑ j ∈ range m, Real.log (w ρ j) with hT
  set G := Real.log g₁ + Real.log g₂ with hGdef
  rw [show (1 : ℝ) / (f * k) * Real.log (Dstar / dstar) = Real.log (Dstar / dstar) / (f * k) by ring,
    le_div_iff₀ (by positivity)]
  have hexp : (1 / (f : ℝ) * T + m * lv + m * G - (30 + K) * (L + (m : ℝ) ^ 2 * L / k)) * (f * k)
      = k * T + f * k * m * lv + f * k * m * G - (30 + K) * (f * k * L + f * (m : ℝ) ^ 2 * L) := by
    field_simp
  rw [hexp]

  have hfk : (0 : ℝ) ≤ f * k := by positivity
  have P1 : (f : ℝ) * k * lv ≤ f * k * L := mul_le_mul_of_nonneg_left hlvL hfk
  have hmm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by rw [sq]; exact le_mul_of_one_le_right (by linarith) hm1
  have hm2L : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * L := le_mul_of_one_le_right (sq_nonneg _) hL1
  have q1 : ((m : ℝ) - 1) * (1 + L) ≤ (m : ℝ) ^ 2 * (2 * L) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have P2 : (f : ℝ) * (((m : ℝ) - 1) * (1 + L)) ≤ f * ((m : ℝ) ^ 2 * (2 * L)) :=
    mul_le_mul_of_nonneg_left q1 hf0.le
  have q2 : (m : ℝ) - 1 ≤ (m : ℝ) ^ 2 * L := by linarith
  have P3 : (f : ℝ) * ((m : ℝ) - 1) ≤ f * ((m : ℝ) ^ 2 * L) := mul_le_mul_of_nonneg_left q2 hf0.le
  have hkL1 : (1 : ℝ) ≤ k * L := one_le_mul_of_one_le_of_one_le (by linarith) hL1
  have P4 : (f : ℝ) * 1 ≤ f * (k * L) := mul_le_mul_of_nonneg_left hkL1 hf0.le
  have P5 : (f : ℝ) * Real.log 2 ≤ f * 1 := mul_le_mul_of_nonneg_left hlog2 hf0.le
  have hmL2 : (m : ℝ) * L ≤ (m : ℝ) ^ 2 * L := mul_le_mul_of_nonneg_right hmm (by linarith)
  have P6 : (f : ℝ) * ((m : ℝ) * L) ≤ f * ((m : ℝ) ^ 2 * L) := mul_le_mul_of_nonneg_left hmL2 hf0.le
  have P7 : 0 ≤ K * (f * ((m : ℝ) ^ 2 * L)) := by positivity
  have P8 : 0 ≤ (f : ℝ) * ((m : ℝ) ^ 2 * L) := by positivity
  have P9 : (f : ℝ) * (-(1 / 2)) ≤ f * Real.log (2 / 3) := mul_le_mul_of_nonneg_left hl23 hf0.le
  rw [hDd]
  linarith

end Formalism.LogVandermondeBounds.StandardLattice
