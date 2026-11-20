import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRankDivPowOfChooseBoundsStatement

open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `(Real.tendsto_pow_log_div_mul_add_atTop 1 (-(D : ℝ)) 1 one_ne_zero).comp (tendsto_atTop_add_const_right _ (D : ℝ) tendsto_natCast_atTop_atTop)`. Use `h.congr (fun m => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem hsGrowth_log_add_div_tendsto (D : ℕ) :
    Tendsto (fun m : ℕ => Real.log ((m : ℝ) + D) / m) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-(D : ℝ)) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right _ (D : ℝ) tendsto_natCast_atTop_atTop)
  refine h.congr (fun m => ?_)
  simp

/- English proof (translation)
Establish `h3` using `Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)`. Break down `lt_or_ge Y 1 with h | h` into its components or cases. Establish `: ⌊Y⌋₊ = 0` using `Nat.floor_eq_zero.mpr h`. Simplify using `only [this, mul_zero, zero_add, Nat.cast_one, Real.log_one]`. Combine the linear relations using `[abs_nonneg (Real.log Y)]`.

Establish `h1 : ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * Y`. Use `push_cast`. Use `Nat.floor_le hY.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hsGrowth_log_floor_le {Y : ℝ} (hY : 0 < Y) :
    Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log 3 + |Real.log Y| := by
  have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  rcases lt_or_ge Y 1 with h | h
  · have : ⌊Y⌋₊ = 0 := Nat.floor_eq_zero.mpr h
    simp only [this, mul_zero, zero_add, Nat.cast_one, Real.log_one]
    linarith [abs_nonneg (Real.log Y)]
  · have h1 : ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * Y := by
      push_cast
      have := Nat.floor_le hY.le
      linarith
    calc Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (3 * Y) := Real.log_le_log (by positivity) h1
      _ = Real.log 3 + Real.log Y := Real.log_mul (by norm_num) hY.ne'
      _ ≤ Real.log 3 + |Real.log Y| := by linarith [le_abs_self (Real.log Y)]

/- English proof (translation)
Introduce `D e δ N κ t he hκ hκ1 ht hmono h ε hε`. Establish `h' : ∀ s : ℕ, ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ (s < e → ∀ (q : ℕ) (R : ℝ), 0 ≤ R → (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧ N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D))`. Introduce `s`. Distinguish the cases in `hs : s < e`. Take `⟨c, c', C, C', h1, h2, h3⟩` from `h s hs`.

Conclude with `⟨c, c', C, C', h1, h2, fun _ => h3⟩`. Conclude with `⟨0, 0, 1, 1, one_pos, one_pos, fun h => absurd h hs⟩`. Use `choose c c' C C' hC hC' hb using h'`. Use `set L : ℝ := δ / ((e : ℝ) ^ D * D.factorial) with hL`. Establish `hdiv : ∀ q s, s < e → (e * q + s) / e = q ∧ (e * q + s) % e = s`.

Introduce `q s hs`. Prove the components needed by the constructor for the conclusion. Rewrite using `[add_comm, Nat.add_mul_div_left _ _ he, Nat.div_eq_of_lt hs, zero_add]`. Rewrite using `[add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]`. Establish `hlow : Tendsto (fun m : ℕ => ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D) atTop (𝓝 L)`.

Use `GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e δ (fun m => δ * (m / e - c (m % e) + D).choose D) he ?_` and prove the remaining obligations. Introduce `s hs`. Use `⟨c s, 0, fun q => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hdiv (q + c s) s hs`. Simplify using `only [h1, h2, Nat.add_sub_cancel, le_refl]`.

Take `⟨h1, h2⟩` from `hdiv q s hs`. Simplify using `only [h1, h2, add_zero]`. Conclude with `Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))`. Establish `hup : Tendsto (fun m : ℕ => ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D) atTop (𝓝 L)`. Use `GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e δ (fun m => δ * (m / e + c' (m % e) + D).choose D) he ?_` and prove the remaining obligations.

Introduce `s hs`. Use `⟨0, c' s, fun q => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hdiv q s hs`. Simplify using `only [add_zero, h1, h2]`. Conclude with `Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))`.

Take `⟨h1, h2⟩` from `hdiv q s hs`. Simplify using `only [h1, h2, le_refl]`. Use `set B : ℝ := ∑ s ∈ Finset.range e, |Real.log (C s)| with hBdef`. Use `set B' : ℝ := ∑ s ∈ Finset.range e, |Real.log (C' s)| with hB'def`. Use `set P : ℝ := ∑ s ∈ Finset.range e, (c' s : ℝ) with hPdef`.

Use `set M : ℕ := ∑ s ∈ Finset.range e, c s with hMdef`. Establish `hB : ∀ s, s < e → Real.log (C s) ≤ B` using `fun s hs => (le_abs_self _).trans (Finset.single_le_sum (f := fun s => |Real.log (C s)|) (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hs))`. Establish `hB' : ∀ s, s < e → |Real.log (C' s)| ≤ B'` using `fun s hs => Finset.single_le_sum (f := fun s => |Real.log (C' s)|) (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hs)`. Establish `hP : ∀ s, s < e → (c' s : ℝ) ≤ P` using `fun s hs => Finset.single_le_sum (f := fun s => (c' s : ℝ)) (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.mpr hs)`. Establish `hlk : Real.log κ ≤ 0` using `Real.log_nonpos hκ.le hκ1`.

Establish `hlowE : ∀ᶠ m : ℕ in atTop, ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D * (t - (B / m + D * (Real.log ((m : ℝ) + D) / m))) ≤ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1)` using `by filter_upwards [eventually_ge_atTop (e * M + 1)] with m hm`. Establish `hm0' : 0 < m` using `Nat.lt_of_lt_of_le (Nat.succ_pos _) hm`. Establish `hm0 : (0 : ℝ) < m` using `by exact_mod_cast hm0'`. Use `set s := m % e with hs_def`. Establish `hse : s < e` using `Nat.mod_lt _ he`.

Establish `hcm : c s ≤ m / e`. Establish `: M ≤ m / e`. Rewrite using `[Nat.le_div_iff_mul_le he]`. Rewrite using `[mul_comm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `(Finset.single_le_sum (f := c) (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hse)).trans this`. Use `set q := m / e - c s with hq`. Establish `hqm : q ≤ m` using `(Nat.sub_le _ _).trans (Nat.div_le_self _ _)`. Establish `hmq : e * (q + c s) + s = m`. Rewrite using `[hq, Nat.sub_add_cancel hcm]`.

Conclude with `Nat.div_add_mod m e`. Establish `hKpos : 0 < (q + D).choose D` using `Nat.choose_pos (by omega)`. Establish `hKpos' : (0 : ℝ) < ((q + D).choose D : ℝ)` using `by exact_mod_cast hKpos`. Establish `hCs` using `hC s`. Use `set R : ℝ := Real.exp (t * m) / (C s * ((q + D).choose D : ℝ)) with hR`.

Establish `hRpos : 0 < R` using `by rw [hR]; positivity`. Establish `hCKR : C s * ((q + D).choose D : ℝ) * R = Real.exp (t * m)`. Rewrite using `[hR]`. Clear the denominators using the available nonvanishing facts. Establish `hb1` using `(hb s hse q R hRpos.le).1`.

Rewrite `hb1` using `[hmq, hCKR]`. Establish `hK1 : Real.log ((q + D).choose D : ℝ) ≤ D * Real.log ((m : ℝ) + D)`. Rewrite using `[← Real.log_pow]`. Apply `Real.log_le_log hKpos'` to reduce the goal to its premises. Establish `: (q + D).choose D ≤ (m + D) ^ D` using `(Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)`.

Conclude with `this` after adjusting the coercions. Use `set K := (q + D).choose D with hK`. Establish `hlogN : (δ * K : ℝ) * Real.log R ≤ Real.log (N m (Real.exp (t * m)))`. Establish `h1 : R ≤ ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ)`. Use `push_cast`.

Use `Nat.lt_floor_add_one R` as an intermediate fact. Use `Nat.cast_nonneg (α := ℝ) ⌊R⌋₊` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ((((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) ≤ N m (Real.exp (t * m))`. Conclude with `hb1` after adjusting the coercions.

Establish `h3 : (0 : ℝ) < (((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ) : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.cast_pow, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := Real.log_le_log h3 h2`. Establish `hlogR : t * m - B - D * Real.log ((m : ℝ) + D) ≤ Real.log R`. Rewrite using `[hR, Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_mul hCs.ne' hKpos'.ne']`. Combine the linear relations using `[hB s hse]`. Establish `key : (δ * K : ℝ) * (t * m - B - D * Real.log ((m : ℝ) + D)) ≤ Real.log (N m (Real.exp (t * m)))` using `(mul_le_mul_of_nonneg_left hlogR (by positivity)).trans hlogN`.

Rewrite using `[le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hupE : ∀ᶠ m : ℕ in atTop, Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤ ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D * ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e))` using `by filter_upwards [eventually_ge_atTop 1] with m hm`. Establish `hm0 : (0 : ℝ) < m` using `by exact_mod_cast hm`. Establish `he0 : (0 : ℝ) < e` using `by exact_mod_cast he`.

Use `set s := m % e with hs_def`. Establish `hse : s < e` using `Nat.mod_lt _ he`. Use `set q := m / e with hq`. Establish `hmq : e * q + s = m` using `Nat.div_add_mod m e`. Establish `hCs` using `hC' s`.

Use `set Y : ℝ := C' s * Real.exp (t * m) / κ ^ (q + c' s) with hY`. Establish `hYpos : 0 < Y` using `by rw [hY]; positivity`. Establish `hb2` using `(hb s hse q (Real.exp (t * m)) (Real.exp_pos _).le).2`. Rewrite `hb2` using `[hmq, ← hY]`. Use `set K := (q + c' s + D).choose D with hK`.

Establish `hlogN : Real.log (N m (Real.exp (t * m))) ≤ (δ * K : ℝ) * (Real.log 3 + |Real.log Y|)`. Establish `h0 : 0 ≤ Real.log 3 + |Real.log Y|`. Use `Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); positivity` as an intermediate fact. Break down `Nat.eq_zero_or_pos (N m (Real.exp (t * m))) with hN | hN` into its components or cases. Rewrite using `[hN, Nat.cast_zero, Real.log_zero]`.

Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Nat.cast_pow, Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := mul_le_mul_of_nonneg_left (hsGrowth_log_floor_le hYpos) (by positivity)`. Establish `hlogY : |Real.log Y| ≤ B' + t * m + (m / e + P) * (-Real.log κ)`. Rewrite using `[hY, Real.log_div (by positivity) (by positivity), Real.log_mul hCs.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]`. Establish `hq1 : ((q : ℕ) : ℝ) ≤ (m : ℝ) / e` using `Nat.cast_div_le`. Establish `hc1` using `hP s hse`.

Establish `hx : ((q : ℝ) + c' s) * (-Real.log κ) ≤ ((m : ℝ) / e + P) * (-Real.log κ)` using `mul_le_mul_of_nonneg_right (by linarith) (by linarith)`. Establish `hx0 : 0 ≤ ((q : ℝ) + c' s) * (-Real.log κ)` using `mul_nonneg (by positivity) (by linarith)`. Establish `ha` using `abs_le.mp (hB' s hse)`. Establish `htm : 0 ≤ t * m` using `by positivity`. Apply the tactic sequence `rw [abs_le]; push_cast; constructor <;> nlinarith`.

Rewrite using `[div_le_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Establish `hLlow : Tendsto (fun m : ℕ => ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D * (t - (B / m + D * (Real.log ((m : ℝ) + D) / m)))) atTop (𝓝 (L * t))`. Establish `h0 : Tendsto (fun m : ℕ => B / (m : ℝ) + D * (Real.log ((m : ℝ) + D) / m)) atTop (𝓝 0)`. Use `(tendsto_const_div_atTop_nhds_zero_nat B).add ((hsGrowth_log_add_div_tendsto D).const_mul (D : ℝ))` as an intermediate fact.

Simplify `this` using `only [mul_zero, add_zero]`. Use `hlow.mul ((tendsto_const_nhds (x := t)).sub h0)` as an intermediate fact. Simplify `this` using `only [sub_zero]`. Establish `hLup : Tendsto (fun m : ℕ => ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D * ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e))) atTop (𝓝 (L * (t - Real.log κ / e)))`. Use `hup.mul ((tendsto_const_div_atTop_nhds_zero_nat (Real.log 3 + B' + P * (-Real.log κ))).add (tendsto_const_nhds (x := t - Real.log κ / e)))` as an intermediate fact.

Simplify `this` using `only [zero_add]`. Establish `e1` using `hLlow.eventually (lt_mem_nhds (show L * t - ε < L * t by linarith))`. Establish `e2` using `hLup.eventually (gt_mem_nhds (show L * (t - Real.log κ / e) < L * (t - Real.log κ / e) + ε by linarith))`. Use `filter_upwards [e1, e2, hlowE, hupE] with m h1 h2 h3 h4`. Conclude with `⟨by linarith, by linarith⟩`.
-/
theorem hsGrowth_exp_radius : ∀ (D e δ : ℕ) (N : ℕ → ℝ → ℕ) (κ t : ℝ), 0 < e → 0 < κ → κ ≤ 1 → 0 < t → (∀ m, ∀ R R' : ℝ, 0 ≤ R → R ≤ R' → N m R ≤ N m R') → (∀ s : ℕ, s < e → ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ ∀ (q : ℕ) (R : ℝ), 0 ≤ R → (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧ N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, δ / ((e : ℝ) ^ D * D.factorial) * t - ε ≤ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ∧ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤ δ / ((e : ℝ) ^ D * D.factorial) * (t - Real.log κ / e) + ε := by
  intro D e δ N κ t he hκ hκ1 ht hmono h ε hε
  have h' : ∀ s : ℕ, ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ (s < e → ∀ (q : ℕ) (R : ℝ), 0 ≤ R →
      (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧
      N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) := by
    intro s
    by_cases hs : s < e
    · obtain ⟨c, c', C, C', h1, h2, h3⟩ := h s hs
      exact ⟨c, c', C, C', h1, h2, fun _ => h3⟩
    · exact ⟨0, 0, 1, 1, one_pos, one_pos, fun h => absurd h hs⟩
  choose c c' C C' hC hC' hb using h'
  set L : ℝ := δ / ((e : ℝ) ^ D * D.factorial) with hL
  have hdiv : ∀ q s, s < e → (e * q + s) / e = q ∧ (e * q + s) % e = s := by
    intro q s hs
    constructor
    · rw [add_comm, Nat.add_mul_div_left _ _ he, Nat.div_eq_of_lt hs, zero_add]
    · rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  have hlow : Tendsto (fun m : ℕ => ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D)
      atTop (𝓝 L) := by
    refine GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e δ (fun m => δ * (m / e - c (m % e) + D).choose D) he ?_
    intro s hs
    refine ⟨c s, 0, fun q => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hdiv (q + c s) s hs
      simp only [h1, h2, Nat.add_sub_cancel, le_refl]
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [h1, h2, add_zero]
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))
  have hup : Tendsto (fun m : ℕ => ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D)
      atTop (𝓝 L) := by
    refine GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e δ (fun m => δ * (m / e + c' (m % e) + D).choose D) he ?_
    intro s hs
    refine ⟨0, c' s, fun q => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [add_zero, h1, h2]
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [h1, h2, le_refl]
  set B : ℝ := ∑ s ∈ Finset.range e, |Real.log (C s)| with hBdef
  set B' : ℝ := ∑ s ∈ Finset.range e, |Real.log (C' s)| with hB'def
  set P : ℝ := ∑ s ∈ Finset.range e, (c' s : ℝ) with hPdef
  set M : ℕ := ∑ s ∈ Finset.range e, c s with hMdef
  have hB : ∀ s, s < e → Real.log (C s) ≤ B := fun s hs => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun s => |Real.log (C s)|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.mpr hs))
  have hB' : ∀ s, s < e → |Real.log (C' s)| ≤ B' := fun s hs =>
    Finset.single_le_sum (f := fun s => |Real.log (C' s)|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.mpr hs)
  have hP : ∀ s, s < e → (c' s : ℝ) ≤ P := fun s hs =>
    Finset.single_le_sum (f := fun s => (c' s : ℝ)) (fun i _ => Nat.cast_nonneg _)
      (Finset.mem_range.mpr hs)
  have hlk : Real.log κ ≤ 0 := Real.log_nonpos hκ.le hκ1

  have hlowE : ∀ᶠ m : ℕ in atTop,
      ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
        (t - (B / m + D * (Real.log ((m : ℝ) + D) / m))) ≤
      Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop (e * M + 1)] with m hm
    have hm0' : 0 < m := Nat.lt_of_lt_of_le (Nat.succ_pos _) hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm0'
    set s := m % e with hs_def
    have hse : s < e := Nat.mod_lt _ he
    have hcm : c s ≤ m / e := by
      have : M ≤ m / e := by
        rw [Nat.le_div_iff_mul_le he]
        rw [mul_comm]; linarith
      exact (Finset.single_le_sum (f := c) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr hse)).trans this
    set q := m / e - c s with hq
    have hqm : q ≤ m := (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
    have hmq : e * (q + c s) + s = m := by
      rw [hq, Nat.sub_add_cancel hcm]; exact Nat.div_add_mod m e
    have hKpos : 0 < (q + D).choose D := Nat.choose_pos (by omega)
    have hKpos' : (0 : ℝ) < ((q + D).choose D : ℝ) := by exact_mod_cast hKpos
    have hCs := hC s
    set R : ℝ := Real.exp (t * m) / (C s * ((q + D).choose D : ℝ)) with hR
    have hRpos : 0 < R := by rw [hR]; positivity
    have hCKR : C s * ((q + D).choose D : ℝ) * R = Real.exp (t * m) := by
      rw [hR]; field_simp
    have hb1 := (hb s hse q R hRpos.le).1
    rw [hmq, hCKR] at hb1
    have hK1 : Real.log ((q + D).choose D : ℝ) ≤ D * Real.log ((m : ℝ) + D) := by
      rw [← Real.log_pow]
      apply Real.log_le_log hKpos'
      have : (q + D).choose D ≤ (m + D) ^ D :=
        (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
      exact_mod_cast this
    set K := (q + D).choose D with hK
    have hlogN : (δ * K : ℝ) * Real.log R ≤ Real.log (N m (Real.exp (t * m))) := by
      have h1 : R ≤ ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        have := Nat.lt_floor_add_one R
        have := Nat.cast_nonneg (α := ℝ) ⌊R⌋₊
        linarith
      have h2 : ((((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) ≤ N m (Real.exp (t * m)) := by
        exact_mod_cast hb1
      have h3 : (0 : ℝ) < (((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ) : ℝ) := by positivity
      calc (δ * K : ℝ) * Real.log R ≤ (δ * K : ℝ) * Real.log ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.log_le_log hRpos h1) (by positivity)
        _ = Real.log ((((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) := by
            rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
        _ ≤ _ := Real.log_le_log h3 h2
    have hlogR : t * m - B - D * Real.log ((m : ℝ) + D) ≤ Real.log R := by
      rw [hR, Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp,
        Real.log_mul hCs.ne' hKpos'.ne']
      linarith [hB s hse]
    have key : (δ * K : ℝ) * (t * m - B - D * Real.log ((m : ℝ) + D)) ≤
        Real.log (N m (Real.exp (t * m))) :=
      (mul_le_mul_of_nonneg_left hlogR (by positivity)).trans hlogN
    rw [le_div_iff₀ (by positivity)]
    calc ((δ * K : ℕ) : ℝ) / (m : ℝ) ^ D * (t - (B / m + D * (Real.log ((m : ℝ) + D) / m))) *
          (m : ℝ) ^ (D + 1) = (δ * K : ℝ) * (t * m - B - D * Real.log ((m : ℝ) + D)) := by
          push_cast; field_simp; ring
      _ ≤ _ := key

  have hupE : ∀ᶠ m : ℕ in atTop, Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤
      ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
        ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    set s := m % e with hs_def
    have hse : s < e := Nat.mod_lt _ he
    set q := m / e with hq
    have hmq : e * q + s = m := Nat.div_add_mod m e
    have hCs := hC' s
    set Y : ℝ := C' s * Real.exp (t * m) / κ ^ (q + c' s) with hY
    have hYpos : 0 < Y := by rw [hY]; positivity
    have hb2 := (hb s hse q (Real.exp (t * m)) (Real.exp_pos _).le).2
    rw [hmq, ← hY] at hb2
    set K := (q + c' s + D).choose D with hK
    have hlogN : Real.log (N m (Real.exp (t * m))) ≤ (δ * K : ℝ) * (Real.log 3 + |Real.log Y|) := by
      have h0 : 0 ≤ Real.log 3 + |Real.log Y| := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); positivity
      rcases Nat.eq_zero_or_pos (N m (Real.exp (t * m))) with hN | hN
      · rw [hN, Nat.cast_zero, Real.log_zero]; positivity
      · calc Real.log (N m (Real.exp (t * m)))
            ≤ Real.log ((((2 * ⌊Y⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) :=
              Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast hb2)
          _ = (δ * K : ℝ) * Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) := by
              rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hsGrowth_log_floor_le hYpos) (by positivity)
    have hlogY : |Real.log Y| ≤ B' + t * m + (m / e + P) * (-Real.log κ) := by
      rw [hY, Real.log_div (by positivity) (by positivity),
        Real.log_mul hCs.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]
      have hq1 : ((q : ℕ) : ℝ) ≤ (m : ℝ) / e := Nat.cast_div_le
      have hc1 := hP s hse
      have hx : ((q : ℝ) + c' s) * (-Real.log κ) ≤ ((m : ℝ) / e + P) * (-Real.log κ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have hx0 : 0 ≤ ((q : ℝ) + c' s) * (-Real.log κ) := mul_nonneg (by positivity) (by linarith)
      have ha := abs_le.mp (hB' s hse)
      have htm : 0 ≤ t * m := by positivity
      rw [abs_le]; push_cast; constructor <;> nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc Real.log (N m (Real.exp (t * m))) ≤ (δ * K : ℝ) * (Real.log 3 + |Real.log Y|) := hlogN
      _ ≤ (δ * K : ℝ) * (Real.log 3 + (B' + t * m + (m / e + P) * (-Real.log κ))) := by
          gcongr
      _ = ((δ * K : ℕ) : ℝ) / (m : ℝ) ^ D *
            ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e)) * (m : ℝ) ^ (D + 1) := by
          push_cast; field_simp; ring

  have hLlow : Tendsto (fun m : ℕ => ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
      (t - (B / m + D * (Real.log ((m : ℝ) + D) / m)))) atTop (𝓝 (L * t)) := by
    have h0 : Tendsto (fun m : ℕ => B / (m : ℝ) + D * (Real.log ((m : ℝ) + D) / m)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat B).add
        ((hsGrowth_log_add_div_tendsto D).const_mul (D : ℝ))
      simpa only [mul_zero, add_zero] using this
    have := hlow.mul ((tendsto_const_nhds (x := t)).sub h0)
    simpa only [sub_zero] using this
  have hLup : Tendsto (fun m : ℕ => ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
      ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e))) atTop
      (𝓝 (L * (t - Real.log κ / e))) := by
    have := hup.mul ((tendsto_const_div_atTop_nhds_zero_nat (Real.log 3 + B' + P * (-Real.log κ))).add
      (tendsto_const_nhds (x := t - Real.log κ / e)))
    simpa only [zero_add] using this
  have e1 := hLlow.eventually (lt_mem_nhds (show L * t - ε < L * t by linarith))
  have e2 := hLup.eventually (gt_mem_nhds
    (show L * (t - Real.log κ / e) < L * (t - Real.log κ / e) + ε by linarith))
  filter_upwards [e1, e2, hlowE, hupE] with m h1 h2 h3 h4
  exact ⟨by linarith, by linarith⟩

end GlobalTheory
