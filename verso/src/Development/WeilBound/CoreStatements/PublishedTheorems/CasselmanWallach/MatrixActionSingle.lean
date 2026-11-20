import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace SecondMomentAlgebra

/- English proof (translation)
Establish `hA : 0 < (2 * (n:ℝ)) ^ m` using `by positivity`. Establish `hs0 : 0 < s` using `by linarith`. Take `⟨k, rfl⟩ : ∃ k, m = k + 1` from `⟨m - 1, by omega⟩`. Establish `e1 : 2 * (k + 1) - 1 = 2 * k + 1` using `by omega`. Establish `e2 : 2 * (k + 1) - 2 = 2 * k` using `by omega`.

Rewrite `h` using `[e1, e2, div_pow, ← pow_mul]`. Use `set A := (2 * (n:ℝ)) ^ (k + 1) with hAdef`. Establish `hP : 0 < s ^ (2 * k)` using `by positivity`. Establish `f1 : s ^ (2 * (k + 1)) = s ^ (2 * k) * s ^ 2` using `by ring`. Establish `f2 : s ^ (2 * k + 1) = s ^ (2 * k) * s` using `by ring`.

Rewrite `h` using `[f1, f2, div_le_iff₀ hA]`. Establish `h' : s ^ (2 * k) * s ^ 2 ≤ s ^ (2 * k) * (A * C1 * s + A * C2 * T)`. Combine the equalities or inequalities in the displayed calculation. Establish `h'' : s ^ 2 ≤ A * C1 * s + A * C2 * T` using `le_of_mul_le_mul_left h' hP`. Establish `h2 : 2 * (A * C1 * s) ≤ s ^ 2`.

Use `mul_le_mul_of_nonneg_right hs2 hs0.le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma alg (n m : ℕ) (C1 C2 s T : ℝ) (hn : (1:ℝ) ≤ n) (hm : 1 ≤ m) (hC2 : 0 < C2) (hs : 1 ≤ s)
    (hs2 : 2 * C1 * (2 * (n:ℝ)) ^ m ≤ s)
    (h : (s ^ 2 / (2 * n)) ^ m ≤ C1 * s ^ (2 * m - 1) + C2 * s ^ (2 * m - 2) * T) :
    1 / (2 * (2 * (n:ℝ)) ^ m * C2) * s ^ 2 ≤ T := by
  have hA : 0 < (2 * (n:ℝ)) ^ m := by positivity
  have hs0 : 0 < s := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) - 2 = 2 * k := by omega
  rw [e1, e2, div_pow, ← pow_mul] at h
  set A := (2 * (n:ℝ)) ^ (k + 1) with hAdef
  have hP : 0 < s ^ (2 * k) := by positivity
  have f1 : s ^ (2 * (k + 1)) = s ^ (2 * k) * s ^ 2 := by ring
  have f2 : s ^ (2 * k + 1) = s ^ (2 * k) * s := by ring
  rw [f1, f2, div_le_iff₀ hA] at h
  have h' : s ^ (2 * k) * s ^ 2 ≤ s ^ (2 * k) * (A * C1 * s + A * C2 * T) := by
    calc s ^ (2 * k) * s ^ 2 ≤ (C1 * (s ^ (2 * k) * s) + C2 * s ^ (2 * k) * T) * A := h
      _ = s ^ (2 * k) * (A * C1 * s + A * C2 * T) := by ring
  have h'' : s ^ 2 ≤ A * C1 * s + A * C2 * T := le_of_mul_le_mul_left h' hP
  have h2 : 2 * (A * C1 * s) ≤ s ^ 2 := by
    have := mul_le_mul_of_nonneg_right hs2 hs0.le
    nlinarith
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- English proof (translation)
Rewrite using `[inner_smul_right, inner_self_eq_norm_sq_to_K]`. Simplify using `[Complex.mul_re, pow_two]`.
-/
lemma reEig (v : V) (μ : ℝ) : (inner ℂ v ((μ:ℂ) • v)).re = μ * ‖v‖ ^ 2 := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, pow_two]

/- English proof (translation)
Establish `h` using `sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n × Fin n))) (f := fun p => f p.1 p.2)`. Simplify `h` using `[Fintype.sum_prod_type', Fintype.sum_prod_type, Finset.card_univ]`.
-/
lemma cs {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ c, ∑ d, f c d) ^ 2 ≤ ((n:ℝ) * n) * ∑ c, ∑ d, f c d ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n × Fin n))) (f := fun p => f p.1 p.2)
  simpa [Fintype.sum_prod_type', Fintype.sum_prod_type, Finset.card_univ] using h

/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type' (fun c d => ‖Z ε E c d w‖ ^ 2), nc, Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun p _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Both sides reduce to the same expression. Simplify using `[hZc _ _ (not_not.mp h)]`.
-/
lemma zsum {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hZc : ∀ a b, ε a = ε b → Z ε E a b = 0) (w : V) :
    ∑ c, ∑ d, ‖Z ε E c d w‖ ^ 2 = ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 w‖ ^ 2 := by
  rw [← Fintype.sum_prod_type' (fun c d => ‖Z ε E c d w‖ ^ 2), nc, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs with h
  · rfl
  · simp [hZc _ _ (not_not.mp h)]

/- English proof (translation)
Establish `h0 : ‖v‖ ≠ 0` using `norm_ne_zero_iff.mpr hv`. Simplify using `only [map_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm, mul_pow, ← Finset.mul_sum]`. Rewrite using `[← mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, one_mul]`.
-/
lemma scale {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (v : V) (hv : v ≠ 0) :
    ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v‖ ^ 2 =
      ‖v‖ ^ 2 * ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 (((‖v‖ : ℂ)⁻¹) • v)‖ ^ 2 := by
  have h0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp only [map_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm, mul_pow, ← Finset.mul_sum]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, one_mul]

end SecondMomentAlgebra

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `h0 h1 h1s h3c h5 h6 h8a n ε V _ _ E hM`. Take `⟨-, -, hZc, hcas⟩` from `h0 n ε V E hM`. Take `⟨κ, hκ⟩` from `h3c n ε V E hM`. Use `set m : ℕ := 2 ^ n with hm`. Establish `hm1 : 1 ≤ m` using `Nat.one_le_two_pow`.

Establish `hnm : n ≤ m` using `Nat.lt_two_pow_self.le`. Establish `h5'` using `h5 n ε V E hM m hm1 hnm`. Use `choose u hu w hw hdec using fun e : Fin n => h5' e e`. Establish `hadj : ∀ e c d, ∃ w' ∈ U E (2 * m - 2), ∀ x y : V, inner ℂ x (w e c d y) = inner ℂ (w' x) y` using `fun e c d => h1s n ε V E hM _ _ (hw e c d)`. Use `choose w' hw' hadj using hadj`.

Establish `bu : ∀ e, ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ) (v : V), 0 ≤ μ → Eig ε E μ v → ‖u e v‖ ≤ C * √(1 + μ) ^ (2 * m - 1) * ‖v‖` using `fun e => h6 n ε V E hM _ _ (hu e)`. Use `choose Cu hCu0 hCu using bu`. Establish `bw : ∀ e c d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ) (v : V), 0 ≤ μ → Eig ε E μ v → ‖w' e c d v‖ ≤ C * √(1 + μ) ^ (2 * m - 2) * ‖v‖` using `fun e c d => h6 n ε V E hM _ _ (hw' e c d)`. Use `choose Cw hCw0 hCw using bw`. Use `set C1 : ℝ := ∑ e, Cu e with hC1def`.

Use `set C2 : ℝ := ∑ e, ∑ c, ∑ d, Cw e c d + 1 with hC2def`. Establish `hC1e : ∀ e, Cu e ≤ C1` using `fun e => Finset.single_le_sum (f := Cu) (fun i _ => hCu0 i) (Finset.mem_univ e)`. Establish `hC2e : ∀ e c d, Cw e c d ≤ C2`. Introduce `e c d`. Establish `a1 : Cw e c d ≤ ∑ d', Cw e c d'` using `Finset.single_le_sum (f := fun d' => Cw e c d') (fun i _ => hCw0 e c i) (Finset.mem_univ d)`.

Establish `a2 : ∑ d', Cw e c d' ≤ ∑ c', ∑ d', Cw e c' d'` using `Finset.single_le_sum (f := fun c' => ∑ d', Cw e c' d') (fun i _ => Finset.sum_nonneg (fun j _ => hCw0 e i j)) (Finset.mem_univ c)`. Establish `a3 : ∑ c', ∑ d', Cw e c' d' ≤ ∑ e', ∑ c', ∑ d', Cw e' c' d'` using `Finset.single_le_sum (f := fun e' => ∑ c', ∑ d', Cw e' c' d') (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hCw0 i j k))) (Finset.mem_univ e)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC2 : 0 < C2`. Establish `: 0 ≤ ∑ e, ∑ c, ∑ d, Cw e c d` using `Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hCw0 i j k)))`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set N : ℝ := (2 * (n:ℝ)) ^ m with hNdef`. Use `⟨1 / ((2 * N * C2) ^ 2 * ((n:ℝ) * n + 1) + 1), max (max 1 (|κ| + 1)) ((2 * C1 * N) ^ 2), by positivity, ?_⟩` and prove the remaining obligations. Introduce `μ v hμ hv`. Establish `hμ1 : 1 ≤ μ` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hμ`.

Establish `hμκ : |κ| + 1 ≤ μ` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hμ`. Establish `hμC : (2 * C1 * N) ^ 2 ≤ μ` using `le_trans (le_max_right _ _) hμ`. Distinguish the cases in `hv0 : v = 0`. Substitute `hv0` using the available equality. Simplify using the standard rewrite rules.

Establish `hnv : 0 < ‖v‖` using `norm_pos_iff.mpr hv0`. Use `set v1 : V := ((‖v‖ : ℂ)⁻¹) • v with hv1def`. Establish `hv1n : ‖v1‖ = 1`. Rewrite using `[hv1def, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hnv.ne']`. Establish `hv1E : Eig ε E μ v1`.

Establish `hv' : casimirK ε E v = (μ : ℂ) • v` using `hv`. Use `show casimirK ε E (((‖v‖ : ℂ)⁻¹) • v) = (μ : ℂ) • (((‖v‖ : ℂ)⁻¹) • v)`. Rewrite using `[map_smul, hv', smul_comm]`. Rewrite using `[SecondMomentAlgebra.scale ε E v hv0]`. It suffices to establish `hS : 1 / ((2 * N * C2) ^ 2 * ((n:ℝ) * n + 1) + 1) * (1 + μ) ^ 2 ≤ ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v1‖ ^ 2 by`.

Use `mul_le_mul_of_nonneg_left hS (sq_nonneg ‖v‖)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX : ∑ a, ∑ b, ‖E a b v1‖ ^ 2 = 2 * μ - κ`. Rewrite using `[(hcas κ hκ v1).1, show casimirK ε E v1 = (μ : ℂ) • v1 from hv1E, SecondMomentAlgebra.reEig, hv1n]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hpos : 0 < 2 * μ - κ` using `by linarith [le_abs_self κ]`. Establish `hne : (Finset.univ : Finset (Fin n)).Nonempty`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[Finset.not_nonempty_iff_eq_empty]`. Rewrite `hX` using `[hne]`.

Simplify using `at hX`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨e0, -⟩` from `hne`. Establish `hn1 : (1:ℝ) ≤ n` using `by exact_mod_cast Nat.succ_le_of_lt (Fin.pos e0)`. Establish `hnr : (n:ℝ) ≠ 0` using `ne_of_gt (by linarith)`.

Establish `hN : 0 < N` using `by positivity`. Take `⟨e, -, he⟩` from `exists_le_of_sum_le (s := Finset.univ) ⟨e0, Finset.mem_univ _⟩ (f := fun _ => (2 * μ - κ) / n) (g := fun e => ∑ a, ‖E a e v1‖ ^ 2) (by`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `: (n:ℝ) * ((2 * μ - κ) / n) = 2 * μ - κ` using `by field_simp`. Rewrite using `[this, ← hX, Finset.sum_comm])`.

Establish `h8` using `h8a n ε V E hM v1 hv1n e n`. Rewrite `h8` using `[hdec e]`. Simplify using `only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, inner_add_right, inner_sum, Complex.add_re, Complex.re_sum] at h8`. Establish `hs : √(1 + μ) ^ 2 = 1 + μ` using `Real.sq_sqrt (by linarith)`. Establish `b1 : (inner ℂ v1 (u e v1)).re ≤ Cu e * √(1 + μ) ^ (2 * m - 1)`.

Establish `r` using `re_inner_le_norm (𝕜 := ℂ) v1 (u e v1)`. Establish `r2 : ‖u e v1‖ ≤ Cu e * √(1 + μ) ^ (2 * m - 1)`. Simplify `hCu e μ v1 (by linarith) hv1E` using `[hv1n]`. Rewrite `r` using `[hv1n, one_mul]`. Conclude with `le_trans r r2`.

Establish `b2 : ∀ c d, (inner ℂ v1 (w e c d (Z ε E c d v1))).re ≤ C2 * √(1 + μ) ^ (2 * m - 2) * ‖Z ε E c d v1‖`. Introduce `c d`. Rewrite using `[hadj e c d]`. Establish `r` using `re_inner_le_norm (𝕜 := ℂ) (w' e c d v1) (Z ε E c d v1)`. Establish `r2 : ‖w' e c d v1‖ ≤ C2 * √(1 + μ) ^ (2 * m - 2)`.

Use `hCw e c d μ v1 (by linarith) hv1E` as an intermediate fact. Rewrite `this` using `[hv1n, mul_one]`. Conclude with `le_trans this (mul_le_mul_of_nonneg_right (hC2e e c d) (by positivity))`. Conclude with `le_trans r (mul_le_mul_of_nonneg_right r2 (norm_nonneg _))`. Establish `hsum : ∑ c, ∑ d, ‖Z ε E c d v1‖ ≤ √((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2)` using `le_trans (le_abs_self _) (Real.abs_le_sqrt (SecondMomentAlgebra.cs (fun c d => ‖Z ε E c d v1‖)))`.

Use `set T := √((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) with hTdef`. Establish `hXe : √(1 + μ) ^ 2 / (2 * n) ≤ ∑ a, ‖E a e v1‖ ^ 2`. Rewrite using `[hs]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_div_iff₀ (by positivity) (by positivity)]`.

Use polynomial arithmetic with `[le_abs_self κ]`. Use `_ ≤ _ := he`. Establish `hmain : (√(1 + μ) ^ 2 / (2 * n)) ^ m ≤ C1 * √(1 + μ) ^ (2 * m - 1) + C2 * √(1 + μ) ^ (2 * m - 2) * T`. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[← Finset.mul_sum]`.

Conclude with `add_le_add (mul_le_mul_of_nonneg_right (hC1e e) (by positivity)) (mul_le_mul_of_nonneg_left hsum (by positivity))`. Establish `hs1 : 1 ≤ √(1 + μ)`. Use `Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + μ by linarith)` as an intermediate fact. Rewrite `this` using `[Real.sqrt_one]`. Then use the resulting hypothesis. Establish `hs2 : 2 * C1 * N ≤ √(1 + μ)`.

Use `le_trans (le_abs_self _) ?_` and prove the remaining obligations. Rewrite using `[← Real.sqrt_sq_eq_abs]`. Conclude with `Real.sqrt_le_sqrt (by linarith)`. Establish `key` using `SecondMomentAlgebra.alg n m C1 C2 (√(1 + μ)) T hn1 hm1 hC2 hs1 hs2 hmain`. Rewrite `key` using `[hs]`.

Establish `hS'0 : 0 ≤ ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2` using `by positivity`. Establish `hq : (1 / (2 * N * C2) * (1 + μ)) ^ 2 ≤ (n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2`. Use `pow_le_pow_left₀ (by positivity) key 2` as an intermediate fact. Rewrite `this` using `[hTdef, Real.sq_sqrt (by positivity)]`. Then use the resulting hypothesis. Establish `hq' : (1 + μ) ^ 2 ≤ (2 * N * C2) ^ 2 * ((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2)`.

Establish `e3 : (1 + μ) ^ 2 = (2 * N * C2) ^ 2 * (1 / (2 * N * C2) * (1 + μ)) ^ 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e3]`. Conclude with `mul_le_mul_of_nonneg_left hq (sq_nonneg _)`. Rewrite using `[← SecondMomentAlgebra.zsum ε E hZc v1]`.

Rewrite using `[div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]`. Use polynomial arithmetic with `[mul_nonneg hS'0 (sq_nonneg (2 * N * C2))]`.
-/
theorem second_moment_of_columns : A0 → A1 → FiltrationAdjointStable → CasimirIsRealScalar → A5 → A6 → ColumnOperatorMoments → A8 := by
  intro h0 h1 h1s h3c h5 h6 h8a n ε V _ _ E hM
  obtain ⟨-, -, hZc, hcas⟩ := h0 n ε V E hM
  obtain ⟨κ, hκ⟩ := h3c n ε V E hM
  set m : ℕ := 2 ^ n with hm
  have hm1 : 1 ≤ m := Nat.one_le_two_pow
  have hnm : n ≤ m := Nat.lt_two_pow_self.le
  have h5' := h5 n ε V E hM m hm1 hnm
  choose u hu w hw hdec using fun e : Fin n => h5' e e
  have hadj : ∀ e c d, ∃ w' ∈ U E (2 * m - 2), ∀ x y : V,
      inner ℂ x (w e c d y) = inner ℂ (w' x) y := fun e c d => h1s n ε V E hM _ _ (hw e c d)
  choose w' hw' hadj using hadj
  have bu : ∀ e, ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ) (v : V), 0 ≤ μ → Eig ε E μ v →
      ‖u e v‖ ≤ C * √(1 + μ) ^ (2 * m - 1) * ‖v‖ := fun e => h6 n ε V E hM _ _ (hu e)
  choose Cu hCu0 hCu using bu
  have bw : ∀ e c d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ) (v : V), 0 ≤ μ → Eig ε E μ v →
      ‖w' e c d v‖ ≤ C * √(1 + μ) ^ (2 * m - 2) * ‖v‖ := fun e c d => h6 n ε V E hM _ _ (hw' e c d)
  choose Cw hCw0 hCw using bw
  set C1 : ℝ := ∑ e, Cu e with hC1def
  set C2 : ℝ := ∑ e, ∑ c, ∑ d, Cw e c d + 1 with hC2def
  have hC1e : ∀ e, Cu e ≤ C1 := fun e =>
    Finset.single_le_sum (f := Cu) (fun i _ => hCu0 i) (Finset.mem_univ e)
  have hC2e : ∀ e c d, Cw e c d ≤ C2 := by
    intro e c d
    have a1 : Cw e c d ≤ ∑ d', Cw e c d' :=
      Finset.single_le_sum (f := fun d' => Cw e c d') (fun i _ => hCw0 e c i) (Finset.mem_univ d)
    have a2 : ∑ d', Cw e c d' ≤ ∑ c', ∑ d', Cw e c' d' :=
      Finset.single_le_sum (f := fun c' => ∑ d', Cw e c' d')
        (fun i _ => Finset.sum_nonneg (fun j _ => hCw0 e i j)) (Finset.mem_univ c)
    have a3 : ∑ c', ∑ d', Cw e c' d' ≤ ∑ e', ∑ c', ∑ d', Cw e' c' d' :=
      Finset.single_le_sum (f := fun e' => ∑ c', ∑ d', Cw e' c' d')
        (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hCw0 i j k)))
        (Finset.mem_univ e)
    linarith
  have hC2 : 0 < C2 := by
    have : 0 ≤ ∑ e, ∑ c, ∑ d, Cw e c d :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hCw0 i j k)))
    linarith
  set N : ℝ := (2 * (n:ℝ)) ^ m with hNdef
  refine ⟨1 / ((2 * N * C2) ^ 2 * ((n:ℝ) * n + 1) + 1), max (max 1 (|κ| + 1)) ((2 * C1 * N) ^ 2),
    by positivity, ?_⟩
  intro μ v hμ hv
  have hμ1 : 1 ≤ μ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hμ
  have hμκ : |κ| + 1 ≤ μ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hμ
  have hμC : (2 * C1 * N) ^ 2 ≤ μ := le_trans (le_max_right _ _) hμ
  by_cases hv0 : v = 0
  · subst hv0
    simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set v1 : V := ((‖v‖ : ℂ)⁻¹) • v with hv1def
  have hv1n : ‖v1‖ = 1 := by
    rw [hv1def, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hnv.ne']
  have hv1E : Eig ε E μ v1 := by
    have hv' : casimirK ε E v = (μ : ℂ) • v := hv
    show casimirK ε E (((‖v‖ : ℂ)⁻¹) • v) = (μ : ℂ) • (((‖v‖ : ℂ)⁻¹) • v)
    rw [map_smul, hv', smul_comm]
  rw [SecondMomentAlgebra.scale ε E v hv0]
  suffices hS : 1 / ((2 * N * C2) ^ 2 * ((n:ℝ) * n + 1) + 1) * (1 + μ) ^ 2 ≤
      ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v1‖ ^ 2 by
    have := mul_le_mul_of_nonneg_left hS (sq_nonneg ‖v‖)
    linarith
  have hX : ∑ a, ∑ b, ‖E a b v1‖ ^ 2 = 2 * μ - κ := by
    rw [(hcas κ hκ v1).1, show casimirK ε E v1 = (μ : ℂ) • v1 from hv1E, SecondMomentAlgebra.reEig, hv1n]
    ring
  have hpos : 0 < 2 * μ - κ := by linarith [le_abs_self κ]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hX
    simp at hX
    linarith
  obtain ⟨e0, -⟩ := hne
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt (Fin.pos e0)
  have hnr : (n:ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hN : 0 < N := by positivity
  obtain ⟨e, -, he⟩ := exists_le_of_sum_le (s := Finset.univ) ⟨e0, Finset.mem_univ _⟩
    (f := fun _ => (2 * μ - κ) / n) (g := fun e => ∑ a, ‖E a e v1‖ ^ 2) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : (n:ℝ) * ((2 * μ - κ) / n) = 2 * μ - κ := by field_simp
      rw [this, ← hX, Finset.sum_comm])
  have h8 := h8a n ε V E hM v1 hv1n e n
  rw [hdec e] at h8
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, inner_add_right, inner_sum,
    Complex.add_re, Complex.re_sum] at h8
  have hs : √(1 + μ) ^ 2 = 1 + μ := Real.sq_sqrt (by linarith)
  have b1 : (inner ℂ v1 (u e v1)).re ≤ Cu e * √(1 + μ) ^ (2 * m - 1) := by
    have r := re_inner_le_norm (𝕜 := ℂ) v1 (u e v1)
    have r2 : ‖u e v1‖ ≤ Cu e * √(1 + μ) ^ (2 * m - 1) := by
      simpa [hv1n] using hCu e μ v1 (by linarith) hv1E
    rw [hv1n, one_mul] at r
    exact le_trans r r2
  have b2 : ∀ c d, (inner ℂ v1 (w e c d (Z ε E c d v1))).re ≤
      C2 * √(1 + μ) ^ (2 * m - 2) * ‖Z ε E c d v1‖ := by
    intro c d
    rw [hadj e c d]
    have r := re_inner_le_norm (𝕜 := ℂ) (w' e c d v1) (Z ε E c d v1)
    have r2 : ‖w' e c d v1‖ ≤ C2 * √(1 + μ) ^ (2 * m - 2) := by
      have := hCw e c d μ v1 (by linarith) hv1E
      rw [hv1n, mul_one] at this
      exact le_trans this (mul_le_mul_of_nonneg_right (hC2e e c d) (by positivity))
    exact le_trans r (mul_le_mul_of_nonneg_right r2 (norm_nonneg _))
  have hsum : ∑ c, ∑ d, ‖Z ε E c d v1‖ ≤ √((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) :=
    le_trans (le_abs_self _) (Real.abs_le_sqrt (SecondMomentAlgebra.cs (fun c d => ‖Z ε E c d v1‖)))
  set T := √((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) with hTdef
  have hXe : √(1 + μ) ^ 2 / (2 * n) ≤ ∑ a, ‖E a e v1‖ ^ 2 := by
    rw [hs]
    calc (1 + μ) / (2 * n) ≤ (2 * μ - κ) / n := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [le_abs_self κ]
      _ ≤ _ := he
  have hmain : (√(1 + μ) ^ 2 / (2 * n)) ^ m ≤
      C1 * √(1 + μ) ^ (2 * m - 1) + C2 * √(1 + μ) ^ (2 * m - 2) * T := by
    calc (√(1 + μ) ^ 2 / (2 * n)) ^ m ≤ (∑ a, ‖E a e v1‖ ^ 2) ^ m :=
          pow_le_pow_left₀ (by positivity) hXe m
      _ ≤ _ := h8
      _ ≤ Cu e * √(1 + μ) ^ (2 * m - 1) + ∑ c, ∑ d, C2 * √(1 + μ) ^ (2 * m - 2) * ‖Z ε E c d v1‖ :=
          add_le_add b1 (Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => b2 c d)
      _ ≤ _ := by
          simp_rw [← Finset.mul_sum]
          exact add_le_add (mul_le_mul_of_nonneg_right (hC1e e) (by positivity))
            (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hs1 : 1 ≤ √(1 + μ) := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + μ by linarith)
    rwa [Real.sqrt_one] at this
  have hs2 : 2 * C1 * N ≤ √(1 + μ) := by
    refine le_trans (le_abs_self _) ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have key := SecondMomentAlgebra.alg n m C1 C2 (√(1 + μ)) T hn1 hm1 hC2 hs1 hs2 hmain
  rw [hs] at key
  have hS'0 : 0 ≤ ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2 := by positivity
  have hq : (1 / (2 * N * C2) * (1 + μ)) ^ 2 ≤ (n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) key 2
    rwa [hTdef, Real.sq_sqrt (by positivity)] at this
  have hq' : (1 + μ) ^ 2 ≤ (2 * N * C2) ^ 2 * ((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) := by
    have e3 : (1 + μ) ^ 2 = (2 * N * C2) ^ 2 * (1 / (2 * N * C2) * (1 + μ)) ^ 2 := by
      field_simp
    rw [e3]
    exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)
  rw [← SecondMomentAlgebra.zsum ε E hZc v1]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hS'0 (sq_nonneg (2 * N * C2))]

end PositivityTheory.CW

end
