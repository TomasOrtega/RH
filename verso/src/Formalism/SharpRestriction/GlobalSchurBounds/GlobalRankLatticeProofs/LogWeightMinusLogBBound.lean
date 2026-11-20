import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaFiveOneOfTheoremTwo

noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

/- English proof (translation)
Unfold `DataB at hB`. Take `⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩` from `hB`. Establish `hL` using `scale_one_le_L sc`. Establish `hkpos : (0 : ℝ) < D.R.k`. Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : 1 ≤ D.R.m)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Establish `: 0 < D.R.k` using `by exact_mod_cast hkpos`. Conclude with `Nat.one_le_of_lt this` after adjusting the coercions. Establish `hx` using `sc.one_lt_alt`.

Establish `hpos : ∀ i, i < D.R.m → 1 ≤ bN D ρ i`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_`.

Establish `h0` using `(hb0 ρ).1`. Establish `h4 : 1 ≤ bN D ρ 0 / sc.x` using `le_trans (by nlinarith) h0`. Establish `h5` using `(le_div_iff₀ (by linarith)).mp h4`. Use the polynomial consequences of the given equalities and inequalities. Consider the case `succ i ih`.

Introduce `hi`. Establish `h1` using `ih (by omega)`. Establish `h2` using `(hw ρ i (by omega)).2.1`. Establish `h3` using `hinc ρ i hi`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `hpos j hj`.
-/
theorem b_ge_one_section_B (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : 1 ≤ bN D ρ j := by
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  have hL := scale_one_le_L sc
  have hkpos : (0 : ℝ) < D.R.k := by
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    nlinarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 0 < D.R.k := by exact_mod_cast hkpos
    exact_mod_cast Nat.one_le_of_lt this
  have hx := sc.one_lt_alt
  have hpos : ∀ i, i < D.R.m → 1 ≤ bN D ρ i := by
    intro i
    induction i with
    | zero =>
      intro _
      have h0 := (hb0 ρ).1
      have h4 : 1 ≤ bN D ρ 0 / sc.x := le_trans (by nlinarith) h0
      have h5 := (le_div_iff₀ (by linarith)).mp h4
      nlinarith
    | succ i ih =>
      intro hi
      have h1 := ih (by omega)
      have h2 := (hw ρ i (by omega)).2.1
      have h3 := hinc ρ i hi
      linarith
  exact hpos j hj

/- English proof (translation)
Unfold `DataB at hB`. Take `⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩` from `hB`. Establish `hstep : ∀ i, i + 1 < D.R.m → w i ρ ≤ w (i + 1) ρ` using `fun i hi => le_of_lt (lt_trans (hinc ρ i hi) (hw ρ (i + 1) hi).2.1)`. Establish `hmono : ∀ d, ∀ i, i + d = D.R.m - 1 → w i ρ ≤ w (D.R.m - 1) ρ`. Introduce `d`.

Proceed by induction on `d with`. Consider the case `zero`. Introduce `i hi`. Establish `h : i = D.R.m - 1` using `by omega`. Simplify using `only [h, le_refl]`.

Consider the case `succ d ih`. Introduce `i hi`. Conclude with `le_trans (hstep i (by omega)) (ih (i + 1) (by omega))`. Conclude with `le_trans (hmono (D.R.m - 1 - j) j (by omega)) (hb0 ρ).2`.
-/
theorem weights_le_two_b (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) : w j ρ ≤ 2 * sc.b := by
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  have hstep : ∀ i, i + 1 < D.R.m → w i ρ ≤ w (i + 1) ρ := fun i hi =>
    le_of_lt (lt_trans (hinc ρ i hi) (hw ρ (i + 1) hi).2.1)
  have hmono : ∀ d, ∀ i, i + d = D.R.m - 1 → w i ρ ≤ w (D.R.m - 1) ρ := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have h : i = D.R.m - 1 := by omega
      simp only [h, le_refl]
    | succ d ih =>
      intro i hi
      exact le_trans (hstep i (by omega)) (ih (i + 1) (by omega))
  exact le_trans (hmono (D.R.m - 1 - j) j (by omega)) (hb0 ρ).2

/- English proof (translation)
Establish `hb1` using `b_ge_one_section_B D sc C0 Δ w hB ρ j hj`. Establish `hwl` using `weights_le_two_b D sc C0 Δ w hB ρ j hj`. Unfold `DataB at hB`. Take `⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩` from `hB`. Take `⟨hw0, hbw, habs⟩` from `hw ρ j hj`.

Establish `hL` using `scale_one_le_L sc`. Establish `hx` using `sc.one_lt_alt`. Establish `hkpos : (0 : ℝ) < D.R.k`. Establish `hm : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : 1 ≤ D.R.m)`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Establish `: 0 < D.R.k` using `by exact_mod_cast hkpos`. Conclude with `Nat.one_le_of_lt this` after adjusting the coercions. Establish `hBpos : 0 < bN D ρ j` using `by linarith`. Establish `hratio : Real.log (w j ρ) - Real.log (bN D ρ j) ≤ 1 / sc.x`.

Rewrite using `[← Real.log_div hw0.ne' hBpos.ne']`. Establish `h1` using `Real.log_le_sub_one_of_pos (div_pos hw0 hBpos)`. Establish `h2 : w j ρ / bN D ρ j - 1 ≤ 1 / sc.x`. Rewrite using `[div_sub_one hBpos.ne', div_le_div_iff₀ hBpos (by linarith)]`. Establish `h4` using `(abs_le.mp habs).2`.

Establish `h3 : (w j ρ - bN D ρ j) * sc.x ≤ bN D ρ j` using `by rwa [le_div_iff₀ (by linarith)] at h4`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlogW : Real.log (w j ρ) ≤ 2 * sc.L`. Establish `h1 : Real.log (w j ρ) ≤ Real.log (2 * sc.b)` using `Real.log_le_log hw0 hwl`.

Establish `h2 : Real.log (2 * sc.b) = Real.log 2 + sc.L`. Unfold `Scale.b`. Rewrite using `[Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]`. Establish `h3 : Real.log 2 < 1`. Use `Real.log_two_lt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx1 : 0 < 1 / sc.x` using `one_div_pos.mpr (by linarith)`. Establish `hkx : ((D.R.k : ℝ) - 1) * (1 / sc.x) ≤ (D.R.k : ℝ) / sc.x`. Establish `e : ((D.R.k : ℝ) - 1) * (1 / sc.x) = (D.R.k : ℝ) / sc.x - 1 / sc.x` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmul : ((D.R.k : ℝ) - 1) * (Real.log (w j ρ) - Real.log (bN D ρ j)) ≤ ((D.R.k : ℝ) - 1) * (1 / sc.x)` using `mul_le_mul_of_nonneg_left hratio (by linarith)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_weight_minus_log_b_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (ρ : D.what₂.Tau) (j : ℕ) (hj : j < D.R.m) :
    (D.R.k : ℝ) * Real.log (w j ρ) - ((D.R.k : ℝ) - 1) * Real.log (bN D ρ j) ≤ (D.R.k : ℝ) / sc.x + 2 * sc.L := by
  have hb1 := b_ge_one_section_B D sc C0 Δ w hB ρ j hj
  have hwl := weights_le_two_b D sc C0 Δ w hB ρ j hj
  unfold DataB at hB
  obtain ⟨hpi, hlogv, hf, hmk, hk, hg, hΔ, hv1, hv2, hu1, hu2, hu3, hw, hinc, hb0, hgap⟩ := hB
  obtain ⟨hw0, hbw, habs⟩ := hw ρ j hj
  have hL := scale_one_le_L sc
  have hx := sc.one_lt_alt
  have hkpos : (0 : ℝ) < D.R.k := by
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    nlinarith
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 0 < D.R.k := by exact_mod_cast hkpos
    exact_mod_cast Nat.one_le_of_lt this
  have hBpos : 0 < bN D ρ j := by linarith
  have hratio : Real.log (w j ρ) - Real.log (bN D ρ j) ≤ 1 / sc.x := by
    rw [← Real.log_div hw0.ne' hBpos.ne']
    have h1 := Real.log_le_sub_one_of_pos (div_pos hw0 hBpos)
    have h2 : w j ρ / bN D ρ j - 1 ≤ 1 / sc.x := by
      rw [div_sub_one hBpos.ne', div_le_div_iff₀ hBpos (by linarith)]
      have h4 := (abs_le.mp habs).2
      have h3 : (w j ρ - bN D ρ j) * sc.x ≤ bN D ρ j := by rwa [le_div_iff₀ (by linarith)] at h4
      linarith
    linarith
  have hlogW : Real.log (w j ρ) ≤ 2 * sc.L := by
    have h1 : Real.log (w j ρ) ≤ Real.log (2 * sc.b) := Real.log_le_log hw0 hwl
    have h2 : Real.log (2 * sc.b) = Real.log 2 + sc.L := by
      unfold Scale.b
      rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]
    have h3 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hx1 : 0 < 1 / sc.x := one_div_pos.mpr (by linarith)
  have hkx : ((D.R.k : ℝ) - 1) * (1 / sc.x) ≤ (D.R.k : ℝ) / sc.x := by
    have e : ((D.R.k : ℝ) - 1) * (1 / sc.x) = (D.R.k : ℝ) / sc.x - 1 / sc.x := by ring
    linarith
  have hmul : ((D.R.k : ℝ) - 1) * (Real.log (w j ρ) - Real.log (bN D ρ j)) ≤
      ((D.R.k : ℝ) - 1) * (1 / sc.x) :=
    mul_le_mul_of_nonneg_left hratio (by linarith)
  nlinarith

/- English proof (translation)
Establish `hP` using `place_data_under_section_B D sc C0 Δ w hB u ρ`. Establish `hm2` using `D.R.two_le_m`. Establish `hk5` using `D.R.m_add_three_le_k`. Establish `hΔ : 1 ≤ Δ`. Unfold `DataB at hB`.

Conclude with `hB.2.2.2.2.2.2.1`. Establish `hx1 : (1 : ℝ) ≤ sc.x` using `sc.one_lt_alt.le`. Take `⟨hvu, hvr, hVV⟩` from `Formalism.LogVandermondeBounds.StandardLattice.VandPlace_holds sc.eps sc.x sc.eps_pos hx1 D.R.k D.R.m Δ (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) (by omega) (by omega) hΔ hP`. Establish `hfac : 0 < facProd D.R.r` using `Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i`. Establish `hvandu : vand (uColR D u ρ) = Formalism.LogVandermondeBounds.StandardLattice.vandN (uN D u ρ) D.R.k`.

Rewrite using `[column_param_eq_fun, vandermonde_fin_eq_nat]`. Establish `hdimrow : dimV (rowLam D ρ) = Formalism.LogVandermondeBounds.StandardLattice.vandN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) / facProd D.R.r`. Rewrite using `[dim_weyl_line_eq, rank_eq_sum]`. Both sides reduce to the same expression. Use `set A := Formalism.LogVandermondeBounds.StandardLattice.vandN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) with hAdef`.

Use `set U := Formalism.LogVandermondeBounds.StandardLattice.vandN (uN D u ρ) D.R.k with hUdef`. Establish `hdsig : (2 / 3 : ℝ) * (A / facProd D.R.r) ≤ D.dsig ρ`. Rewrite using `[← hdimrow]`. Conclude with `h3`. Establish `hA' : (2 / 3 : ℝ) * A ≤ D.dsig ρ * facProd D.R.r`.

Use `mul_le_mul_of_nonneg_right hdsig hfac.le` as an intermediate fact. Rewrite `this` using `[mul_assoc, div_mul_cancel₀ _ hfac.ne']`. Then use the resulting hypothesis. Establish `hdivle : (2 / 3 : ℝ) * A / U ≤ D.dsig ρ * facProd D.R.r / U`. Rewrite using `[div_eq_mul_inv, div_eq_mul_inv]`. Conclude with `mul_le_mul_of_nonneg_right hA' (inv_nonneg.mpr hvu.le)`.

Establish `hlog1` using `Real.log_le_log (div_pos (mul_pos (by norm_num) hvr) hvu) hdivle`. Rewrite `hlog1` using `[Real.log_div (mul_pos (by norm_num) hvr).ne' hvu.ne', Real.log_mul (by norm_num) hvr.ne']`. Establish `hLd : sc.L = sc.x ^ sc.eps` using `rfl`. Establish `h8 : Real.log (8 * (sc.x * Real.exp (sc.x ^ sc.eps))) = Real.log 8 + Real.log sc.x + sc.L`. Rewrite using `[Real.log_mul (by norm_num) (mul_pos (by linarith) (Real.exp_pos _)).ne', Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, hLd]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hVV` using `[h8]`. Establish `hkpos : (0 : ℝ) < D.R.k` using `by exact_mod_cast (by omega : 0 < D.R.k)`. Establish `hlogk : Real.log D.R.k ≤ sc.L` using `le_trans (Real.log_le_log hkpos (by linarith)) h2k`. Establish `hm1` using `mul_le_mul_of_nonneg_left hx hkpos.le`.

Establish `hm2'` using `mul_le_mul_of_nonneg_left hlogk hkpos.le`. Rewrite using `[hvandu]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem place_dimension_lower_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (h2k : Real.log (2 * (D.R.k : ℝ)) ≤ sc.L)
    (hx : 2 * (Real.log 8 + 1 + Real.log sc.x) ≤ sc.L) (u : D.what₂.Word) (ρ : D.what₂.Tau)
    (h3 : (2 / 3 : ℝ) * dimV (rowLam D ρ) ≤ D.dsig ρ) :
    Real.log (2 / 3) + ((D.R.k : ℝ) - 1) * ∑ j ∈ range D.R.m, Real.log (bN D ρ j) - 5 * D.R.k * sc.L ≤
      Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) := by
  have hP := place_data_under_section_B D sc C0 Δ w hB u ρ
  have hm2 := D.R.two_le_m
  have hk5 := D.R.m_add_three_le_k
  have hΔ : 1 ≤ Δ := by
    unfold DataB at hB
    exact hB.2.2.2.2.2.2.1
  have hx1 : (1 : ℝ) ≤ sc.x := sc.one_lt_alt.le
  obtain ⟨hvu, hvr, hVV⟩ := Formalism.LogVandermondeBounds.StandardLattice.VandPlace_holds sc.eps sc.x sc.eps_pos hx1 D.R.k D.R.m Δ
    (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) (by omega) (by omega) hΔ hP
  have hfac : 0 < facProd D.R.r := Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  have hvandu : vand (uColR D u ρ) = Formalism.LogVandermondeBounds.StandardLattice.vandN (uN D u ρ) D.R.k := by
    rw [column_param_eq_fun, vandermonde_fin_eq_nat]
  have hdimrow : dimV (rowLam D ρ) =
      Formalism.LogVandermondeBounds.StandardLattice.vandN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) /
        facProd D.R.r := by
    rw [dim_weyl_line_eq, rank_eq_sum]
    rfl
  set A := Formalism.LogVandermondeBounds.StandardLattice.vandN (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) (D.R.k - 1 + D.R.m) with hAdef
  set U := Formalism.LogVandermondeBounds.StandardLattice.vandN (uN D u ρ) D.R.k with hUdef
  have hdsig : (2 / 3 : ℝ) * (A / facProd D.R.r) ≤ D.dsig ρ := by
    rw [← hdimrow]
    exact h3
  have hA' : (2 / 3 : ℝ) * A ≤ D.dsig ρ * facProd D.R.r := by
    have := mul_le_mul_of_nonneg_right hdsig hfac.le
    rwa [mul_assoc, div_mul_cancel₀ _ hfac.ne'] at this
  have hdivle : (2 / 3 : ℝ) * A / U ≤ D.dsig ρ * facProd D.R.r / U := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hA' (inv_nonneg.mpr hvu.le)
  have hlog1 := Real.log_le_log (div_pos (mul_pos (by norm_num) hvr) hvu) hdivle
  rw [Real.log_div (mul_pos (by norm_num) hvr).ne' hvu.ne', Real.log_mul (by norm_num) hvr.ne'] at hlog1
  have hLd : sc.L = sc.x ^ sc.eps := rfl
  have h8 : Real.log (8 * (sc.x * Real.exp (sc.x ^ sc.eps))) = Real.log 8 + Real.log sc.x + sc.L := by
    rw [Real.log_mul (by norm_num) (mul_pos (by linarith) (Real.exp_pos _)).ne',
      Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp, hLd]
    ring
  rw [h8] at hVV
  have hkpos : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hlogk : Real.log D.R.k ≤ sc.L := le_trans (Real.log_le_log hkpos (by linarith)) h2k
  have hm1 := mul_le_mul_of_nonneg_left hx hkpos.le
  have hm2' := mul_le_mul_of_nonneg_left hlogk hkpos.le
  rw [hvandu]
  linarith

/- English proof (translation)
Establish `hK : 0 < K` using `by linarith`. Establish `hF0 : 0 ≤ F` using `by linarith`. Establish `hFK : 0 < F * K` using `mul_pos (by linarith) hK`. Establish `hMM : 0 ≤ Mm * (Mm - 1) / 2` using `by nlinarith`. Establish `key : F * K * (X - lo) = F * (Mm * (Mm - 1) / 2) * lv - F * K * lv - F * ((Mm - 1) / 2) * l2v + SL + F * (Mm * (Mm - 1) / 2) * G + F * SG + (SP - K * SW) + 11 * F * K * Lr`.

Take the linear combination `hid - hlo`. Establish `hQ : 0 ≤ 3 * K * Lr - (Mm - 1) / 2 * Lr - Mm - 2 - K`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hMK (by linarith : (0 : ℝ) ≤ Lr), mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ K), mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ Mm)]`. Establish `h1 : 0 ≤ F * (Mm * (Mm - 1) / 2) * lv` using `mul_nonneg (mul_nonneg hF0 hMM) hlv0`. Establish `h2 : F * K * lv ≤ F * K * Lr` using `mul_le_mul_of_nonneg_left hlv hFK.le`.

Establish `h3 : F * ((Mm - 1) / 2) * l2v ≤ F * ((Mm - 1) / 2) * Lr` using `mul_le_mul_of_nonneg_left hl2v (mul_nonneg hF0 (by linarith))`. Establish `h4 : 0 ≤ F * (Mm * (Mm - 1) / 2) * G` using `mul_nonneg (mul_nonneg hF0 hMM) hG`. Establish `h5 : F * (-2) ≤ F * SG` using `mul_le_mul_of_nonneg_left hSG hF0`. Establish `h6 : 0 ≤ F * (3 * K * Lr - (Mm - 1) / 2 * Lr - Mm - 2 - K)` using `mul_nonneg hF0 hQ`. Establish `hpos : 0 ≤ F * K * (X - lo)`.

Rewrite using `[key]`. Use the polynomial consequences of the given equalities and inequalities. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `: F * K * (X - lo) < 0` using `mul_neg_of_pos_of_neg hFK (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_X_lower_arithmetic (F K Mm Lr lv l2v G SL SG SP SW X lo : ℝ)
    (hF : 1 ≤ F) (hM : 44 ≤ Mm) (hMK : Mm ≤ K) (hL : 1 ≤ Lr) (hlv0 : 0 ≤ lv) (hlv : lv ≤ Lr) (hl2v : l2v ≤ Lr)
    (hG : 0 ≤ G) (hSL : -(F * (Mm - 1)) ≤ SL) (hSG : -2 ≤ SG)
    (hSPW : F * (-1 - 5 * K * Lr - (K + 2 * K * Lr)) ≤ SP - K * SW)
    (hid : F * K * X = F * ((Mm - 1) * K + Mm * (Mm - 1) / 2) * lv - F * ((Mm - 1) / 2) * l2v + SL +
      F * (Mm * (2 * K + Mm - 1) / 2) * G + F * SG + SP)
    (hlo : F * K * lo = K * SW + F * K * Mm * lv + F * K * Mm * G - 11 * F * K * Lr) : lo ≤ X := by
  have hK : 0 < K := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hFK : 0 < F * K := mul_pos (by linarith) hK
  have hMM : 0 ≤ Mm * (Mm - 1) / 2 := by nlinarith
  have key : F * K * (X - lo) = F * (Mm * (Mm - 1) / 2) * lv - F * K * lv - F * ((Mm - 1) / 2) * l2v +
      SL + F * (Mm * (Mm - 1) / 2) * G + F * SG + (SP - K * SW) + 11 * F * K * Lr := by
    linear_combination hid - hlo
  have hQ : 0 ≤ 3 * K * Lr - (Mm - 1) / 2 * Lr - Mm - 2 - K := by
    nlinarith [mul_le_mul_of_nonneg_right hMK (by linarith : (0 : ℝ) ≤ Lr),
      mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ K),
      mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ Mm)]
  have h1 : 0 ≤ F * (Mm * (Mm - 1) / 2) * lv := mul_nonneg (mul_nonneg hF0 hMM) hlv0
  have h2 : F * K * lv ≤ F * K * Lr := mul_le_mul_of_nonneg_left hlv hFK.le
  have h3 : F * ((Mm - 1) / 2) * l2v ≤ F * ((Mm - 1) / 2) * Lr :=
    mul_le_mul_of_nonneg_left hl2v (mul_nonneg hF0 (by linarith))
  have h4 : 0 ≤ F * (Mm * (Mm - 1) / 2) * G := mul_nonneg (mul_nonneg hF0 hMM) hG
  have h5 : F * (-2) ≤ F * SG := mul_le_mul_of_nonneg_left hSG hF0
  have h6 : 0 ≤ F * (3 * K * Lr - (Mm - 1) / 2 * Lr - Mm - 2 - K) := mul_nonneg hF0 hQ
  have hpos : 0 ≤ F * K * (X - lo) := by
    rw [key]
    nlinarith
  by_contra hlt
  push_neg at hlt
  have : F * K * (X - lo) < 0 := mul_neg_of_pos_of_neg hFK (by linarith)
  linarith

/- English proof (translation)
Use `letI := D.host.cmStar`. Take `⟨hB, hR⟩` from `hA`. Establish `hf0 : 0 < D.R.f` using `degree_pos_alt D`. Establish `hfR : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf0`. Establish `hfne : (D.R.f : ℝ) ≠ 0` using `by linarith`.

Establish `hm2` using `D.R.two_le_m`. Establish `hk5` using `D.R.m_add_three_le_k`. Establish `hr` using `rank_eq_sum D`. Unfold `RowsA at hR`. Take `⟨hl2v, hgL, h44, hmk, hmx, h2k, -, -⟩` from `hR`.

Establish `hL` using `scale_one_le_L sc`. Establish `hx1` using `sc.one_lt_alt`. Establish `hkR : (0 : ℝ) < D.R.k` using `by exact_mod_cast (by omega : 0 < D.R.k)`. Establish `hmkR : (D.R.m : ℝ) ≤ D.R.k` using `by exact_mod_cast hmk`. Establish `h44R : (44 : ℝ) ≤ D.R.m` using `by exact_mod_cast h44`.

Establish `hpi : Real.pi ≤ D.host.v`. Unfold `DataB at hB`. Conclude with `hB.1`. Establish `hlogv : Real.log D.host.v ≤ sc.L`. Unfold `DataB at hB`.

Conclude with `hB.2.1`. Establish `hvpos : 0 < D.host.v` using `lt_of_lt_of_le Real.pi_pos hpi`. Establish `hgR : ∀ i : Fin 2, (3 : ℝ) ≤ (D.host.g i : ℝ)` using `fun i => by`. Conclude with `three_le_level_of_section_B D sc C0 Δ w hB i` after adjusting the coercions. Take `⟨lv, hlvd⟩ : ∃ lv : ℝ, lv = Real.log (D.host.v / Real.pi)` from `⟨_, rfl⟩`.

Take `⟨G, hGd⟩ : ∃ G : ℝ, G = Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))` from `⟨_, rfl⟩`. Take `⟨SW, hSWd⟩ : ∃ SW : ℝ, SW = ∑ ρ, ∑ j ∈ range D.R.m, Real.log (w j ρ)` from `⟨_, rfl⟩`. Establish `hlv0 : 0 ≤ lv`. Rewrite using `[hlvd]`. Conclude with `Real.log_nonneg ((one_le_div Real.pi_pos).mpr hpi)`.

Establish `hlv : lv ≤ sc.L`. Rewrite using `[hlvd, Real.log_div hvpos.ne' Real.pi_pos.ne']`. Use `Real.log_pos (by linarith [Real.pi_gt_three] : (1 : ℝ) < Real.pi)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hG : 0 ≤ G`.

Rewrite using `[hGd]`. Conclude with `Real.log_nonneg (by nlinarith [hgR 0, hgR 1])`. Establish `hSL : -((D.R.f : ℝ) * ((D.R.m : ℝ) - 1)) ≤ ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M)`. Establish `hterm : ∀ M ∈ Finset.Ioc D.R.k D.R.r, -(D.R.f : ℝ) ≤ Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M)`. Introduce `M hM`.

Establish `hM2 : 2 ≤ M`. Rewrite `hM` using `[Finset.mem_Ioc]`. Use linear arithmetic over natural numbers and integers. Establish `h1` using `massIdentity_holds D M hM2`. Establish `h2` using `Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one M hM2`.

Rewrite `h1` using `[zetaR_eq]`. Establish `h3` using `neg_abs_le (Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M))`. Use the polynomial consequences of the given equalities and inequalities. Establish `h` using `Finset.card_nsmul_le_sum _ _ _ hterm`. Rewrite `h` using `[Nat.card_Ioc, nsmul_eq_mul]`.

Establish `hc : ((D.R.r - D.R.k : ℕ) : ℝ) = (D.R.m : ℝ) - 1`. Establish `h' : D.R.r - D.R.k + 1 = D.R.m` using `by omega`. Establish `h'' : ((D.R.r - D.R.k : ℕ) : ℝ) + 1 = D.R.m` using `by exact_mod_cast h'`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h` using `[hc]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hSGi : ∀ i : Fin 2, -1 ≤ ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹)`. Introduce `i`. Establish `hg2 : 2 ≤ D.host.g i`. Use `three_le_level_of_section_B D sc C0 Δ w hB i` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hpos : ∀ j ∈ Finset.Ioc D.R.k D.R.r, 0 < 1 - ((D.host.g i : ℝ) ^ j)⁻¹` using `fun j hj => one_sub_inv_pow_pos _ hg2 j (by rw [Finset.mem_Ioc] at hj; omega)`. Rewrite using `[← Real.log_prod (fun j hj => (hpos j hj).ne')]`. Establish `hsplit` using `piN_split D.R.k (D.R.r - D.R.k) (D.host.g i)`. Rewrite `hsplit` using `[show D.R.k + (D.R.r - D.R.k) = D.R.r by omega]`.

Establish `hpk` using `piN_pos D.R.k (D.host.g i) hg2`. Establish `hprod : ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) = piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i)`. Rewrite using `[hsplit, mul_div_cancel_left₀ _ hpk.ne']`. Rewrite using `[hprod]`. Establish `h42` using `((local_index_formulas_and_bounds D).1 i).2.2.1`.

Establish `hgk : (9 : ℝ) ≤ (D.host.g i : ℝ) ^ (D.R.k + 1)`. Combine the equalities or inequalities in the displayed calculation. Establish `hinv : ((D.host.g i : ℝ) ^ (D.R.k + 1))⁻¹ ≤ 1 / 9`. Rewrite using `[one_div]`. Conclude with `inv_anti₀ (by norm_num) hgk`.

Establish `hrat : (7 : ℝ) / 9 ≤ piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i)` using `by linarith`. Establish `hrpos : 0 < piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i)` using `by linarith`. Establish `hl` using `Real.one_sub_inv_le_log_of_pos hrpos`. Establish `hinv2 : (piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i))⁻¹ ≤ 9 / 7`. Rewrite using `[show (9 : ℝ) / 7 = ((7 : ℝ) / 9)⁻¹ by norm_num]`.

Conclude with `inv_anti₀ (by norm_num) hrat`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hSG : -2 ≤ ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹)`. Rewrite using `[Fin.sum_univ_two]`. Combine the linear relations using `[hSGi 0, hSGi 1]`.

Establish `hgap : ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (spectralGapLowerBound D (1 / 3))`. Introduce `ρ a b hab`. Conclude with `le_trans (explicit_gap_le_general_gap D 8192 (1 / 3) le_rfl) (((h4B Δ w hB).2.1 ρ) a b hab)`. Establish `hexp : Real.exp (-(D.R.r : ℝ)) ≤ 1 / 3`. Establish `hr2 : (2 : ℝ) ≤ D.R.r` using `by exact_mod_cast (by omega : 2 ≤ D.R.r)`.

Establish `h1 : Real.exp (-(D.R.r : ℝ)) ≤ Real.exp (-2)` using `Real.exp_le_exp.mpr (by linarith)`. Establish `h2 : (3 : ℝ) ≤ Real.exp 2`. Use `Real.add_one_le_exp 2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : (Real.exp 2)⁻¹ ≤ 1 / 3`.

Rewrite using `[one_div]`. Conclude with `inv_anti₀ (by norm_num) h2`. Establish `h5 : Real.exp (-2) = (Real.exp 2)⁻¹` using `Real.exp_neg 2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3ρ : ∀ ρ, (2 / 3 : ℝ) * dimV (rowLam D ρ) ≤ D.dsig ρ`.

Introduce `ρ`. Establish `h` using `(h3 (1 / 3) hexp (by norm_num) ρ (hgap ρ)).1`. Establish `e : (1 : ℝ) - 1 / 3 = 2 / 3` using `by norm_num`. Rewrite `h` using `[e]`. Conclude with `h`.

Establish `hl23 : -1 ≤ Real.log (2 / 3)`. Use `Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2 / 3)` as an intermediate fact. Evaluate the numerical expressions using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hρ : ∀ ρ, -1 - 5 * (D.R.k : ℝ) * sc.L - ((D.R.k : ℝ) + 2 * D.R.k * sc.L) ≤ Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) - (D.R.k : ℝ) * ∑ j ∈ range D.R.m, Real.log (w j ρ)`.

Introduce `ρ`. Establish `hpl` using `place_dimension_lower_bound D sc C0 Δ w hB h2k hx u ρ (h3ρ ρ)`. Establish `hj : ∀ j ∈ range D.R.m, (D.R.k : ℝ) * Real.log (w j ρ) - ((D.R.k : ℝ) - 1) * Real.log (bN D ρ j) ≤ (D.R.k : ℝ) / sc.x + 2 * sc.L` using `fun j hj => log_weight_minus_log_b_bound D sc C0 Δ w hB ρ j (Finset.mem_range.mp hj)`. Establish `hsum` using `Finset.sum_le_sum hj`. Rewrite `hsum` using `[Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`.

Establish `hmx' : (D.R.m : ℝ) * ((D.R.k : ℝ) / sc.x) ≤ D.R.k`. Rewrite using `[mul_div_assoc', div_le_iff₀ (by linarith)]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hmx hkR.le]`. Establish `hmk' : (D.R.m : ℝ) * (2 * sc.L) ≤ 2 * D.R.k * sc.L`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hmkR (by linarith : (0 : ℝ) ≤ sc.L)]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hSPW : (D.R.f : ℝ) * (-1 - 5 * D.R.k * sc.L - (D.R.k + 2 * D.R.k * sc.L)) ≤ (∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ))) - (D.R.k : ℝ) * SW`. Establish `h` using `Finset.sum_le_sum (fun ρ (_ : ρ ∈ (Finset.univ : Finset D.what₂.Tau)) => hρ ρ)`. Rewrite `h` using `[Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]`. Rewrite using `[hSWd]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hid : (D.R.f : ℝ) * D.R.k * logXuD D u = (D.R.f : ℝ) * (((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2) * lv - (D.R.f : ℝ) * (((D.R.m : ℝ) - 1) / 2) * Real.log (2 * D.host.v) + ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.ho …`. Rewrite using `[hlvd, hGd]`. Conclude with `identity_five_one_of_aux2b_of_aux2v D h2b h2v u`. Establish `hinner : ∀ j ∈ range D.R.m, ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) = (∑ ρ, Real.log (w j ρ)) + D.R.f * lv`.

Introduce `j hj`. Combine the equalities or inequalities in the displayed calculation. Establish `hw1` using `weights_ge_one_section_B D sc C0 Δ w hB ρ j (Finset.mem_range.mp hj)`. Rewrite using `[mul_div_assoc, Real.log_mul (by linarith) (div_pos hvpos Real.pi_pos).ne', hlvd]`. Use `_ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`.

Establish `hlow : ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) = (1 / (D.R.f : ℝ)) * SW + D.R.m * lv`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinner j hj, mul_add, ← mul_assoc, one_div_mul_cancel hfne, one_mul]`. Use `_ = (1 / (D.R.f : ℝ)) * ∑ j ∈ range D.R.m, ∑ ρ, Real.log (w j ρ) + D.R.m * lv := by`. Rewrite using `[Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]`.

Use `_ = _ := by rw [hSWd, Finset.sum_comm]`. Establish `hlogg : ∑ i : Fin 2, Real.log (D.host.g i : ℝ) = G`. Rewrite using `[Fin.sum_univ_two, hGd, Real.log_mul (by linarith [hgR 0]) (by linarith [hgR 1])]`. Establish `hlo : (D.R.f : ℝ) * D.R.k * lowS D sc w = (D.R.k : ℝ) * SW + D.R.f * D.R.k * D.R.m * lv + D.R.f * D.R.k * D.R.m * G - 11 * D.R.f * D.R.k * sc.L`. Unfold `lowS`.

Rewrite using `[hlow, hlogg]`. Clear the denominators using the available nonvanishing facts. Conclude with `log_X_lower_arithmetic (D.R.f : ℝ) (D.R.k : ℝ) (D.R.m : ℝ) sc.L lv (Real.log (2 * D.host.v)) G _ _ _ SW (logXuD D u) (lowS D sc w) hfR h44R hmkR hL hlv0 hlv hl2v hG hSL hSG hSPW hid hlo`.
-/
theorem part_five_lower_at_scale (D : D7) (sc : Scale) (C0 CY : ℝ)
    (hx : 2 * (Real.log 8 + 1 + Real.log sc.x) ≤ sc.L)
    (h2b : MassRatio₂ D) (h2v : VolumeEqMass₂ D) (h3 : SigmaDegreeTwoSidedBoundOfGap D) (h4B : PartFourSectionBData D sc 8192 C0)
    (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hA : DataA D sc C0 CY Δ w) (u : D.what₂.Word) :
    lowS D sc w ≤ logXuD D u := by
  letI := D.host.cmStar
  obtain ⟨hB, hR⟩ := hA
  have hf0 : 0 < D.R.f := degree_pos_alt D
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf0
  have hfne : (D.R.f : ℝ) ≠ 0 := by linarith
  have hm2 := D.R.two_le_m
  have hk5 := D.R.m_add_three_le_k
  have hr := rank_eq_sum D
  unfold RowsA at hR
  obtain ⟨hl2v, hgL, h44, hmk, hmx, h2k, -, -⟩ := hR
  have hL := scale_one_le_L sc
  have hx1 := sc.one_lt_alt
  have hkR : (0 : ℝ) < D.R.k := by exact_mod_cast (by omega : 0 < D.R.k)
  have hmkR : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast hmk
  have h44R : (44 : ℝ) ≤ D.R.m := by exact_mod_cast h44
  have hpi : Real.pi ≤ D.host.v := by
    unfold DataB at hB
    exact hB.1
  have hlogv : Real.log D.host.v ≤ sc.L := by
    unfold DataB at hB
    exact hB.2.1
  have hvpos : 0 < D.host.v := lt_of_lt_of_le Real.pi_pos hpi
  have hgR : ∀ i : Fin 2, (3 : ℝ) ≤ (D.host.g i : ℝ) := fun i => by
    exact_mod_cast three_le_level_of_section_B D sc C0 Δ w hB i
  obtain ⟨lv, hlvd⟩ : ∃ lv : ℝ, lv = Real.log (D.host.v / Real.pi) := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G : ℝ, G = Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨SW, hSWd⟩ : ∃ SW : ℝ, SW = ∑ ρ, ∑ j ∈ range D.R.m, Real.log (w j ρ) := ⟨_, rfl⟩
  have hlv0 : 0 ≤ lv := by
    rw [hlvd]
    exact Real.log_nonneg ((one_le_div Real.pi_pos).mpr hpi)
  have hlv : lv ≤ sc.L := by
    rw [hlvd, Real.log_div hvpos.ne' Real.pi_pos.ne']
    have := Real.log_pos (by linarith [Real.pi_gt_three] : (1 : ℝ) < Real.pi)
    linarith
  have hG : 0 ≤ G := by
    rw [hGd]
    exact Real.log_nonneg (by nlinarith [hgR 0, hgR 1])

  have hSL : -((D.R.f : ℝ) * ((D.R.m : ℝ) - 1)) ≤
      ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) := by
    have hterm : ∀ M ∈ Finset.Ioc D.R.k D.R.r, -(D.R.f : ℝ) ≤ Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) := by
      intro M hM
      have hM2 : 2 ≤ M := by
        rw [Finset.mem_Ioc] at hM
        omega
      have h1 := massIdentity_holds D M hM2
      have h2 := Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one M hM2
      rw [zetaR_eq] at h1
      have h3 := neg_abs_le (Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M))
      nlinarith
    have h := Finset.card_nsmul_le_sum _ _ _ hterm
    rw [Nat.card_Ioc, nsmul_eq_mul] at h
    have hc : ((D.R.r - D.R.k : ℕ) : ℝ) = (D.R.m : ℝ) - 1 := by
      have h' : D.R.r - D.R.k + 1 = D.R.m := by omega
      have h'' : ((D.R.r - D.R.k : ℕ) : ℝ) + 1 = D.R.m := by exact_mod_cast h'
      linarith
    rw [hc] at h
    nlinarith

  have hSGi : ∀ i : Fin 2, -1 ≤ ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) := by
    intro i
    have hg2 : 2 ≤ D.host.g i := by
      have := three_le_level_of_section_B D sc C0 Δ w hB i
      omega
    have hpos : ∀ j ∈ Finset.Ioc D.R.k D.R.r, 0 < 1 - ((D.host.g i : ℝ) ^ j)⁻¹ := fun j hj =>
      one_sub_inv_pow_pos _ hg2 j (by rw [Finset.mem_Ioc] at hj; omega)
    rw [← Real.log_prod (fun j hj => (hpos j hj).ne')]
    have hsplit := piN_split D.R.k (D.R.r - D.R.k) (D.host.g i)
    rw [show D.R.k + (D.R.r - D.R.k) = D.R.r by omega] at hsplit
    have hpk := piN_pos D.R.k (D.host.g i) hg2
    have hprod : ∏ j ∈ Finset.Ioc D.R.k D.R.r, (1 - ((D.host.g i : ℝ) ^ j)⁻¹) =
        piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i) := by
      rw [hsplit, mul_div_cancel_left₀ _ hpk.ne']
    rw [hprod]
    have h42 := ((local_index_formulas_and_bounds D).1 i).2.2.1
    have hgk : (9 : ℝ) ≤ (D.host.g i : ℝ) ^ (D.R.k + 1) := by
      calc (9 : ℝ) = 3 ^ 2 := by norm_num
        _ ≤ (D.host.g i : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) (hgR i) 2
        _ ≤ (D.host.g i : ℝ) ^ (D.R.k + 1) := pow_le_pow_right₀ (by linarith [hgR i]) (by omega)
    have hinv : ((D.host.g i : ℝ) ^ (D.R.k + 1))⁻¹ ≤ 1 / 9 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) hgk
    have hrat : (7 : ℝ) / 9 ≤ piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i) := by linarith
    have hrpos : 0 < piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i) := by linarith
    have hl := Real.one_sub_inv_le_log_of_pos hrpos
    have hinv2 : (piN D.R.r (D.host.g i) / piN D.R.k (D.host.g i))⁻¹ ≤ 9 / 7 := by
      rw [show (9 : ℝ) / 7 = ((7 : ℝ) / 9)⁻¹ by norm_num]
      exact inv_anti₀ (by norm_num) hrat
    linarith
  have hSG : -2 ≤ ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) := by
    rw [Fin.sum_univ_two]
    linarith [hSGi 0, hSGi 1]

  have hgap : ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (spectralGapLowerBound D (1 / 3)) := by
    intro ρ a b hab
    exact le_trans (explicit_gap_le_general_gap D 8192 (1 / 3) le_rfl) (((h4B Δ w hB).2.1 ρ) a b hab)
  have hexp : Real.exp (-(D.R.r : ℝ)) ≤ 1 / 3 := by
    have hr2 : (2 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 2 ≤ D.R.r)
    have h1 : Real.exp (-(D.R.r : ℝ)) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp 2
      linarith
    have h4 : (Real.exp 2)⁻¹ ≤ 1 / 3 := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) h2
    have h5 : Real.exp (-2) = (Real.exp 2)⁻¹ := Real.exp_neg 2
    linarith
  have h3ρ : ∀ ρ, (2 / 3 : ℝ) * dimV (rowLam D ρ) ≤ D.dsig ρ := by
    intro ρ
    have h := (h3 (1 / 3) hexp (by norm_num) ρ (hgap ρ)).1
    have e : (1 : ℝ) - 1 / 3 = 2 / 3 := by norm_num
    rw [e] at h
    exact h
  have hl23 : -1 ≤ Real.log (2 / 3) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2 / 3)
    norm_num at this
    linarith
  have hρ : ∀ ρ, -1 - 5 * (D.R.k : ℝ) * sc.L - ((D.R.k : ℝ) + 2 * D.R.k * sc.L) ≤
      Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) -
        (D.R.k : ℝ) * ∑ j ∈ range D.R.m, Real.log (w j ρ) := by
    intro ρ
    have hpl := place_dimension_lower_bound D sc C0 Δ w hB h2k hx u ρ (h3ρ ρ)
    have hj : ∀ j ∈ range D.R.m, (D.R.k : ℝ) * Real.log (w j ρ) - ((D.R.k : ℝ) - 1) * Real.log (bN D ρ j) ≤
        (D.R.k : ℝ) / sc.x + 2 * sc.L :=
      fun j hj => log_weight_minus_log_b_bound D sc C0 Δ w hB ρ j (Finset.mem_range.mp hj)
    have hsum := Finset.sum_le_sum hj
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at hsum
    have hmx' : (D.R.m : ℝ) * ((D.R.k : ℝ) / sc.x) ≤ D.R.k := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hmx hkR.le]
    have hmk' : (D.R.m : ℝ) * (2 * sc.L) ≤ 2 * D.R.k * sc.L := by
      nlinarith [mul_le_mul_of_nonneg_right hmkR (by linarith : (0 : ℝ) ≤ sc.L)]
    nlinarith
  have hSPW : (D.R.f : ℝ) * (-1 - 5 * D.R.k * sc.L - (D.R.k + 2 * D.R.k * sc.L)) ≤
      (∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ))) - (D.R.k : ℝ) * SW := by
    have h := Finset.sum_le_sum (fun ρ (_ : ρ ∈ (Finset.univ : Finset D.what₂.Tau)) => hρ ρ)
    rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum] at h
    rw [hSWd]
    linarith

  have hid : (D.R.f : ℝ) * D.R.k * logXuD D u =
      (D.R.f : ℝ) * (((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2) * lv -
        (D.R.f : ℝ) * (((D.R.m : ℝ) - 1) / 2) * Real.log (2 * D.host.v) +
        ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) +
        (D.R.f : ℝ) * ((D.R.m : ℝ) * (2 * D.R.k + D.R.m - 1) / 2) * G +
        (D.R.f : ℝ) * ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) +
        ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) := by
    rw [hlvd, hGd]
    exact identity_five_one_of_aux2b_of_aux2v D h2b h2v u
  have hinner : ∀ j ∈ range D.R.m, ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) =
      (∑ ρ, Real.log (w j ρ)) + D.R.f * lv := by
    intro j hj
    calc ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) = ∑ ρ, (Real.log (w j ρ) + lv) :=
          Finset.sum_congr rfl fun ρ _ => by
            have hw1 := weights_ge_one_section_B D sc C0 Δ w hB ρ j (Finset.mem_range.mp hj)
            rw [mul_div_assoc, Real.log_mul (by linarith) (div_pos hvpos Real.pi_pos).ne', hlvd]
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]
  have hlow : ∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi) =
      (1 / (D.R.f : ℝ)) * SW + D.R.m * lv := by
    calc _ = ∑ j ∈ range D.R.m, ((1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ) + lv) :=
          Finset.sum_congr rfl fun j hj => by
            rw [hinner j hj, mul_add, ← mul_assoc, one_div_mul_cancel hfne, one_mul]
      _ = (1 / (D.R.f : ℝ)) * ∑ j ∈ range D.R.m, ∑ ρ, Real.log (w j ρ) + D.R.m * lv := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = _ := by rw [hSWd, Finset.sum_comm]
  have hlogg : ∑ i : Fin 2, Real.log (D.host.g i : ℝ) = G := by
    rw [Fin.sum_univ_two, hGd, Real.log_mul (by linarith [hgR 0]) (by linarith [hgR 1])]
  have hlo : (D.R.f : ℝ) * D.R.k * lowS D sc w =
      (D.R.k : ℝ) * SW + D.R.f * D.R.k * D.R.m * lv + D.R.f * D.R.k * D.R.m * G - 11 * D.R.f * D.R.k * sc.L := by
    unfold lowS
    rw [hlow, hlogg]
    field_simp
  exact log_X_lower_arithmetic (D.R.f : ℝ) (D.R.k : ℝ) (D.R.m : ℝ) sc.L lv (Real.log (2 * D.host.v)) G _ _ _ SW
    (logXuD D u) (lowS D sc w) hfR h44R hmkR hL hlv0 hlv hl2v hG hSL hSG hSPW hid hlo

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x0, hx0⟩ : ∃ x0 : ℝ, ∀ x, x0 ≤ x → 2 * (Real.log 8 + 1 + Real.log x) ≤ x ^ eps := by`. Take `⟨A, hA⟩ : ∃ A : ℝ, A = 4 / eps + 2 * (Real.log 8 + 1) + 1` from `⟨_, rfl⟩`. Establish `h8 : 0 < Real.log 8` using `Real.log_pos (by norm_num)`. Establish `hd : 0 < 4 / eps` using `div_pos (by norm_num) heps`. Establish `hA1 : 1 ≤ A` using `by rw [hA]; linarith`.

Establish `hA0 : 0 < A` using `by linarith`. Use `⟨A ^ (2 / eps), fun x hx => ?_⟩` and prove the remaining obligations. Establish `hx0pos : 0 < A ^ (2 / eps)` using `Real.rpow_pos_of_pos hA0 _`. Establish `hxpos : 0 < x` using `lt_of_lt_of_le hx0pos hx`. Establish `he : (2 / eps) * (eps / 2) = 1`.

Rewrite using `[div_mul_div_comm, mul_comm 2 eps, div_self (mul_pos heps two_pos).ne']`. Establish `hyA : A ≤ x ^ (eps / 2)`. Combine the equalities or inequalities in the displayed calculation. Establish `hy2 : x ^ eps = (x ^ (eps / 2)) ^ 2`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hlog : Real.log x ≤ x ^ (eps / 2) / (eps / 2)` using `Real.log_le_rpow_div hxpos.le (by linarith)`. Rewrite `hlog` using `[div_div_eq_mul_div]`.

Establish `h2 : 2 * Real.log x ≤ 4 / eps * x ^ (eps / 2)`. Establish `e : x ^ (eps / 2) * 2 / eps * 2 = 4 / eps * x ^ (eps / 2)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy0 : 0 ≤ x ^ (eps / 2)` using `le_trans hA0.le hyA`. Establish `hmul1` using `mul_le_mul_of_nonneg_left hyA hy0`.

Establish `hmul2` using `mul_le_mul_of_nonneg_left (le_trans hA1 hyA) (by linarith : (0 : ℝ) ≤ 2 * (Real.log 8 + 1))`. Rewrite using `[hy2]`. Rewrite `hmul1` using `[hA]`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨x0, fun D sc hse hxx h2b h2v h3 h4B Δ w hA u => ?_⟩` and prove the remaining obligations.

Apply `part_five_lower_at_scale D sc C0 CY _ h2b h2v h3 h4B Δ w hA u` to reduce the goal to its premises. Establish `hLd : sc.L = sc.x ^ sc.eps` using `rfl`. Rewrite using `[hLd, hse]`. Conclude with `hx0 sc.x hxx`.
-/
theorem part_five_lower_eventually (eps C0 CY : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ (D : D7) (sc : Scale), sc.eps = eps → x0 ≤ sc.x → MassRatio₂ D → VolumeEqMass₂ D → SigmaDegreeTwoSidedBoundOfGap D →
      PartFourSectionBData D sc 8192 C0 → ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataA D sc C0 CY Δ w → ∀ u : D.what₂.Word,
        lowS D sc w ≤ logXuD D u := by
  obtain ⟨x0, hx0⟩ : ∃ x0 : ℝ, ∀ x, x0 ≤ x → 2 * (Real.log 8 + 1 + Real.log x) ≤ x ^ eps := by
    obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 4 / eps + 2 * (Real.log 8 + 1) + 1 := ⟨_, rfl⟩
    have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
    have hd : 0 < 4 / eps := div_pos (by norm_num) heps
    have hA1 : 1 ≤ A := by rw [hA]; linarith
    have hA0 : 0 < A := by linarith
    refine ⟨A ^ (2 / eps), fun x hx => ?_⟩
    have hx0pos : 0 < A ^ (2 / eps) := Real.rpow_pos_of_pos hA0 _
    have hxpos : 0 < x := lt_of_lt_of_le hx0pos hx
    have he : (2 / eps) * (eps / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm 2 eps, div_self (mul_pos heps two_pos).ne']
    have hyA : A ≤ x ^ (eps / 2) := by
      calc A = (A ^ (2 / eps)) ^ (eps / 2) := by rw [← Real.rpow_mul hA0.le, he, Real.rpow_one]
        _ ≤ x ^ (eps / 2) := Real.rpow_le_rpow hx0pos.le hx (by linarith)
    have hy2 : x ^ eps = (x ^ (eps / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
      congr 1
      push_cast
      ring
    have hlog : Real.log x ≤ x ^ (eps / 2) / (eps / 2) := Real.log_le_rpow_div hxpos.le (by linarith)
    rw [div_div_eq_mul_div] at hlog
    have h2 : 2 * Real.log x ≤ 4 / eps * x ^ (eps / 2) := by
      have e : x ^ (eps / 2) * 2 / eps * 2 = 4 / eps * x ^ (eps / 2) := by ring
      linarith
    have hy0 : 0 ≤ x ^ (eps / 2) := le_trans hA0.le hyA
    have hmul1 := mul_le_mul_of_nonneg_left hyA hy0
    have hmul2 := mul_le_mul_of_nonneg_left (le_trans hA1 hyA) (by linarith : (0 : ℝ) ≤ 2 * (Real.log 8 + 1))
    rw [hy2]
    rw [hA] at hmul1
    nlinarith
  refine ⟨x0, fun D sc hse hxx h2b h2v h3 h4B Δ w hA u => ?_⟩
  apply part_five_lower_at_scale D sc C0 CY _ h2b h2v h3 h4B Δ w hA u
  have hLd : sc.L = sc.x ^ sc.eps := rfl
  rw [hLd, hse]
  exact hx0 sc.x hxx

end Formalism.MainNotions.StandardLattice
