import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaFiveOneOfTheoremTwo

noncomputable section
namespace Formalism.MainNotions.StandardLattice
open NumberField Formalism.BasicNotions Finset

/- English proof (translation)
Establish `hr : 2 ≤ D.R.r`. Establish `h1` using `D.R.two_le_m`. Establish `h2` using `D.R.m_add_three_le_k`. Use `first`. Consider the case `(show 2 ≤ D.R.k + D.R.m - 1; omega)`.

Consider the case `omega`. Establish `hr' : (2 : ℝ) ≤ D.R.r` using `by exact_mod_cast hr`. Establish `h3 : (3 : ℝ) ≤ Real.exp 2`. Use `Real.add_one_le_exp (2 : ℝ)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_neg_r_le_third (D : D7) : Real.exp (-(D.R.r : ℝ)) ≤ 1 / 3 := by
  have hr : 2 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    first
      | (show 2 ≤ D.R.k + D.R.m - 1; omega)
      | omega
  have hr' : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  calc Real.exp (-(D.R.r : ℝ)) ≤ Real.exp (-2) := Real.exp_le_exp.2 (by linarith)
    _ = 1 / Real.exp 2 := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3

/- English proof (translation)
Establish `hk` using `D.R.k_ge`. Establish `hm` using `D.R.two_le_m`. Establish `hpl` using `place_data_under_section_B D sc C0 Δ w hB u ρ`. Establish `b7 : 1 ≤ Δ` using `hB.2.2.2.2.2.2.1`. Establish `hmk : (D.R.m : ℝ) ≤ D.R.k`.

Conclude with `(by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)` after adjusting the coercions. Establish `h` using `(h3 (1 / 3) (exp_neg_r_le_third D) (by norm_num) ρ (fun a b hab => le_trans (explicit_gap_le_general_gap D 8192 (1 / 3) le_rfl) (hgap ρ a b hab))).2`. Rewrite `h` using `[formal_degree_line_eq, count_plus_eq, count_minus_eq]`. Take `⟨hd, hT, hlog⟩` from `Formalism.LogVandermondeBounds.StandardLattice.UpperPlace_holds sc.eps sc.x sc.eps_pos sc.one_lt_alt.le D.R.k D.R.m Δ 3 (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) hm D.R.m_even (by omega) hmk b7 (by norm_num) hpl (fun i j hij hj => one_le_column_sub_of_lt D u ρ i j hij hj)`. Establish `a1` using `abs_param_sup_nonneg (rowLam D ρ)`.

Establish `a2` using `abs_param_sup_le D ρ`. Establish `hr1 : (1 : ℝ) ≤ ((D.R.k - 1 + D.R.m : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ D.R.k - 1 + D.R.m)`. Establish `h' : D.dsig ρ ≤ 4 * Formalism.LogVandermondeBounds.StandardLattice.dTau D.R.k D.R.m (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) * (3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * ((D.R.k - 1 + D.R.m : ℕ) : ℝ) * (vN D ρ 0 + bN D …`. Use `le_trans h ?_` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations.

Use `pow_le_pow_left₀ (by positivity) ?_ _` and prove the remaining obligations. Establish `c0 : 0 ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[dim_weyl_column_eq]`. Establish `h4` using `Real.log_le_log (D.dsig_pos ρ) h'`.

Establish `eL : sc.L = sc.x ^ sc.eps` using `rfl`. Rewrite using `[eL]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem place_dimension_upper_bound (D : D7) (sc : Scale) (C0 Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) (hB : DataB D sc C0 Δ w)
    (h3 : SigmaDegreeTwoSidedBoundOfGap D) (hgap : ∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D 8192 (1 / 3)))
    (u : D.what₂.Word) (ρ : D.what₂.Tau) :
    Real.log (D.dsig ρ) - Real.log (dimV (uColR D u ρ)) ≤
      (D.R.k : ℝ) * D.R.m * (Real.log 3 + 5 * Real.log (2 * D.R.k) + 5 * sc.L + 10) := by
  have hk := D.R.k_ge
  have hm := D.R.two_le_m
  have hpl := place_data_under_section_B D sc C0 Δ w hB u ρ
  have b7 : 1 ≤ Δ := hB.2.2.2.2.2.2.1
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    exact_mod_cast (by have := D.R.m_add_three_le_k; omega : D.R.m ≤ D.R.k)
  have h := (h3 (1 / 3) (exp_neg_r_le_third D) (by norm_num) ρ
    (fun a b hab => le_trans (explicit_gap_le_general_gap D 8192 (1 / 3) le_rfl) (hgap ρ a b hab))).2
  rw [formal_degree_line_eq, count_plus_eq, count_minus_eq] at h
  obtain ⟨hd, hT, hlog⟩ := Formalism.LogVandermondeBounds.StandardLattice.UpperPlace_holds sc.eps sc.x sc.eps_pos sc.one_lt_alt.le D.R.k D.R.m Δ 3
      (uN D u ρ) (vN D ρ) (bN D ρ) (fun j => w j ρ) hm D.R.m_even (by omega) hmk b7 (by norm_num) hpl
      (fun i j hij hj => one_le_column_sub_of_lt D u ρ i j hij hj)
  have a1 := abs_param_sup_nonneg (rowLam D ρ)
  have a2 := abs_param_sup_le D ρ
  have hr1 : (1 : ℝ) ≤ ((D.R.k - 1 + D.R.m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ D.R.k - 1 + D.R.m)
  have h' : D.dsig ρ ≤ 4 * Formalism.LogVandermondeBounds.StandardLattice.dTau D.R.k D.R.m (Formalism.LogVandermondeBounds.StandardLattice.rowPar D.R.k (vN D ρ) (bN D ρ)) *
      (3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * ((D.R.k - 1 + D.R.m : ℕ) : ℝ) *
        (vN D ρ 0 + bN D ρ (D.R.m - 1))) ^ ((D.R.k - 1 + D.R.m / 2) * (D.R.m / 2)) := by
    refine le_trans h ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have c0 : 0 ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) := by positivity
    calc 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * lamAbs (rowLam D ρ)
        ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * (vN D ρ 0 + bN D ρ (D.R.m - 1)) :=
          mul_le_mul_of_nonneg_left a2 c0
      _ = 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * 1 * (vN D ρ 0 + bN D ρ (D.R.m - 1)) := by ring
      _ ≤ 3 * ((D.R.k - 1 + D.R.m / 2 : ℕ) : ℝ) * ((D.R.m / 2 : ℕ) : ℝ) * ((D.R.k - 1 + D.R.m : ℕ) : ℝ) *
          (vN D ρ 0 + bN D ρ (D.R.m - 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 c0) (le_trans a1 a2)
  rw [dim_weyl_column_eq]
  have h4 := Real.log_le_log (D.dsig_pos ρ) h'
  have eL : sc.L = sc.x ^ sc.eps := rfl
  rw [eL]
  linarith

/- English proof (translation)
The claim follows from `Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i`.
-/
theorem facProd_pos' (N : ℕ) : 0 < facProd N :=
  Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i

/- English proof (translation)
Establish `hsplit : facProd r = facProd k * ∏ i ∈ Finset.Ico k r, ((i.factorial : ℕ) : ℝ)`. Unfold `facProd`. Rewrite using `[Finset.prod_range_mul_prod_Ico _ hkr]`. Establish `hk0 : 0 < facProd k` using `facProd_pos' k`. Establish `hP0 : 0 < ∏ i ∈ Finset.Ico k r, ((i.factorial : ℕ) : ℝ)` using `Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i`.

Rewrite using `[hsplit, Real.log_mul hk0.ne' hP0.ne', add_sub_cancel_left, Real.log_prod (fun i _ => by exact_mod_cast (Nat.factorial_pos i).ne')]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Establish `hir : i ≤ r` using `(Finset.mem_Ico.mp hi).2.le`. Establish `h1 : ((i.factorial : ℕ) : ℝ) ≤ (r : ℝ) ^ r`.

Conclude with `(Nat.factorial_le_pow i).trans ((Nat.pow_le_pow_left hir i).trans (Nat.pow_le_pow_right (by omega) hir))` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Use `_ = ((r - k : ℕ) : ℝ) * ((r : ℝ) * Real.log r) := by`. Rewrite using `[Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]`.
-/
theorem log_factorial_product_difference (k r : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r) :
    Real.log (facProd r) - Real.log (facProd k) ≤ ((r - k : ℕ) : ℝ) * ((r : ℝ) * Real.log r) := by
  have hsplit : facProd r = facProd k * ∏ i ∈ Finset.Ico k r, ((i.factorial : ℕ) : ℝ) := by
    unfold facProd
    rw [Finset.prod_range_mul_prod_Ico _ hkr]
  have hk0 : 0 < facProd k := facProd_pos' k
  have hP0 : 0 < ∏ i ∈ Finset.Ico k r, ((i.factorial : ℕ) : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  rw [hsplit, Real.log_mul hk0.ne' hP0.ne', add_sub_cancel_left,
    Real.log_prod (fun i _ => by exact_mod_cast (Nat.factorial_pos i).ne')]
  calc ∑ i ∈ Finset.Ico k r, Real.log ((i.factorial : ℕ) : ℝ)
      ≤ ∑ i ∈ Finset.Ico k r, ((r : ℝ) * Real.log r) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hir : i ≤ r := (Finset.mem_Ico.mp hi).2.le
        have h1 : ((i.factorial : ℕ) : ℝ) ≤ (r : ℝ) ^ r := by
          exact_mod_cast (Nat.factorial_le_pow i).trans
            ((Nat.pow_le_pow_left hir i).trans (Nat.pow_le_pow_right (by omega) hir))
        calc Real.log ((i.factorial : ℕ) : ℝ) ≤ Real.log ((r : ℝ) ^ r) :=
              Real.log_le_log (by exact_mod_cast Nat.factorial_pos i) h1
          _ = (r : ℝ) * Real.log r := by rw [Real.log_pow]
    _ = ((r - k : ℕ) : ℝ) * ((r : ℝ) * Real.log r) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]

/- English proof (translation)
Establish `hk0 : 0 < k` using `by linarith`. Establish `hm0 : 0 < m` using `by linarith`. Establish `hL0 : 0 < L` using `by linarith`. Establish `hCY : 0 ≤ CY`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Establish `: 2 * CY * L < 0` using `by nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht1 : f * ((m - 1) * k + m * (m - 1) / 2) * lv ≤ f * ((m - 1) * k + m * (m - 1) / 2) * L` using `mul_le_mul_of_nonneg_left hlv (by have : 0 ≤ (m - 1) * k := by nlinarith`. Establish `: 0 ≤ m * (m - 1) / 2` using `by nlinarith`.

Use the proof step `positivity)`. Establish `ht2 : 0 ≤ f * ((m - 1) / 2) * l2v`. Establish `: 0 ≤ (m - 1) / 2` using `by linarith`. Check the signs of the components of the expression. Establish `ht4 : f * (m * (2 * k + m - 1) / 2) * lg ≤ f * (m * (2 * k + m - 1) / 2) * (2 * CY * L)` using `mul_le_mul_of_nonneg_left hlg (by have : 0 ≤ m * (2 * k + m - 1) / 2 := by nlinarith positivity)`.

Establish `ht5 : f * S5 ≤ 0` using `mul_nonpos_of_nonneg_of_nonpos hf.le hS5`. Establish `hsum : f * k * X ≤ f * (((m - 1) * k + m * (m - 1) / 2) * L + m + m * (2 * k + m - 1) * CY * L + k * m * (12 + 12 * L))`. Rewrite using `[id]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpoly : ((m - 1) * k + m * (m - 1) / 2) * L + m + m * (2 * k + m - 1) * CY * L + k * m * (12 + 12 * L) ≤ k * ((15 + 3 * CY) * m * L)`.

Establish `a1 : 0 ≤ CY * L * m * (k - m + 1)`. Establish `: 0 ≤ k - m + 1` using `by linarith`. Check the signs of the components of the expression. Establish `a2 : 0 ≤ k * m * (L - 9)`. Establish `: 0 ≤ L - 9` using `by linarith`.

Check the signs of the components of the expression. Establish `a3 : 0 ≤ m * (k - m) * L`. Establish `: 0 ≤ k - m` using `by linarith`. Check the signs of the components of the expression. Establish `a4 : 0 ≤ k * L` using `by positivity`.

Establish `a5 : m ≤ k * m * L` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hfk : 0 < f * k` using `mul_pos hf hk0`. Establish `: f * k * X ≤ f * k * ((15 + 3 * CY) * m * L)`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `le_of_mul_le_mul_left this hfk`.
-/
theorem log_X_upper_arithmetic (f k m L CY lv l2v SL lg S5 S6 X : ℝ) (hf : 0 < f) (hk : 5 ≤ k) (hm : 44 ≤ m) (hmk : m ≤ k)
    (hL : 9 ≤ L) (hlv0 : 0 ≤ lv) (hlv : lv ≤ L) (h2v : 0 ≤ l2v) (hSL : SL ≤ f * m) (hlg0 : 0 ≤ lg)
    (hlg : lg ≤ 2 * CY * L) (hS5 : S5 ≤ 0)
    (hS6 : S6 ≤ f * (k * m * (2 + 5 * L + 5 * L + 10) + m * (2 * k * L)))
    (id : f * k * X = f * ((m - 1) * k + m * (m - 1) / 2) * lv - f * ((m - 1) / 2) * l2v + SL +
      f * (m * (2 * k + m - 1) / 2) * lg + f * S5 + S6) :
    X ≤ (15 + 3 * CY) * m * L := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 < m := by linarith
  have hL0 : 0 < L := by linarith
  have hCY : 0 ≤ CY := by
    by_contra h
    push_neg at h
    have : 2 * CY * L < 0 := by nlinarith
    linarith
  have ht1 : f * ((m - 1) * k + m * (m - 1) / 2) * lv ≤ f * ((m - 1) * k + m * (m - 1) / 2) * L :=
    mul_le_mul_of_nonneg_left hlv (by have : 0 ≤ (m - 1) * k := by nlinarith
                                      have : 0 ≤ m * (m - 1) / 2 := by nlinarith
                                      positivity)
  have ht2 : 0 ≤ f * ((m - 1) / 2) * l2v := by
    have : 0 ≤ (m - 1) / 2 := by linarith
    positivity
  have ht4 : f * (m * (2 * k + m - 1) / 2) * lg ≤ f * (m * (2 * k + m - 1) / 2) * (2 * CY * L) :=
    mul_le_mul_of_nonneg_left hlg (by have : 0 ≤ m * (2 * k + m - 1) / 2 := by nlinarith
                                      positivity)
  have ht5 : f * S5 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hf.le hS5
  have hsum : f * k * X ≤ f * (((m - 1) * k + m * (m - 1) / 2) * L + m +
      m * (2 * k + m - 1) * CY * L + k * m * (12 + 12 * L)) := by
    rw [id]
    nlinarith
  have hpoly : ((m - 1) * k + m * (m - 1) / 2) * L + m + m * (2 * k + m - 1) * CY * L +
      k * m * (12 + 12 * L) ≤ k * ((15 + 3 * CY) * m * L) := by
    have a1 : 0 ≤ CY * L * m * (k - m + 1) := by
      have : 0 ≤ k - m + 1 := by linarith
      positivity
    have a2 : 0 ≤ k * m * (L - 9) := by
      have : 0 ≤ L - 9 := by linarith
      positivity
    have a3 : 0 ≤ m * (k - m) * L := by
      have : 0 ≤ k - m := by linarith
      positivity
    have a4 : 0 ≤ k * L := by positivity
    have a5 : m ≤ k * m * L := by nlinarith
    nlinarith
  have hfk : 0 < f * k := mul_pos hf hk0
  have : f * k * X ≤ f * k * ((15 + 3 * CY) * m * L) := by
    calc f * k * X ≤ f * (((m - 1) * k + m * (m - 1) / 2) * L + m +
          m * (2 * k + m - 1) * CY * L + k * m * (12 + 12 * L)) := hsum
      _ ≤ f * (k * ((15 + 3 * CY) * m * L)) := mul_le_mul_of_nonneg_left hpoly hf.le
      _ = f * k * ((15 + 3 * CY) * m * L) := by ring
  exact le_of_mul_le_mul_left this hfk

/- English proof (translation)
Take `⟨x0, hx0⟩` from `Filter.eventually_atTop.1 ((tendsto_rpow_atTop heps).eventually_ge_atTop 9)`. Use `⟨x0, fun D sc he hx h2b h2v h3 h4B Δ w hA u => ?_⟩` and prove the remaining obligations. Set `_` to `D.host.cmStar`. Establish `hL9 : 9 ≤ sc.L` using `by unfold Scale.L; rw [he]; exact hx0 sc.x hx`. Take `⟨hB, r1, r2, r3, r4, r5, r6, -, -⟩` from `hA`.

Establish `hgap` using `(h4B Δ w hB).2.1`. Establish `id` using `identity_five_one_of_aux2b_of_aux2v D h2b h2v u`. Establish `hkN` using `D.R.k_ge`. Establish `hmN` using `D.R.two_le_m`. Establish `er : D.R.r = D.R.k + D.R.m - 1` using `rfl`.

Establish `hk5 : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hkN`. Establish `hm44 : (44 : ℝ) ≤ D.R.m` using `by exact_mod_cast r3`. Establish `hmk : (D.R.m : ℝ) ≤ D.R.k` using `by exact_mod_cast r4`. Establish `hf : (0 : ℝ) < D.R.f` using `by exact_mod_cast degree_pos_alt D`. Establish `hv` using `host_v_pos D`.

Establish `hpi` using `hB.1`. Establish `hpi3 : (3 : ℝ) < Real.pi` using `Real.pi_gt_three`. Establish `hlv0 : 0 ≤ Real.log (D.host.v / Real.pi)` using `Real.log_nonneg ((one_le_div Real.pi_pos).2 hpi)`. Establish `hlv : Real.log (D.host.v / Real.pi) ≤ sc.L`. Use `le_trans (Real.log_le_log (div_pos hv Real.pi_pos) ?_) hB.2.1` and prove the remaining obligations.

Rewrite using `[div_le_iff₀ Real.pi_pos]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2v0 : 0 ≤ Real.log (2 * D.host.v)` using `Real.log_nonneg (by linarith)`. Establish `hcard : ((Finset.Ioc D.R.k D.R.r).card : ℝ) ≤ D.R.m`. Rewrite using `[Nat.card_Ioc]; exact_mod_cast (by omega : D.R.r - D.R.k ≤ D.R.m)`.

Establish `hSL : ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) ≤ (D.R.f : ℝ) * D.R.m`. Establish `h1 : ∀ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) ≤ (D.R.f : ℝ)`. Introduce `M hM`. Establish `hM2 : 2 ≤ M` using `by have := (Finset.mem_Ioc.1 hM).1; omega`. Establish `a` using `massIdentity_holds D M hM2`.

Establish `b` using `Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one M hM2`. Rewrite `b` using `[← zetaR_eq]`. Establish `c` using `mul_le_mul_of_nonneg_left b hf.le`. Combine the linear relations using `[le_abs_self (Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M))]`. Establish `h2` using `Finset.sum_le_card_nsmul _ _ _ h1`.

Rewrite `h2` using `[nsmul_eq_mul]`. Establish `h3` using `mul_le_mul_of_nonneg_right hcard hf.le`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg1 : ∀ i, (1 : ℝ) ≤ (D.host.g i : ℝ)` using `fun i => by exact_mod_cast (D.host.g_prime i).one_lt.le`. Establish `elg : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) = Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ)` using `Real.log_mul (by linarith [hg1 0]) (by linarith [hg1 1])`.

Establish `hlg0 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))`. Rewrite using `[elg]`. Combine the linear relations using `[Real.log_nonneg (hg1 0), Real.log_nonneg (hg1 1)]`. Establish `hlg : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ 2 * CY * sc.L`. Rewrite using `[elg]`.

Combine the linear relations using `[r2 0, r2 1]`. Establish `hS5 : ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ≤ 0`. Use `Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j hj => ?_` and prove the remaining obligations. Establish `hj1 : 1 ≤ j` using `by have := (Finset.mem_Ioc.1 hj).1; omega`. Establish `p` using `one_sub_inv_pow_pos (D.host.g i) (D.host.g_prime i).two_le j hj1`.

Use `Real.log_nonpos p.le ?_` and prove the remaining obligations. Establish `: 0 ≤ ((D.host.g i : ℝ) ^ j)⁻¹` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl3 : Real.log 3 ≤ 2`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith` as an intermediate fact.

Establish `hrR : (D.R.r : ℝ) ≤ 2 * D.R.k`. Establish `: D.R.r ≤ 2 * D.R.k` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hr1 : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast (by omega : 1 ≤ D.R.r)`. Establish `hlr : Real.log (D.R.r : ℝ) ≤ sc.L` using `le_trans (Real.log_le_log (by linarith) hrR) r6`.

Establish `hlr0 : 0 ≤ Real.log (D.R.r : ℝ)` using `Real.log_nonneg hr1`. Establish `hrlr : (D.R.r : ℝ) * Real.log (D.R.r : ℝ) ≤ 2 * D.R.k * sc.L` using `mul_le_mul hrR hlr hlr0 (by linarith)`. Establish `hrk : ((D.R.r - D.R.k : ℕ) : ℝ) ≤ D.R.m` using `by exact_mod_cast (by omega : D.R.r - D.R.k ≤ D.R.m)`. Establish `hS6 : ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤ (D.R.f : ℝ) * ((D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10) + D.R.m * (2 * D.R.k * sc.L))`. Establish `h1 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau), Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤ (D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10) + D.R.m * (2 * D.R.k * sc.L)`.

Introduce `ρ _`. Establish `hdim` using `dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)`. Establish `hV : 0 < vand (uColR D u ρ)`. Unfold `dimV at hdim`. Conclude with `(div_pos_iff_of_pos_right (facProd_pos' _)).1 hdim`.

Establish `e1 : Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) = (Real.log (D.dsig ρ) - Real.log (dimV (uColR D u ρ))) + (Real.log (facProd D.R.r) - Real.log (facProd D.R.k))`. Unfold `dimV`. Rewrite using `[Real.log_div (mul_pos (D.dsig_pos ρ) (facProd_pos' _)).ne' hV.ne', Real.log_mul (D.dsig_pos ρ).ne' (facProd_pos' _).ne', Real.log_div hV.ne' (facProd_pos' _).ne']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`.

Establish `a` using `place_dimension_upper_bound D sc C0 Δ w hB h3 hgap u ρ`. Establish `b` using `log_factorial_product_difference D.R.k D.R.r (by omega) (by omega)`. Establish `hkm : 0 ≤ (D.R.k : ℝ) * D.R.m` using `by positivity`. Establish `a' : (D.R.k : ℝ) * D.R.m * (Real.log 3 + 5 * Real.log (2 * D.R.k) + 5 * sc.L + 10) ≤ (D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10)` using `mul_le_mul_of_nonneg_left (by linarith) hkm`. Establish `b' : ((D.R.r - D.R.k : ℕ) : ℝ) * ((D.R.r : ℝ) * Real.log (D.R.r : ℝ)) ≤ D.R.m * (2 * D.R.k * sc.L)` using `mul_le_mul hrk hrlr (mul_nonneg (by linarith) hlr0) (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `Finset.sum_le_card_nsmul _ _ _ h1`. Rewrite `h2` using `[Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`. Conclude with `h2`. Conclude with `log_X_upper_arithmetic (D.R.f : ℝ) D.R.k D.R.m sc.L CY _ _ _ _ _ _ _ hf hk5 hm44 hmk hL9 hlv0 hlv h2v0 hSL hlg0 hlg hS5 hS6 id`.
-/
theorem logXuD_upper_bound_eventually (eps C0 CY : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ (D : D7) (sc : Scale), sc.eps = eps → x0 ≤ sc.x → MassRatio₂ D → VolumeEqMass₂ D → SigmaDegreeTwoSidedBoundOfGap D →
      PartFourSectionBData D sc 8192 C0 → ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataA D sc C0 CY Δ w → ∀ u : D.what₂.Word,
        logXuD D u ≤ (15 + 3 * CY) * D.R.m * sc.L := by
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((tendsto_rpow_atTop heps).eventually_ge_atTop 9)
  refine ⟨x0, fun D sc he hx h2b h2v h3 h4B Δ w hA u => ?_⟩
  let _ := D.host.cmStar
  have hL9 : 9 ≤ sc.L := by unfold Scale.L; rw [he]; exact hx0 sc.x hx
  obtain ⟨hB, r1, r2, r3, r4, r5, r6, -, -⟩ := hA
  have hgap := (h4B Δ w hB).2.1
  have id := identity_five_one_of_aux2b_of_aux2v D h2b h2v u
  have hkN := D.R.k_ge
  have hmN := D.R.two_le_m
  have er : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hkN
  have hm44 : (44 : ℝ) ≤ D.R.m := by exact_mod_cast r3
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast r4
  have hf : (0 : ℝ) < D.R.f := by exact_mod_cast degree_pos_alt D
  have hv := host_v_pos D
  have hpi := hB.1
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three

  have hlv0 : 0 ≤ Real.log (D.host.v / Real.pi) := Real.log_nonneg ((one_le_div Real.pi_pos).2 hpi)
  have hlv : Real.log (D.host.v / Real.pi) ≤ sc.L := by
    refine le_trans (Real.log_le_log (div_pos hv Real.pi_pos) ?_) hB.2.1
    rw [div_le_iff₀ Real.pi_pos]; nlinarith
  have h2v0 : 0 ≤ Real.log (2 * D.host.v) := Real.log_nonneg (by linarith)

  have hcard : ((Finset.Ioc D.R.k D.R.r).card : ℝ) ≤ D.R.m := by
    rw [Nat.card_Ioc]; exact_mod_cast (by omega : D.R.r - D.R.k ≤ D.R.m)
  have hSL : ∑ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) ≤ (D.R.f : ℝ) * D.R.m := by
    have h1 : ∀ M ∈ Finset.Ioc D.R.k D.R.r, Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M) ≤ (D.R.f : ℝ) := by
      intro M hM
      have hM2 : 2 ≤ M := by have := (Finset.mem_Ioc.1 hM).1; omega
      have a := massIdentity_holds D M hM2
      have b := Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one M hM2
      rw [← zetaR_eq] at b
      have c := mul_le_mul_of_nonneg_left b hf.le
      linarith [le_abs_self (Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M))]
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    rw [nsmul_eq_mul] at h2
    have h3 := mul_le_mul_of_nonneg_right hcard hf.le
    linarith

  have hg1 : ∀ i, (1 : ℝ) ≤ (D.host.g i : ℝ) := fun i => by exact_mod_cast (D.host.g_prime i).one_lt.le
  have elg : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) =
      Real.log (D.host.g 0 : ℝ) + Real.log (D.host.g 1 : ℝ) :=
    Real.log_mul (by linarith [hg1 0]) (by linarith [hg1 1])
  have hlg0 : 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
    rw [elg]; linarith [Real.log_nonneg (hg1 0), Real.log_nonneg (hg1 1)]
  have hlg : Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ 2 * CY * sc.L := by
    rw [elg]; linarith [r2 0, r2 1]
  have hS5 : ∑ i : Fin 2, ∑ j ∈ Finset.Ioc D.R.k D.R.r, Real.log (1 - ((D.host.g i : ℝ) ^ j)⁻¹) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j hj => ?_
    have hj1 : 1 ≤ j := by have := (Finset.mem_Ioc.1 hj).1; omega
    have p := one_sub_inv_pow_pos (D.host.g i) (D.host.g_prime i).two_le j hj1
    refine Real.log_nonpos p.le ?_
    have : 0 ≤ ((D.host.g i : ℝ) ^ j)⁻¹ := by positivity
    linarith

  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have hrR : (D.R.r : ℝ) ≤ 2 * D.R.k := by
    have : D.R.r ≤ 2 * D.R.k := by omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hlr : Real.log (D.R.r : ℝ) ≤ sc.L := le_trans (Real.log_le_log (by linarith) hrR) r6
  have hlr0 : 0 ≤ Real.log (D.R.r : ℝ) := Real.log_nonneg hr1
  have hrlr : (D.R.r : ℝ) * Real.log (D.R.r : ℝ) ≤ 2 * D.R.k * sc.L :=
    mul_le_mul hrR hlr hlr0 (by linarith)
  have hrk : ((D.R.r - D.R.k : ℕ) : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : D.R.r - D.R.k ≤ D.R.m)
  have hS6 : ∑ ρ, Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤
      (D.R.f : ℝ) * ((D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10) + D.R.m * (2 * D.R.k * sc.L)) := by
    have h1 : ∀ ρ ∈ (Finset.univ : Finset D.what₂.Tau),
        Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) ≤
          (D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10) + D.R.m * (2 * D.R.k * sc.L) := by
      intro ρ _
      have hdim := dim_weyl_pos_of_strictAnti _ (column_param_strictAnti D u ρ)
      have hV : 0 < vand (uColR D u ρ) := by
        unfold dimV at hdim
        exact (div_pos_iff_of_pos_right (facProd_pos' _)).1 hdim
      have e1 : Real.log (D.dsig ρ * facProd D.R.r / vand (uColR D u ρ)) =
          (Real.log (D.dsig ρ) - Real.log (dimV (uColR D u ρ))) +
            (Real.log (facProd D.R.r) - Real.log (facProd D.R.k)) := by
        unfold dimV
        rw [Real.log_div (mul_pos (D.dsig_pos ρ) (facProd_pos' _)).ne' hV.ne',
          Real.log_mul (D.dsig_pos ρ).ne' (facProd_pos' _).ne',
          Real.log_div hV.ne' (facProd_pos' _).ne']
        ring
      rw [e1]
      have a := place_dimension_upper_bound D sc C0 Δ w hB h3 hgap u ρ
      have b := log_factorial_product_difference D.R.k D.R.r (by omega) (by omega)
      have hkm : 0 ≤ (D.R.k : ℝ) * D.R.m := by positivity
      have a' : (D.R.k : ℝ) * D.R.m * (Real.log 3 + 5 * Real.log (2 * D.R.k) + 5 * sc.L + 10) ≤
          (D.R.k : ℝ) * D.R.m * (2 + 5 * sc.L + 5 * sc.L + 10) :=
        mul_le_mul_of_nonneg_left (by linarith) hkm
      have b' : ((D.R.r - D.R.k : ℕ) : ℝ) * ((D.R.r : ℝ) * Real.log (D.R.r : ℝ)) ≤
          D.R.m * (2 * D.R.k * sc.L) :=
        mul_le_mul hrk hrlr (mul_nonneg (by linarith) hlr0) (by linarith)
      linarith
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    rw [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at h2
    exact h2
  exact log_X_upper_arithmetic (D.R.f : ℝ) D.R.k D.R.m sc.L CY _ _ _ _ _ _ _ hf hk5 hm44 hmk hL9 hlv0 hlv h2v0 hSL hlg0 hlg hS5
    hS6 id

end Formalism.MainNotions.StandardLattice
