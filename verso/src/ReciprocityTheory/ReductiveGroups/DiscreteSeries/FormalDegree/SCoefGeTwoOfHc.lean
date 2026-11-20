import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FiPmatEqFiOneSmulPmat

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Establish `h : lam ⟨i + 1, hi⟩ < lam ⟨i, by omega⟩` using `hlam (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))`. Simplify using `only [sCoef, dif_pos hi]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sCoef_gt_one {lam : Fin n → ℝ} (hlam : StrictAnti lam) {i : ℕ} (hi : i + 1 < n) :
    1 < sCoef lam i := by
  have h : lam ⟨i + 1, hi⟩ < lam ⟨i, by omega⟩ := hlam (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
  simp only [sCoef, dif_pos hi]
  linarith

/- English proof (translation)
Establish `h : lam ⟨i + 1, hi⟩ ≤ lam ⟨i, by omega⟩` using `hlam (Fin.mk_le_mk.mpr (Nat.le_succ i))`. Simplify using `only [sCoef, dif_pos hi]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sCoef_ge_one {lam : Fin n → ℝ} (hlam : Antitone lam) {i : ℕ} (hi : i + 1 < n) :
    1 ≤ sCoef lam i := by
  have h : lam ⟨i + 1, hi⟩ ≤ lam ⟨i, by omega⟩ := hlam (Fin.mk_le_mk.mpr (Nat.le_succ i))
  simp only [sCoef, dif_pos hi]
  linarith

/- English proof (translation)
Take `⟨m1, hm1⟩` from `hlam.2 ⟨i, by omega⟩`. Take `⟨m2, hm2⟩` from `hlam.2 ⟨i + 1, hi⟩`. Establish `hlt : lam ⟨i + 1, hi⟩ < lam ⟨i, by omega⟩` using `hlam.1 (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))`. Establish `hd : lam ⟨i, by omega⟩ - lam ⟨i + 1, hi⟩ = ((m1 - m2 : ℤ) : ℝ)` using `by push_cast; linarith`. Establish `hpos : (0 : ℝ) < ((m1 - m2 : ℤ) : ℝ)` using `by rw [← hd]; linarith`.

Establish `h0 : (0 : ℤ) < m1 - m2` using `Int.cast_pos.mp hpos`. Establish `h1 : (1 : ℤ) ≤ m1 - m2` using `by omega`. Establish `h1' : (1 : ℝ) ≤ ((m1 - m2 : ℤ) : ℝ)` using `by exact_mod_cast h1`. Simplify using `only [sCoef, dif_pos hi]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sCoef_ge_two_of_hc {lam : Fin n → ℝ} (hlam : IsHCParam lam) {i : ℕ} (hi : i + 1 < n) :
    2 ≤ sCoef lam i := by
  obtain ⟨m1, hm1⟩ := hlam.2 ⟨i, by omega⟩
  obtain ⟨m2, hm2⟩ := hlam.2 ⟨i + 1, hi⟩
  have hlt : lam ⟨i + 1, hi⟩ < lam ⟨i, by omega⟩ := hlam.1 (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
  have hd : lam ⟨i, by omega⟩ - lam ⟨i + 1, hi⟩ = ((m1 - m2 : ℤ) : ℝ) := by push_cast; linarith
  have hpos : (0 : ℝ) < ((m1 - m2 : ℤ) : ℝ) := by rw [← hd]; linarith
  have h0 : (0 : ℤ) < m1 - m2 := Int.cast_pos.mp hpos
  have h1 : (1 : ℤ) ≤ m1 - m2 := by omega
  have h1' : (1 : ℝ) ≤ ((m1 - m2 : ℤ) : ℝ) := by exact_mod_cast h1
  simp only [sCoef, dif_pos hi]
  linarith

/- English proof (translation)
Establish `hc` using `fi_convex z hi`. Establish `ht0 : 0 < t` using `by linarith`. Establish `h : Fi (((1 / t * t + (1 - 1 / t) * 0 : ℝ) : ℂ) • pmat z) i ≤ 1 / t * Fi (((t : ℝ) : ℂ) • pmat z) i + (1 - 1 / t) * Fi (((0 : ℝ) : ℂ) • pmat z) i` using `hc.2 (Set.mem_univ t) (Set.mem_univ (0 : ℝ)) (show (0 : ℝ) ≤ 1 / t by positivity) (show (0 : ℝ) ≤ 1 - 1 / t by rw [sub_nonneg, div_le_one ht0]; exact ht) (show 1 / t + (1 - 1 / t) = (1 : ℝ) by ring)`. Establish `e1 : 1 / t * t + (1 - 1 / t) * 0 = 1` using `by rw [mul_zero, add_zero, one_div_mul_cancel ht0.ne']`. Establish `e0 : Fi (((0 : ℝ) : ℂ) • pmat z) i = 0` using `by simp [fi_zero]`.

Rewrite `h` using `[e1, e0, Complex.ofReal_one, one_smul, mul_zero, add_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fi_scale {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) {t : ℝ} (ht : 1 ≤ t) :
    t * Fi (pmat z) i ≤ Fi ((t : ℂ) • pmat z) i := by
  have hc := fi_convex z hi
  have ht0 : 0 < t := by linarith
  have h : Fi (((1 / t * t + (1 - 1 / t) * 0 : ℝ) : ℂ) • pmat z) i ≤
      1 / t * Fi (((t : ℝ) : ℂ) • pmat z) i + (1 - 1 / t) * Fi (((0 : ℝ) : ℂ) • pmat z) i :=
    hc.2 (Set.mem_univ t) (Set.mem_univ (0 : ℝ)) (show (0 : ℝ) ≤ 1 / t by positivity)
      (show (0 : ℝ) ≤ 1 - 1 / t by rw [sub_nonneg, div_le_one ht0]; exact ht)
      (show 1 / t + (1 - 1 / t) = (1 : ℝ) by ring)
  have e1 : 1 / t * t + (1 - 1 / t) * 0 = 1 := by rw [mul_zero, add_zero, one_div_mul_cancel ht0.ne']
  have e0 : Fi (((0 : ℝ) : ℂ) • pmat z) i = 0 := by simp [fi_zero]
  rw [e1, e0, Complex.ofReal_one, one_smul, mul_zero, add_zero] at h
  calc t * Fi (pmat z) i ≤ t * (1 / t * Fi ((t : ℂ) • pmat z) i) := mul_le_mul_of_nonneg_left h ht0.le
    _ = Fi ((t : ℂ) • pmat z) i := by rw [← mul_assoc, mul_one_div_cancel ht0.ne', one_mul]

/- English proof (translation)
Unfold `Ph`. Use `Finset.sum_nonneg fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i + 1 < n` using `by have := Finset.mem_range.mp hi; omega`. Conclude with `mul_nonneg (by linarith [sCoef_ge_one hlam hi']) (fi_nonneg z _)`.
-/
theorem ph_nonneg {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (z : PCoord ε → ℂ) :
    0 ≤ Ph lam (pmat z) := by
  unfold Ph
  refine Finset.sum_nonneg fun i hi => ?_
  have hi' : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  exact mul_nonneg (by linarith [sCoef_ge_one hlam hi']) (fi_nonneg z _)

/- English proof (translation)
Unfold `Ph`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i + 1 < n` using `by have := Finset.mem_range.mp hi; omega`. Establish `hs` using `sCoef_ge_one hlam hi'`.

Establish `hf` using `fi_scale z (i := i + 1) (by omega) ht`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ph_scale {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (z : PCoord ε → ℂ) {t : ℝ}
    (ht : 1 ≤ t) : t * Ph lam (pmat z) ≤ Ph lam ((t : ℂ) • pmat z) := by
  unfold Ph
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  have hs := sCoef_ge_one hlam hi'
  have hf := fi_scale z (i := i + 1) (by omega) ht
  calc t * (sCoef lam i * Fi (pmat z) (i + 1)) = sCoef lam i * (t * Fi (pmat z) (i + 1)) := by ring
    _ ≤ sCoef lam i * Fi ((t : ℂ) • pmat z) (i + 1) := mul_le_mul_of_nonneg_left hf (by linarith)

/- English proof (translation)
Proceed by induction on `a, hba using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ k hbk ih`. Rewrite using `[Finset.sum_Ico_succ_top hbk, ih (by omega)]`. Simplify using `only [sCoef, dif_pos ha]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_Ico_sCoef (lam : Fin n → ℝ) {b a : ℕ} (hba : b ≤ a) (ha : a < n) :
    ∑ i ∈ Ico b a, sCoef lam i = lam ⟨b, by omega⟩ - lam ⟨a, ha⟩ + ((a : ℝ) - (b : ℝ)) := by
  induction a, hba using Nat.le_induction with
  | base => simp
  | succ k hbk ih =>
    rw [Finset.sum_Ico_succ_top hbk, ih (by omega)]
    simp only [sCoef, dif_pos ha]
    push_cast
    ring

/- English proof (translation)
Rewrite using `[sum_Ico_sCoef lam (Fin.le_iff_val_le_val.mp h) a.isLt]`. Simplify using `only [Fin.eta, wab]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_Ico_sCoef_fin (lam : Fin n → ℝ) (a b : Fin n) (h : b ≤ a) :
    ∑ i ∈ Ico (b : ℕ) a, sCoef lam i = wab lam a b := by
  rw [sum_Ico_sCoef lam (Fin.le_iff_val_le_val.mp h) a.isLt]
  simp only [Fin.eta, wab]
  ring

/- English proof (translation)
Repeatedly rewrite using `[mul_ite, mul_zero]`. Rewrite using `[← Finset.sum_filter, ← Finset.sum_mul]`. Establish `ha` using `a.isLt`. Establish `hf : (range (n - 1)).filter (fun i => (b : ℕ) < i + 1 ∧ i + 1 ≤ (a : ℕ)) = Ico (b : ℕ) a`. Use extensionality with `i`.

Simplify using `only [mem_filter, mem_range, mem_Ico]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hf]`. Use `split_ifs with h`. Rewrite using `[sum_Ico_sCoef_fin lam a b h.le]`.

Establish `h' : (a : ℕ) ≤ b` using `Fin.le_iff_val_le_val.mp (not_lt.mp h)`. Rewrite using `[Finset.Ico_eq_empty_of_le h', sum_empty, zero_mul]`.
-/
theorem sum_sCoef_ind (lam : Fin n → ℝ) (a b : Fin n) (c : ℝ) :
    ∑ i ∈ range (n - 1), sCoef lam i * (if (b : ℕ) < i + 1 ∧ i + 1 ≤ (a : ℕ) then c else 0) =
      if b < a then wab lam a b * c else 0 := by
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  have ha := a.isLt
  have hf : (range (n - 1)).filter (fun i => (b : ℕ) < i + 1 ∧ i + 1 ≤ (a : ℕ)) = Ico (b : ℕ) a := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hf]
  split_ifs with h
  · rw [sum_Ico_sCoef_fin lam a b h.le]
  · have h' : (a : ℕ) ≤ b := Fin.le_iff_val_le_val.mp (not_lt.mp h)
    rw [Finset.Ico_eq_empty_of_le h', sum_empty, zero_mul]

/- English proof (translation)
Unfold `pmat`. Rewrite using `[dif_pos ab.2]`.
-/
theorem pmat_coord {ε : Fin n → Bool} (z : PCoord ε → ℂ) (ab : PCoord ε) :
    pmat z ab.1.1 ab.1.2 = z ab := by
  unfold pmat
  rw [dif_pos ab.2]

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_of_ne (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2)]`. Rewrite using `[Finset.sum_subtype (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2) _ (by simp)]`. Use `Finset.sum_congr rfl fun ab _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos ab.2.1, pmat_coord]`. Introduce `x _ hx`.

Assume the negation of the conclusion as `hP`. Apply `hx` to reduce the goal to its premises. Distinguish the cases in `h1 : x.2 < x.1`. Establish `h2 : ε x.1 = ε x.2`. Assume the negation of the conclusion as `h`.

Conclude with `hP ⟨h1, h⟩`. Establish `h3 : pmat z x.1 x.2 = 0`. Unfold `pmat`. Rewrite using `[dif_neg (fun h => h.2 h2), dif_neg (fun h => lt_asymm h.1 h1)]`. Rewrite using `[if_pos h1, h3, norm_zero]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h1]`.
-/
theorem sum_pairs_pmat {ε : Fin n → Bool} (w : Fin n → Fin n → ℝ) (z : PCoord ε → ℂ) :
    ∑ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) =
      ∑ ab : PCoord ε, w ab.1.1 ab.1.2 * ‖z ab‖ ^ 2 := by
  rw [← Finset.sum_filter_of_ne (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2)]
  · rw [Finset.sum_subtype (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2) _ (by simp)]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [if_pos ab.2.1, pmat_coord]
  · intro x _ hx
    by_contra hP
    apply hx
    by_cases h1 : x.2 < x.1
    · have h2 : ε x.1 = ε x.2 := by
        by_contra h
        exact hP ⟨h1, h⟩
      have h3 : pmat z x.1 x.2 = 0 := by
        unfold pmat
        rw [dif_neg (fun h => h.2 h2), dif_neg (fun h => lt_asymm h.1 h1)]
      rw [if_pos h1, h3, norm_zero]
      ring
    · rw [if_neg h1]

/- English proof (translation)
Establish `step1 : ∑ i ∈ range (n - 1), sCoef lam i * Vi (pmat z) (i + 1) = ∑ a : Fin n, ∑ b : Fin n, if b < a then wab lam a b * ‖pmat z a b‖ ^ 2 else 0`. Simplify using `only [Vi, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Conclude with `sum_sCoef_ind lam a b _`. Rewrite using `[step1, ← Fintype.sum_prod_type', Qf]`. Conclude with `sum_pairs_pmat (wab lam) z`.
-/
theorem sum_sCoef_Vi {ε : Fin n → Bool} (lam : Fin n → ℝ) (z : PCoord ε → ℂ) :
    ∑ i ∈ range (n - 1), sCoef lam i * Vi (pmat z) (i + 1) = Qf lam z := by
  have step1 : ∑ i ∈ range (n - 1), sCoef lam i * Vi (pmat z) (i + 1) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then wab lam a b * ‖pmat z a b‖ ^ 2 else 0 := by
    simp only [Vi, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact sum_sCoef_ind lam a b _
  rw [step1, ← Fintype.sum_prod_type', Qf]
  exact sum_pairs_pmat (wab lam) z

/- English proof (translation)
Take `⟨⟨a, b⟩, hba, hne⟩` from `ab`. Use `show h0 + 1 ≤ wab lam a b`. Establish `h1` using `hgap a b hne`. Establish `h2 : lam a < lam b` using `hlam hba`. Establish `hv : (b : ℕ) + 1 ≤ (a : ℕ)` using `Fin.lt_def.mp hba`.

Establish `h3 : ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ)` using `by exact_mod_cast hv`. Rewrite `h1` using `[abs_of_neg (by linarith)]`. Simplify using `only [wab]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wab_lower {ε : Fin n → Bool} {lam : Fin n → ℝ} {h0 : ℝ} (hlam : StrictAnti lam)
    (hgap : GapAtLeast ε lam h0) (ab : PCoord ε) : h0 + 1 ≤ wab lam ab.1.1 ab.1.2 := by
  obtain ⟨⟨a, b⟩, hba, hne⟩ := ab
  show h0 + 1 ≤ wab lam a b
  have h1 := hgap a b hne
  have h2 : lam a < lam b := hlam hba
  have hv : (b : ℕ) + 1 ≤ (a : ℕ) := Fin.lt_def.mp hba
  have h3 : ((b : ℕ) : ℝ) + 1 ≤ ((a : ℕ) : ℝ) := by exact_mod_cast hv
  rw [abs_of_neg (by linarith)] at h1
  simp only [wab]
  linarith

/- English proof (translation)
Unfold `lamAbs`. Conclude with `le_ciSup_of_le (Set.finite_range (fun a => ⨆ b, |lam a - lam b|)).bddAbove a (le_ciSup (Set.finite_range (fun b => |lam a - lam b|)).bddAbove b)`.
-/
theorem abs_le_lamAbs (lam : Fin n → ℝ) (a b : Fin n) : |lam a - lam b| ≤ lamAbs lam := by
  unfold lamAbs
  exact le_ciSup_of_le (Set.finite_range (fun a => ⨆ b, |lam a - lam b|)).bddAbove a
    (le_ciSup (Set.finite_range (fun b => |lam a - lam b|)).bddAbove b)

/- English proof (translation)
Take `⟨⟨a, b⟩, hba, -⟩` from `ab`. Use `show wab lam a b ≤ 2 * lamAbs lam`. Establish `hle : (b : ℕ) ≤ a` using `le_of_lt (Fin.lt_def.mp hba)`. Establish `ha` using `a.isLt`. Establish `hw` using `sum_Ico_sCoef_fin lam a b (le_of_lt hba)`.

Establish `hsum : #(Ico (b : ℕ) a) • (2 : ℝ) ≤ ∑ i ∈ Ico (b : ℕ) a, sCoef lam i` using `Finset.card_nsmul_le_sum _ _ _ fun i hi => sCoef_ge_two_of_hc hlam (by`. Use `Finset.mem_Ico.mp hi` as an intermediate fact. Use the proof step `omega)`. Rewrite `hsum` using `[hw, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hle]`. Establish `hab` using `abs_le_lamAbs lam b a`.

Use `le_abs_self (lam b - lam a)` as an intermediate fact. Simplify using `only [wab] at hsum ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wab_upper {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : IsHCParam lam) (ab : PCoord ε) :
    wab lam ab.1.1 ab.1.2 ≤ 2 * lamAbs lam := by
  obtain ⟨⟨a, b⟩, hba, -⟩ := ab
  show wab lam a b ≤ 2 * lamAbs lam
  have hle : (b : ℕ) ≤ a := le_of_lt (Fin.lt_def.mp hba)
  have ha := a.isLt
  have hw := sum_Ico_sCoef_fin lam a b (le_of_lt hba)
  have hsum : #(Ico (b : ℕ) a) • (2 : ℝ) ≤ ∑ i ∈ Ico (b : ℕ) a, sCoef lam i :=
    Finset.card_nsmul_le_sum _ _ _ fun i hi => sCoef_ge_two_of_hc hlam (by
      have := Finset.mem_Ico.mp hi
      omega)
  rw [hw, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hle] at hsum
  have hab := abs_le_lamAbs lam b a
  have := le_abs_self (lam b - lam a)
  simp only [wab] at hsum ⊢
  linarith

/- English proof (translation)
Rewrite using `[hs_pmat]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[show (h0 + 1) * (2 * ∑ ab, ‖z ab‖ ^ 2) / 2 = (h0 + 1) * ∑ ab, ‖z ab‖ ^ 2 by ring, Finset.mul_sum, Qf]`. Conclude with `Finset.sum_le_sum fun ab _ => mul_le_mul_of_nonneg_right (wab_lower hlam.1 hgap ab) (by positivity)`. Rewrite using `[show lamAbs lam * (2 * ∑ ab, ‖z ab‖ ^ 2) = (2 * lamAbs lam) * ∑ ab, ‖z ab‖ ^ 2 by ring, Finset.mul_sum, Qf]`.

Conclude with `Finset.sum_le_sum fun ab _ => mul_le_mul_of_nonneg_right (wab_upper hlam ab) (by positivity)`.
-/
theorem qf_bounds {ε : Fin n → Bool} {lam : Fin n → ℝ} {h0 : ℝ} (hlam : IsHCParam lam)
    (hgap : GapAtLeast ε lam h0) (z : PCoord ε → ℂ) :
    (h0 + 1) * hs (pmat z) / 2 ≤ Qf lam z ∧ Qf lam z ≤ lamAbs lam * hs (pmat z) := by
  rw [hs_pmat]
  constructor
  · rw [show (h0 + 1) * (2 * ∑ ab, ‖z ab‖ ^ 2) / 2 = (h0 + 1) * ∑ ab, ‖z ab‖ ^ 2 by ring,
      Finset.mul_sum, Qf]
    exact Finset.sum_le_sum fun ab _ =>
      mul_le_mul_of_nonneg_right (wab_lower hlam.1 hgap ab) (by positivity)
  · rw [show lamAbs lam * (2 * ∑ ab, ‖z ab‖ ^ 2) = (2 * lamAbs lam) * ∑ ab, ‖z ab‖ ^ 2 by ring,
      Finset.mul_sum, Qf]
    exact Finset.sum_le_sum fun ab _ =>
      mul_le_mul_of_nonneg_right (wab_upper hlam ab) (by positivity)

/- English proof (translation)
Rewrite using `[← sum_sCoef_Vi lam z, Ph, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i + 1 < n` using `by have := Finset.mem_range.mp hi; omega`. Establish `hs` using `sCoef_ge_one hlam hi'`. Establish `hf` using `fi_lower z (i := i + 1) (by omega) h1 h2`.

Use `mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ sCoef lam i by linarith)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ph_lower {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (z : PCoord ε → ℂ) {ep : ℝ}
    (h1 : rhoP z ≤ ep) (h2 : ep ≤ 1) : (1 - ep) * Qf lam z ≤ 2 * Ph lam (pmat z) := by
  rw [← sum_sCoef_Vi lam z, Ph, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  have hs := sCoef_ge_one hlam hi'
  have hf := fi_lower z (i := i + 1) (by omega) h1 h2
  have := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ sCoef lam i by linarith)
  nlinarith

/- English proof (translation)
Rewrite using `[← sum_sCoef_Vi lam z, Ph]`. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i + 1 < n` using `by have := Finset.mem_range.mp hi; omega`. Establish `hs` using `sCoef_ge_one hlam hi'`. Conclude with `mul_le_mul_of_nonneg_left (fi_upper z (by omega) h1) (by linarith)`.
-/
theorem ph_upper {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (z : PCoord ε → ℂ)
    (h1 : rhoP z ≤ 1) : Ph lam (pmat z) ≤ Qf lam z := by
  rw [← sum_sCoef_Vi lam z, Ph]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  have hs := sCoef_ge_one hlam hi'
  exact mul_le_mul_of_nonneg_left (fi_upper z (by omega) h1) (by linarith)

end ReciprocityTheory.ChartRestriction.DS
