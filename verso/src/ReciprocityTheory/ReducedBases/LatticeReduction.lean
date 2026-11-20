import ReciprocityTheory.ReducedBases.GsInnerBOfLt
import ReciprocityTheory.ReducedBases.ExistsBoundedBasis

noncomputable section

namespace ReciprocityTheory.ReducedBases.T2

open Finset InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

def IsRed (b : Fin d → E) : Prop :=
  LinearIndependent ℝ b ∧ (∀ i j : Fin d, j < i → |mu b i j| ≤ 1 / 2) ∧
    (∀ i j : Fin d, i.val = j.val + 1 → ‖gs b j‖ ^ 2 ≤ 2 * ‖gs b i‖ ^ 2)

/- English proof (translation)
Simplify using `only [nu, sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]`.
-/
lemma nu_sub (b : Fin d → E) (c w : Fin d → ℝ) (N : ℝ) (j : Fin d) :
    nu b (fun l => c l - N * w l) j = nu b c j - N * nu b w j := by
  simp only [nu, sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]

/- English proof (translation)
Unfold `nu`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Break down `lt_or_ge l j with hlj | hjl` into its components or cases. Establish `h0 : ⟪gs b j, b l⟫_ℝ = 0` using `by first`.

Consider the case `exact gramSchmidt_inv_triangular ℝ b hlj`. Consider the case `exact gramSchmidt_inv_triangular b hlj`. Simplify using `[mu, h0]`. Simplify using `[h l hjl]`.
-/
lemma nu_eq_zero_of (b : Fin d → E) (c : Fin d → ℝ) (j : Fin d) (h : ∀ l, j ≤ l → c l = 0) :
    nu b c j = 0 := by
  unfold nu
  apply Finset.sum_eq_zero
  intro l _
  rcases lt_or_ge l j with hlj | hjl
  · have h0 : ⟪gs b j, b l⟫_ℝ = 0 := by
      first
      | exact gramSchmidt_inv_triangular ℝ b hlj
      | exact gramSchmidt_inv_triangular b hlj
    simp [mu, h0]
  · simp [h l hjl]

/- English proof (translation)
Establish `e : ⟪gs b j, b j⟫_ℝ = ‖gs b j‖ ^ 2` using `by conv_lhs => rw [gramSchmidt_def'' ℝ b j]`. Rewrite using `[inner_add_right, inner_sum, real_inner_self_eq_norm_sq, Finset.sum_eq_zero, add_zero]`. Introduce `i hi`. Rewrite using `[inner_smul_right, gramSchmidt_orthogonal ℝ b (ne_of_gt (Finset.mem_Iio.mp hi)), mul_zero]`. Establish `hne : gs b j ≠ 0` using `by first`.

Consider the case `exact gramSchmidt_ne_zero j hb`. Consider the case `exact gramSchmidt_ne_zero (𝕜 := ℝ) j hb`. Rewrite using `[mu, e]`. Conclude with `div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))`.
-/
private lemma mu_self_of_linearIndependent (b : Fin d → E) (hb : LinearIndependent ℝ b) (j : Fin d) :
    mu b j j = 1 := by
  have e : ⟪gs b j, b j⟫_ℝ = ‖gs b j‖ ^ 2 := by
    conv_lhs => rw [gramSchmidt_def'' ℝ b j]
    rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq, Finset.sum_eq_zero, add_zero]
    intro i hi
    rw [inner_smul_right, gramSchmidt_orthogonal ℝ b (ne_of_gt (Finset.mem_Iio.mp hi)), mul_zero]
  have hne : gs b j ≠ 0 := by
    first
    | exact gramSchmidt_ne_zero j hb
    | exact gramSchmidt_ne_zero (𝕜 := ℝ) j hb
  rw [mu, e]
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))

/- English proof (translation)
Unfold `nu`. Rewrite using `[← Finset.sum_filter_add_sum_filter_not univ (fun l : Fin d => j.val + 1 ≤ l.val), add_comm]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[mu_self_of_linearIndependent b hb j, mul_one]`.

Introduce `l hl hlj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hl`. Establish `h1 : l.val ≠ j.val` using `fun h => hlj (Fin.ext h)`. Establish `hlt : l < j` using `Fin.lt_iff_val_lt_val.mpr (by omega)`. Establish `h0 : ⟪gs b j, b l⟫_ℝ = 0` using `by first`.

Consider the case `exact gramSchmidt_inv_triangular ℝ b hlt`. Consider the case `exact gramSchmidt_inv_triangular b hlt`. Simplify using `[mu, h0]`. Introduce `hj`. It suffices to derive a contradiction.

Apply `hj` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
private lemma nu_eq_add_sum_mu (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) (j : Fin d) :
    nu b c j = c j + ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), c l * mu b l j := by
  unfold nu
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun l : Fin d => j.val + 1 ≤ l.val), add_comm]
  congr 1
  rw [Finset.sum_eq_single j]
  · rw [mu_self_of_linearIndependent b hb j, mul_one]
  · intro l hl hlj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hl
    have h1 : l.val ≠ j.val := fun h => hlj (Fin.ext h)
    have hlt : l < j := Fin.lt_iff_val_lt_val.mpr (by omega)
    have h0 : ⟪gs b j, b l⟫_ℝ = 0 := by
      first
      | exact gramSchmidt_inv_triangular ℝ b hlt
      | exact gramSchmidt_inv_triangular b hlt
    simp [mu, h0]
  · intro hj
    exfalso
    apply hj
    simp

/- English proof (translation)
Rewrite using `[nu_eq_add_sum_mu b hb c j, Finset.sum_eq_zero, add_zero]`. Introduce `l hl`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hl`. Rewrite using `[h l (Fin.lt_iff_val_lt_val.mpr (by omega)), zero_mul]`.
-/
lemma nu_top (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) (j : Fin d)
    (h : ∀ l, j < l → c l = 0) : nu b c j = c j := by
  rw [nu_eq_add_sum_mu b hb c j, Finset.sum_eq_zero, add_zero]
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  rw [h l (Fin.lt_iff_val_lt_val.mpr (by omega)), zero_mul]

/- English proof (translation)
Conclude with `nu_eq_add_sum_mu b hb c j`.
-/
lemma nu_split (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) (j : Fin d) :
    nu b c j = c j + ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), c l * mu b l j := by
  exact nu_eq_add_sum_mu b hb c j

/- English proof (translation)
Proceed by induction on `t generalizing c with`. Consider the case `zero`. Conclude with `⟨0, fun l _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩`. Consider the case `succ t ih`. Establish `htd : t < d` using `by omega`.

Take `⟨k, hk⟩ : ∃ k : ℤ, k = round (nu b c ⟨t, htd⟩ / N)` from `⟨_, rfl⟩`. Take `⟨w, hw0, hw⟩` from `ih (fun l => c l - N * (if l = ⟨t, htd⟩ then (k : ℝ) else 0)) (by omega)`. Use `⟨fun l => w l + if l = ⟨t, htd⟩ then k else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `l hl`. Establish `hne : l ≠ ⟨t, htd⟩`.

Introduce `h`. Rewrite `hl` using `[h]`. Simplify using `at hl`. Simplify using `[hw0 l (by omega), hne]`. Introduce `j hj`.

Establish `hnu : nu b (fun l => c l - N * ((w l + if l = ⟨t, htd⟩ then k else 0 : ℤ) : ℝ)) j = nu b (fun l => (c l - N * (if l = ⟨t, htd⟩ then (k : ℝ) else 0)) - N * (w l : ℝ)) j`. Use `congr 1`. Use function extensionality and compare the values at `l`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`. Distinguish the cases in `hjt : j.val < t`.

Conclude with `(le_of_eq (congrArg abs hnu)).trans (hw j hjt)`. Take `rfl : j = ⟨t, htd⟩` from `Fin.ext (by simp; omega)`. Establish `hval : nu b (fun l => c l - N * ((w l + if l = ⟨t, htd⟩ then k else 0 : ℤ) : ℝ)) ⟨t, htd⟩ = nu b c ⟨t, htd⟩ - N * (k : ℝ)`. Rewrite using `[hnu, nu_sub, nu_eq_zero_of b (fun l => ((w l : ℤ) : ℝ)) ⟨t, htd⟩ (fun l hl => by simp [hw0 l hl]), mul_zero, sub_zero, nu_sub, nu_top b hb (fun l => if l = ⟨t, htd⟩ then (k : ℝ) else 0) ⟨t, htd⟩ (fun l hl => if_neg (ne_of_gt hl))]`. Simplify using the standard rewrite rules.

Establish `hN0 : N ≠ 0` using `hN.ne'`. Establish `hr` using `abs_sub_round (nu b c ⟨t, htd⟩ / N)`. Establish `e3 : N * (nu b c ⟨t, htd⟩ / N) = nu b c ⟨t, htd⟩` using `by field_simp`. Establish `e2 : nu b c ⟨t, htd⟩ - N * (k : ℝ) = N * (nu b c ⟨t, htd⟩ / N - (round (nu b c ⟨t, htd⟩ / N) : ℝ))`. Rewrite using `[hk, mul_sub, e3]`.

Rewrite using `[hval, e2, abs_mul, abs_of_pos hN]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma babai (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ) {N : ℝ} (hN : 0 < N)
    (t : ℕ) (ht : t ≤ d) : ∃ w : Fin d → ℤ, (∀ l : Fin d, t ≤ l.val → w l = 0) ∧
      ∀ j : Fin d, j.val < t → |nu b (fun l => c l - N * (w l : ℝ)) j| ≤ N / 2 := by
  induction t generalizing c with
  | zero =>
    exact ⟨0, fun l _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ t ih =>
    have htd : t < d := by omega
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round (nu b c ⟨t, htd⟩ / N) := ⟨_, rfl⟩
    obtain ⟨w, hw0, hw⟩ := ih (fun l => c l - N * (if l = ⟨t, htd⟩ then (k : ℝ) else 0)) (by omega)
    refine ⟨fun l => w l + if l = ⟨t, htd⟩ then k else 0, ?_, ?_⟩
    · intro l hl
      have hne : l ≠ ⟨t, htd⟩ := by
        intro h
        rw [h] at hl
        simp at hl
      simp [hw0 l (by omega), hne]
    · intro j hj
      have hnu : nu b (fun l => c l - N * ((w l + if l = ⟨t, htd⟩ then k else 0 : ℤ) : ℝ)) j =
          nu b (fun l => (c l - N * (if l = ⟨t, htd⟩ then (k : ℝ) else 0)) - N * (w l : ℝ)) j := by
        congr 1
        funext l
        split_ifs <;> push_cast <;> ring
      by_cases hjt : j.val < t
      · exact (le_of_eq (congrArg abs hnu)).trans (hw j hjt)
      · obtain rfl : j = ⟨t, htd⟩ := Fin.ext (by simp; omega)
        have hval : nu b (fun l => c l - N * ((w l + if l = ⟨t, htd⟩ then k else 0 : ℤ) : ℝ)) ⟨t, htd⟩ =
            nu b c ⟨t, htd⟩ - N * (k : ℝ) := by
          rw [hnu, nu_sub, nu_eq_zero_of b (fun l => ((w l : ℤ) : ℝ)) ⟨t, htd⟩
            (fun l hl => by simp [hw0 l hl]), mul_zero, sub_zero, nu_sub,
            nu_top b hb (fun l => if l = ⟨t, htd⟩ then (k : ℝ) else 0) ⟨t, htd⟩
              (fun l hl => if_neg (ne_of_gt hl))]
          simp
        have hN0 : N ≠ 0 := hN.ne'
        have hr := abs_sub_round (nu b c ⟨t, htd⟩ / N)
        have e3 : N * (nu b c ⟨t, htd⟩ / N) = nu b c ⟨t, htd⟩ := by field_simp
        have e2 : nu b c ⟨t, htd⟩ - N * (k : ℝ) =
            N * (nu b c ⟨t, htd⟩ / N - (round (nu b c ⟨t, htd⟩ / N) : ℝ)) := by
          rw [hk, mul_sub, e3]
        rw [hval, e2, abs_mul, abs_of_pos hN]
        calc N * |nu b c ⟨t, htd⟩ / N - (round (nu b c ⟨t, htd⟩ / N) : ℝ)| ≤ N * (1 / 2) :=
              mul_le_mul_of_nonneg_left hr hN.le
          _ = N / 2 := by ring

/- English proof (translation)
Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers.
-/
lemma filter_le_succ (n : ℕ) (h : n + 1 < d) :
    univ.filter (fun j : Fin d => j.val ≤ n + 1) =
      insert ⟨n + 1, h⟩ (univ.filter (fun j : Fin d => j.val ≤ n)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]
  omega

/- English proof (translation)
Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers.
-/
lemma filter_ge (n : ℕ) (h : n < d) :
    univ.filter (fun j : Fin d => n ≤ j.val) =
      insert ⟨n, h⟩ (univ.filter (fun j : Fin d => n + 1 ≤ j.val)) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, Fin.val_mk]
  omega

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `h`. Establish `hs : univ.filter (fun j : Fin d => j.val ≤ 0) = {⟨0, h⟩}`.

Use extensionality with `j`. Simplify using `[Fin.ext_iff]`. Rewrite using `[hs, Finset.sum_singleton]`. Evaluate the numerical expressions. Consider the case `succ n ih`.

Introduce `h`. Rewrite using `[filter_le_succ n h, Finset.sum_insert (by simp)]`. Establish `h1` using `ih (by omega)`. Establish `h2` using `hl ⟨n + 1, h⟩ ⟨n, by omega⟩ rfl`. Establish `hp : (0 : ℝ) ≤ 2 ^ (n + 1) - 1`.

Establish `: (1 : ℝ) ≤ 2 ^ (n + 1)` using `one_le_pow₀ (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `mul_le_mul_of_nonneg_left h2 hp`. Establish `e : ((2 : ℝ) ^ (n + 1 + 1) - 1) * ‖gs b ⟨n + 1, h⟩‖ ^ 2 = ‖gs b ⟨n + 1, h⟩‖ ^ 2 + (2 ^ (n + 1) - 1) * (2 * ‖gs b ⟨n + 1, h⟩‖ ^ 2)` using `by ring`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma sum_gs_le (b : Fin d → E)
    (hl : ∀ i j : Fin d, i.val = j.val + 1 → ‖gs b j‖ ^ 2 ≤ 2 * ‖gs b i‖ ^ 2) :
    ∀ (n : ℕ) (h : n < d), ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ n), ‖gs b j‖ ^ 2 ≤
      (2 ^ (n + 1) - 1) * ‖gs b ⟨n, h⟩‖ ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro h
    have hs : univ.filter (fun j : Fin d => j.val ≤ 0) = {⟨0, h⟩} := by
      ext j
      simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton]
    norm_num
  | succ n ih =>
    intro h
    rw [filter_le_succ n h, Finset.sum_insert (by simp)]
    have h1 := ih (by omega)
    have h2 := hl ⟨n + 1, h⟩ ⟨n, by omega⟩ rfl
    have hp : (0 : ℝ) ≤ 2 ^ (n + 1) - 1 := by
      have : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hp
    have e : ((2 : ℝ) ^ (n + 1 + 1) - 1) * ‖gs b ⟨n + 1, h⟩‖ ^ 2 =
        ‖gs b ⟨n + 1, h⟩‖ ^ 2 + (2 ^ (n + 1) - 1) * (2 * ‖gs b ⟨n + 1, h⟩‖ ^ 2) := by ring
    rw [e]
    linarith

/- English proof (translation)
Establish `key : ∀ j : Fin d, |c j| ≤ M + 1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), |c l|`. Introduce `j`. Establish `e` using `nu_split b hb c j`. Establish `h1 : |∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), c l * mu b l j| ≤ 1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), |c l|`. Rewrite using `[Finset.mul_sum]`.

Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hl`. Rewrite using `[abs_mul, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_right (hs l j (Fin.lt_iff_val_lt_val.mpr (by omega))) (abs_nonneg _)`. Establish `h2` using `abs_le.mp (hM j)`.

Establish `h1'` using `abs_le.mp h1`. Rewrite using `[abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `T : ∀ m : ℕ, ∀ k : ℕ, d = k + m → M + 1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => k ≤ l.val), |c l| ≤ (3 / 2) ^ m * M`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero`. Introduce `k hk`. Establish `he : univ.filter (fun l : Fin d => k ≤ l.val) = ∅`. Rewrite using `[Finset.filter_eq_empty_iff]`.

Introduce `l _`. Use `l.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[he, Finset.sum_empty]`. Simplify using the standard rewrite rules.

Consider the case `succ m ih`. Introduce `k hk`. Establish `hkd : k < d` using `by omega`. Rewrite using `[filter_ge k hkd, Finset.sum_insert (by simp)]`. Establish `h1` using `ih (k + 1) (by omega)`.

Establish `h2 : |c ⟨k, hkd⟩| ≤ M + 1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => k + 1 ≤ l.val), |c l|` using `key ⟨k, hkd⟩`. Rewrite using `[pow_succ]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hj` using `key j`. Establish `hjd` using `j.isLt`.

Establish `h3` using `T (d - (j.val + 1)) (j.val + 1) (by omega)`. Establish `hp : ((3 : ℝ) / 2) ^ (d - (j.val + 1)) ≤ (3 / 2) ^ d` using `by first`. Consider the case `exact pow_le_pow_right₀ (by norm_num) (by omega)`. Consider the case `exact pow_le_pow_right (by norm_num) (by omega)`. Establish `hM'` using `mul_le_mul_of_nonneg_right hp hM0`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma coeff_bound (b : Fin d → E) (hb : LinearIndependent ℝ b)
    (hs : ∀ i j : Fin d, j < i → |mu b i j| ≤ 1 / 2) (c : Fin d → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ j, |nu b c j| ≤ M) (j : Fin d) : |c j| ≤ (3 / 2) ^ d * M := by
  have key : ∀ j : Fin d, |c j| ≤ M + 1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), |c l| := by
    intro j
    have e := nu_split b hb c j
    have h1 : |∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), c l * mu b l j| ≤
        1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => j.val + 1 ≤ l.val), |c l| := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hs l j (Fin.lt_iff_val_lt_val.mpr (by omega))) (abs_nonneg _)
    have h2 := abs_le.mp (hM j)
    have h1' := abs_le.mp h1
    rw [abs_le]
    constructor <;> linarith
  have T : ∀ m : ℕ, ∀ k : ℕ, d = k + m →
      M + 1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => k ≤ l.val), |c l| ≤ (3 / 2) ^ m * M := by
    intro m
    induction m with
    | zero =>
      intro k hk
      have he : univ.filter (fun l : Fin d => k ≤ l.val) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro l _
        have := l.isLt
        omega
      rw [he, Finset.sum_empty]
      simp
    | succ m ih =>
      intro k hk
      have hkd : k < d := by omega
      rw [filter_ge k hkd, Finset.sum_insert (by simp)]
      have h1 := ih (k + 1) (by omega)
      have h2 : |c ⟨k, hkd⟩| ≤ M + 1 / 2 * ∑ l ∈ univ.filter (fun l : Fin d => k + 1 ≤ l.val), |c l| :=
        key ⟨k, hkd⟩
      rw [pow_succ]
      linarith
  have hj := key j
  have hjd := j.isLt
  have h3 := T (d - (j.val + 1)) (j.val + 1) (by omega)
  have hp : ((3 : ℝ) / 2) ^ (d - (j.val + 1)) ≤ (3 / 2) ^ d := by
    first
    | exact pow_le_pow_right₀ (by norm_num) (by omega)
    | exact pow_le_pow_right (by norm_num) (by omega)
  have hM' := mul_le_mul_of_nonneg_right hp hM0
  linarith

end ReciprocityTheory.ReducedBases.T2

end
