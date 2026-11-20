import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MulVecBvecApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact

open Matrix

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula.UWC

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW

variable {k r : ℕ}

def lI (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩

def Wp (k r : ℕ) : Finset (Fin (2 * r + k + 1)) :=
  Finset.univ.filter fun i => r ≤ i.val ∧ i.val < r + k

/- English proof (translation)
Establish `hterm : ∀ i, star (w i) * (Hpk k r *ᵥ v) i = (if r ≤ i.val ∧ i.val < r + k then star (w i) * v i else 0) - (if lI k r = i then star (w (lI k r)) * v (lI k r) else 0)`. Introduce `i`. Rewrite using `[Hpk_mulVec_apply]`. Establish `hi` using `i.isLt`. Distinguish the cases in `hW : inW k r i`.

Establish `hp : piI k r i = i`. Establish `hW'` using `hW`. Unfold `inW at hW'`. Unfold `piI`. Rewrite using `[if_pos hW']`.

Rewrite using `[hp]`. Unfold `inW at hW`. Distinguish the cases in `hl : i.val = r + k`. Establish `h1 : lI k r = i` using `Fin.ext hl.symm`. Rewrite using `[if_neg (by omega), if_pos h1, h1]`.

Unfold `epsI`. Rewrite using `[if_pos hl]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : lI k r ≠ i` using `fun h => hl (by rw [← h]; rfl)`. Rewrite using `[if_pos ⟨hW.1, by omega⟩, if_neg h1]`.

Unfold `epsI`. Rewrite using `[if_neg hl]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : v (piI k r i) = 0` using `hv _ (piI_not_inW hW)`. Establish `h1 : lI k r ≠ i` using `fun h => hW (by rw [← h]; unfold inW lI; simp)`.

Unfold `inW at hW`. Rewrite using `[h0, if_neg (by omega), if_neg h1]; ring`. Simplify using `only [dotProduct, Pi.star_apply, hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, Wp, Finset.sum_filter]`.
-/
lemma star_dotProduct_Hpk_mulVec_eq_sum_sub (v w : Fin (2 * r + k + 1) → ℂ) (hv : ∀ i, ¬ inW k r i → v i = 0) :
    star w ⬝ᵥ (Hpk k r *ᵥ v) =
      (∑ i ∈ Wp k r, star (w i) * v i) - star (w (lI k r)) * v (lI k r) := by
  have hterm : ∀ i, star (w i) * (Hpk k r *ᵥ v) i =
      (if r ≤ i.val ∧ i.val < r + k then star (w i) * v i else 0) -
        (if lI k r = i then star (w (lI k r)) * v (lI k r) else 0) := by
    intro i
    rw [Hpk_mulVec_apply]
    have hi := i.isLt
    by_cases hW : inW k r i
    · have hp : piI k r i = i := by
        have hW' := hW
        unfold inW at hW'
        unfold piI
        rw [if_pos hW']
      rw [hp]
      unfold inW at hW
      by_cases hl : i.val = r + k
      · have h1 : lI k r = i := Fin.ext hl.symm
        rw [if_neg (by omega), if_pos h1, h1]
        unfold epsI; rw [if_pos hl]; ring
      · have h1 : lI k r ≠ i := fun h => hl (by rw [← h]; rfl)
        rw [if_pos ⟨hW.1, by omega⟩, if_neg h1]
        unfold epsI; rw [if_neg hl]; ring
    · have h0 : v (piI k r i) = 0 := hv _ (piI_not_inW hW)
      have h1 : lI k r ≠ i := fun h => hW (by rw [← h]; unfold inW lI; simp)
      unfold inW at hW
      rw [h0, if_neg (by omega), if_neg h1]; ring
  simp only [dotProduct, Pi.star_apply, hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Wp, Finset.sum_filter]

/- English proof (translation)
Rewrite using `[Complex.star_def, Complex.conj_mul']`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma star_mul_self_eq (x : ℂ) : star x * x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

/- English proof (translation)
Establish `hv : ∀ i, ¬ inW k r i → z i = 0` using `fun i hi => hz i (by unfold inW at hi; omega)`. Unfold `Tz herm`. Rewrite using `[star_dotProduct_Hpk_mulVec_eq_sum_sub z z hv]`. Simplify using `only [star_mul_self_eq]`. Rewrite using `[← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma tz_eq {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    Tz k r z = ‖z (lI k r)‖ ^ 2 - ∑ i ∈ Wp k r, ‖z i‖ ^ 2 := by
  have hv : ∀ i, ¬ inW k r i → z i = 0 := fun i hi => hz i (by unfold inW at hi; omega)
  unfold Tz herm
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub z z hv]
  simp only [star_mul_self_eq]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]
  ring

/- English proof (translation)
Establish `hh' : hᴴ * (Hpk k r * h) = Hpk k r` using `by rw [← Matrix.mul_assoc]; exact hh`. Rewrite using `[star_mulVec, ← dotProduct_mulVec]`. Simplify using `only [Matrix.mulVec_mulVec, hh']`.
-/
lemma herm_invariant {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UH (Hpk k r)) (u v : Fin (2 * r + k + 1) → ℂ) :
    star (h *ᵥ u) ⬝ᵥ (Hpk k r *ᵥ (h *ᵥ v)) = star u ⬝ᵥ (Hpk k r *ᵥ v) := by
  have hh' : hᴴ * (Hpk k r * h) = Hpk k r := by rw [← Matrix.mul_assoc]; exact hh
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, hh']

/- English proof (translation)
Apply the tactic sequence `unfold epsI; split_ifs <;> simp`.
-/
lemma norm_epsI (i : Fin (2 * r + k + 1)) : ‖epsI k r i‖ = 1 := by
  unfold epsI; split_ifs <;> simp

/- English proof (translation)
Apply the tactic sequence `rw [bvec_apply]; split_ifs <;> simp`.
-/
lemma norm_bvec_le (j i : Fin (2 * r + k + 1)) : ‖bvec j i‖ ≤ 1 := by
  rw [bvec_apply]; split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Hpk_mulVec_apply, norm_mul, norm_epsI, one_mul]`. Conclude with `norm_bvec_le _ _`.
-/
lemma norm_H_bvec_le (j i : Fin (2 * r + k + 1)) : ‖(Hpk k r *ᵥ bvec j) i‖ ≤ 1 := by
  rw [Hpk_mulVec_apply, norm_mul, norm_epsI, one_mul]
  exact norm_bvec_le _ _

def Bd (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  ((2 * r + k + 1 : ℕ) : ℝ) +
    (Real.sqrt (∑ i ∈ Wp k r, ‖z i‖ ^ 2) * ((2 * r + k + 1 : ℕ) : ℝ) + ∑ i, ‖z i‖) /
      (‖z (lI k r)‖ - Real.sqrt (∑ i ∈ Wp k r, ‖z i‖ ^ 2))

/- English proof (translation)
Use `set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn`. Establish `hn1 : 1 ≤ n` using `by rw [hn]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)`. Use `set A := ∑ i ∈ Wp k r, ‖z i‖ ^ 2 with hAdef`. Use `set a := Real.sqrt A with hadef`. Use `set b := ‖z (lI k r)‖ with hbdef`.

Use `set Z := ∑ i, ‖z i‖ with hZdef`. Establish `hA0 : 0 ≤ A` using `Finset.sum_nonneg fun _ _ => sq_nonneg _`. Establish `ha0 : 0 ≤ a` using `Real.sqrt_nonneg _`. Establish `hb0 : 0 ≤ b` using `norm_nonneg _`. Establish `hZ0 : 0 ≤ Z` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`.

Establish `haa : a ^ 2 = A` using `Real.sq_sqrt hA0`. Establish `hTab : Tz k r z = b ^ 2 - a ^ 2` using `by rw [tz_eq hz, haa]`. Establish `hab : a < b`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`.

Use polynomial arithmetic with `[mul_self_le_mul_self hb0 hc]`. Establish `hba : 0 < b - a` using `by linarith`. Establish `hq0 : 0 ≤ (a * n + Z) / (b - a)` using `div_nonneg (by positivity) hba.le`. Establish `hBd : Bd k r z = n + (a * n + Z) / (b - a)` using `rfl`. Rewrite using `[hBd]`.

Establish `hδ : ∀ x : ℂ, (x = if i = j then 1 else 0) → ‖x‖ ≤ n + (a * n + Z) / (b - a)`. Introduce `x hx`. Apply the tactic sequence `have : ‖x‖ ≤ 1 := by rw [hx]; split_ifs <;> simp`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `hij : inW k r i ∧ inW k r j`.

Use `swap`. Conclude with `hδ _ (uw_block hh i j hij)`. Take `⟨hiW, hjW⟩` from `hij`. Use `set c : Fin (2 * r + k + 1) → ℂ := fun x => h x j with hcdef`. Establish `hc : c = h *ᵥ bvec j` using `funext fun x => (mulVec_bvec_apply h x j).symm`.

Establish `hcW : ∀ x, ¬ inW k r x → c x = 0`. Introduce `x hx`. Establish `hne : x ≠ j` using `by rintro rfl; exact hx hjW`. Use `uw_block hh x j (fun h' => hx h'.1)` as an intermediate fact. Simplify using `only [hcdef, this, if_neg hne]`.

Establish `hEA : star c ⬝ᵥ (Hpk k r *ᵥ c) = star (bvec j) ⬝ᵥ (Hpk k r *ᵥ bvec j)`. Rewrite using `[hc]`. Conclude with `herm_invariant hh.1 _ _`. Establish `hEK : star z ⬝ᵥ (Hpk k r *ᵥ c) = star z ⬝ᵥ (Hpk k r *ᵥ bvec j)`. Use `herm_invariant hh.1 z (bvec j)` as an intermediate fact.

Rewrite `this` using `[hh.2.2]`. Rewrite using `[hc]`. Conclude with `this`. Establish `hnA : ‖star (bvec j) ⬝ᵥ (Hpk k r *ᵥ bvec j)‖ ≤ n`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Establish `: ∀ x ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))), ‖(star (bvec j)) x * (Hpk k r *ᵥ bvec j) x‖ ≤ 1`. Introduce `x _`. Rewrite using `[norm_mul, Pi.star_apply, norm_star]`. Conclude with `mul_le_one₀ (norm_bvec_le _ _) (norm_nonneg _) (norm_H_bvec_le _ _)`. Use `(Finset.sum_le_sum this).trans ?_` and prove the remaining obligations.

Simplify using `[hn]`. Establish `hnK : ‖star z ⬝ᵥ (Hpk k r *ᵥ bvec j)‖ ≤ Z`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, Pi.star_apply, norm_star]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (norm_H_bvec_le _ _)`.

Rewrite `hEA` using `[star_dotProduct_Hpk_mulVec_eq_sum_sub c c hcW]`. Rewrite `hEK` using `[star_dotProduct_Hpk_mulVec_eq_sum_sub c z hcW]`. Use `set X2 := ∑ x ∈ Wp k r, ‖c x‖ ^ 2 with hX2`. Use `set Y := ‖c (lI k r)‖ with hY`. Establish `hY0 : 0 ≤ Y` using `norm_nonneg _`.

Establish `hX20 : 0 ≤ X2` using `Finset.sum_nonneg fun _ _ => sq_nonneg _`. Establish `h1 : X2 - Y ^ 2 ≤ n`. Establish `e` using `congrArg Complex.re hEA`. Simplify using `only [star_mul_self_eq] at e`. Rewrite `e` using `[← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]`.

Rewrite using `[e]`. Conclude with `(Complex.re_le_norm _).trans hnA`. Establish `h2 : b * Y ≤ (∑ x ∈ Wp k r, ‖z x‖ * ‖c x‖) + Z`. Establish `e : star (z (lI k r)) * c (lI k r) = (∑ x ∈ Wp k r, star (z x) * c x) - star z ⬝ᵥ (Hpk k r *ᵥ bvec j)`. Rewrite using `[← hEK]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2` using `congrArg norm e`. Rewrite `e2` using `[norm_mul, norm_star]`. Rewrite using `[hbdef, hY, e2]`. Use `(norm_sub_le _ _).trans (add_le_add ?_ hnK)` and prove the remaining obligations.

Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_star]`. Establish `hCS : (∑ x ∈ Wp k r, ‖z x‖ * ‖c x‖) ≤ a * Real.sqrt X2` using `Real.sum_mul_le_sqrt_mul_sqrt _ _ _`. Establish `hsX : Real.sqrt X2 ≤ n + Y`.

Establish `: X2 ≤ (n + Y) ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hYb : Y ≤ (a * n + Z) / (b - a)`. Rewrite using `[le_div_iff₀ hba]`. Use the polynomial consequences of the given equalities and inequalities.

Distinguish the cases in `hil : i = lI k r`. Establish `: ‖h i j‖ = Y` using `by rw [hY, hil]`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hiWp : i ∈ Wp k r`.

Unfold `Wp inW at *`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use `⟨hiW.1, ?_⟩` and prove the remaining obligations. Break down `Nat.lt_or_ge i.val (r + k) with h' | h'` into its components or cases. Conclude with `h'`.

Conclude with `absurd (Fin.ext (by simp [lI]; omega)) hil`. Establish `hci : ‖c i‖ ^ 2 ≤ X2` using `Finset.single_le_sum (f := fun x => ‖c x‖ ^ 2) (fun _ _ => sq_nonneg _) hiWp`. Establish `hci' : ‖c i‖ ≤ n + Y`. Establish `h0 : 0 ≤ ‖c i‖` using `norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.

Establish `: ‖h i j‖ = ‖c i‖` using `rfl`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma uw_entry_bound {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (i j : Fin (2 * r + k + 1)) : ‖h i j‖ ≤ Bd k r z := by
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  set A := ∑ i ∈ Wp k r, ‖z i‖ ^ 2 with hAdef
  set a := Real.sqrt A with hadef
  set b := ‖z (lI k r)‖ with hbdef
  set Z := ∑ i, ‖z i‖ with hZdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have haa : a ^ 2 = A := Real.sq_sqrt hA0
  have hTab : Tz k r z = b ^ 2 - a ^ 2 := by rw [tz_eq hz, haa]
  have hab : a < b := by
    by_contra hc
    push Not at hc
    nlinarith [mul_self_le_mul_self hb0 hc]
  have hba : 0 < b - a := by linarith
  have hq0 : 0 ≤ (a * n + Z) / (b - a) := div_nonneg (by positivity) hba.le
  have hBd : Bd k r z = n + (a * n + Z) / (b - a) := rfl
  rw [hBd]
  have hδ : ∀ x : ℂ, (x = if i = j then 1 else 0) → ‖x‖ ≤ n + (a * n + Z) / (b - a) := by
    intro x hx
    have : ‖x‖ ≤ 1 := by rw [hx]; split_ifs <;> simp
    linarith
  by_cases hij : inW k r i ∧ inW k r j
  swap
  · exact hδ _ (uw_block hh i j hij)
  obtain ⟨hiW, hjW⟩ := hij

  set c : Fin (2 * r + k + 1) → ℂ := fun x => h x j with hcdef
  have hc : c = h *ᵥ bvec j := funext fun x => (mulVec_bvec_apply h x j).symm
  have hcW : ∀ x, ¬ inW k r x → c x = 0 := by
    intro x hx
    have hne : x ≠ j := by rintro rfl; exact hx hjW
    have := uw_block hh x j (fun h' => hx h'.1)
    simp only [hcdef, this, if_neg hne]
  have hEA : star c ⬝ᵥ (Hpk k r *ᵥ c) = star (bvec j) ⬝ᵥ (Hpk k r *ᵥ bvec j) := by
    rw [hc]; exact herm_invariant hh.1 _ _
  have hEK : star z ⬝ᵥ (Hpk k r *ᵥ c) = star z ⬝ᵥ (Hpk k r *ᵥ bvec j) := by
    have := herm_invariant hh.1 z (bvec j)
    rw [hh.2.2] at this
    rw [hc]; exact this
  have hnA : ‖star (bvec j) ⬝ᵥ (Hpk k r *ᵥ bvec j)‖ ≤ n := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ x ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))),
        ‖(star (bvec j)) x * (Hpk k r *ᵥ bvec j) x‖ ≤ 1 := by
      intro x _
      rw [norm_mul, Pi.star_apply, norm_star]
      exact mul_le_one₀ (norm_bvec_le _ _) (norm_nonneg _) (norm_H_bvec_le _ _)
    refine (Finset.sum_le_sum this).trans ?_
    simp [hn]
  have hnK : ‖star z ⬝ᵥ (Hpk k r *ᵥ bvec j)‖ ≤ Z := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, Pi.star_apply, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_H_bvec_le _ _)
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub c c hcW] at hEA
  rw [star_dotProduct_Hpk_mulVec_eq_sum_sub c z hcW] at hEK
  set X2 := ∑ x ∈ Wp k r, ‖c x‖ ^ 2 with hX2
  set Y := ‖c (lI k r)‖ with hY
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hX20 : 0 ≤ X2 := Finset.sum_nonneg fun _ _ => sq_nonneg _

  have h1 : X2 - Y ^ 2 ≤ n := by
    have e := congrArg Complex.re hEA
    simp only [star_mul_self_eq] at e
    rw [← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re] at e
    rw [e]
    exact (Complex.re_le_norm _).trans hnA

  have h2 : b * Y ≤ (∑ x ∈ Wp k r, ‖z x‖ * ‖c x‖) + Z := by
    have e : star (z (lI k r)) * c (lI k r) =
        (∑ x ∈ Wp k r, star (z x) * c x) - star z ⬝ᵥ (Hpk k r *ᵥ bvec j) := by
      rw [← hEK]; ring
    have e2 := congrArg norm e
    rw [norm_mul, norm_star] at e2
    rw [hbdef, hY, e2]
    refine (norm_sub_le _ _).trans (add_le_add ?_ hnK)
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [norm_mul, norm_star]
  have hCS : (∑ x ∈ Wp k r, ‖z x‖ * ‖c x‖) ≤ a * Real.sqrt X2 :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hsX : Real.sqrt X2 ≤ n + Y := by
    have : X2 ≤ (n + Y) ^ 2 := by nlinarith
    calc Real.sqrt X2 ≤ Real.sqrt ((n + Y) ^ 2) := Real.sqrt_le_sqrt this
      _ = n + Y := Real.sqrt_sq (by linarith)
  have hYb : Y ≤ (a * n + Z) / (b - a) := by
    rw [le_div_iff₀ hba]
    nlinarith
  by_cases hil : i = lI k r
  · have : ‖h i j‖ = Y := by rw [hY, hil]
    rw [this]; linarith
  · have hiWp : i ∈ Wp k r := by
      unfold Wp inW at *
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hiW.1, ?_⟩
      rcases Nat.lt_or_ge i.val (r + k) with h' | h'
      · exact h'
      · exact absurd (Fin.ext (by simp [lI]; omega)) hil
    have hci : ‖c i‖ ^ 2 ≤ X2 :=
      Finset.single_le_sum (f := fun x => ‖c x‖ ^ 2) (fun _ _ => sq_nonneg _) hiWp
    have hci' : ‖c i‖ ≤ n + Y := by
      have h0 : 0 ≤ ‖c i‖ := norm_nonneg _
      nlinarith
    have : ‖h i j‖ = ‖c i‖ := rfl
    rw [this]; linarith

end PI.QuotSetU.UnitaryGroupMassFormula.UWC

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW PI.QuotSetU.UnitaryGroupMassFormula.UWC

/- English proof (translation)
Introduce `k r z hz hT`. Establish `hcont : ∀ v : Fin (2 * r + k + 1) → ℂ, Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => g *ᵥ v` using `fun v => Continuous.matrix_mulVec continuous_id continuous_const`. Establish `hcl : IsClosed (UWset k r z)`. Establish `e : UWset k r z = UH (Hpk k r) ∩ ((⋂ a : Fin r, ({g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩ {g | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g | g *ᵥ z = z})`. Use extensionality with `g`.

Simplify using `only [UWset, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]`. Rewrite using `[e]`. Use `(unitary_hermitian_group k r).1.inter (IsClosed.inter (isClosed_iInter fun a => ?_) ?_)` and prove the remaining obligations. Conclude with `(isClosed_eq (hcont _) continuous_const).inter (isClosed_eq (hcont _) continuous_const)`. Conclude with `isClosed_eq (hcont _) continuous_const`.

Establish `hB : IsCompact (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) (Bd k r z))` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Use `hB.of_isClosed_subset hcl ?_` and prove the remaining obligations. Introduce `g hg i _ j _`. Simplify using `using uw_entry_bound hz hT hg i j`.
-/
theorem unitary_weyl_compact : UWCompact := by
  intro k r z hz hT
  have hcont : ∀ v : Fin (2 * r + k + 1) → ℂ,
      Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => g *ᵥ v :=
    fun v => Continuous.matrix_mulVec continuous_id continuous_const
  have hcl : IsClosed (UWset k r z) := by
    have e : UWset k r z = UH (Hpk k r) ∩ ((⋂ a : Fin r,
        ({g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {g | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g | g *ᵥ z = z}) := by
      ext g
      simp only [UWset, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [e]
    refine (unitary_hermitian_group k r).1.inter (IsClosed.inter (isClosed_iInter fun a => ?_) ?_)
    · exact (isClosed_eq (hcont _) continuous_const).inter (isClosed_eq (hcont _) continuous_const)
    · exact isClosed_eq (hcont _) continuous_const
  have hB : IsCompact (Set.pi Set.univ fun _ : Fin (2 * r + k + 1) => Set.pi Set.univ fun _ : Fin (2 * r + k + 1) =>
      Metric.closedBall (0 : ℂ) (Bd k r z)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hB.of_isClosed_subset hcl ?_
  intro g hg i _ j _
  simpa using uw_entry_bound hz hT hg i j

end PI.QuotSetU.UnitaryGroupMassFormula

end
