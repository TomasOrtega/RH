import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.FlagPsDeriv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm

noncomputable section

def flagTerm (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (j : Fin f × Fin N)
    (z : (Σ _ : Fin f, LowerPair N) → ℂ) : ℝ :=
  if h : j.2.val + 1 < N then
    (lam j.1 j.2 - lam j.1 ⟨j.2.val + 1, h⟩) * flagPs N p (j.2.val + 1) h.le fun q => z ⟨j.1, q⟩
  else 0

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [flagWeightProd, flagWeight, flagTerm, Fintype.sum_prod_type]`.
-/
theorem flagWeightProd_eq (f N p : ℕ) (lam : Fin f → Fin N → ℝ) :
    flagWeightProd f N p lam = fun z => ∑ j : Fin f × Fin N, flagTerm f N p lam j z := by
  funext z
  simp only [flagWeightProd, flagWeight, flagTerm, Fintype.sum_prod_type]

/- English proof (translation)
Use `fun_prop`.
-/
theorem contDiff_factor {f N : ℕ} (τ : Fin f) :
    ContDiff ℝ 2 fun z : (Σ _ : Fin f, LowerPair N) → ℂ => fun q : LowerPair N => z ⟨τ, q⟩ := by
  fun_prop

/- English proof (translation)
Unfold `flagTerm`. Distinguish the cases in `h : j.2.val + 1 < N`. Simplify using `only [h, dif_pos]`. Conclude with `contDiffAt_const.mul (contDiffAt_flagPs p _ h.le (contDiff_factor j.1) rfl)`. Simplify using `only [h, dif_neg, not_false_eq_true]`.

Conclude with `contDiffAt_const`.
-/
theorem contDiffAt_flagTerm (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (j : Fin f × Fin N) :
    ContDiffAt ℝ 2 (flagTerm f N p lam j) 0 := by
  unfold flagTerm
  by_cases h : j.2.val + 1 < N
  · simp only [h, dif_pos]
    exact contDiffAt_const.mul (contDiffAt_flagPs p _ h.le (contDiff_factor j.1) rfl)
  · simp only [h, dif_neg, not_false_eq_true]
    exact contDiffAt_const

/- English proof (translation)
Establish `: ∀ c b, ‖lowerMatrix (Complex.I • u) c b‖ = ‖lowerMatrix u c b‖`. Introduce `c b`. Simplify using `only [lowerMatrix, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [tailSum, this]`.
-/
theorem tailSum_I {N : ℕ} (p i : ℕ) (u : LowerPair N → ℂ) :
    tailSum p i (lowerMatrix (Complex.I • u)) = tailSum p i (lowerMatrix u) := by
  have : ∀ c b, ‖lowerMatrix (Complex.I • u) c b‖ = ‖lowerMatrix u c b‖ := by
    intro c b
    simp only [lowerMatrix, Matrix.of_apply]
    split_ifs <;> simp
  simp only [tailSum, this]

/- English proof (translation)
Rewrite using `[deriv_const_mul_field', deriv_const_mul_field']`. Conclude with `congrArg (c * ·) (deriv_deriv_flagPs p i hi fun q => v ⟨τ, q⟩)`.
-/
theorem deriv_deriv_term {f N : ℕ} (p : ℕ) (c : ℝ) (i : ℕ) (hi : i ≤ N) (τ : Fin f)
    (v : (Σ _ : Fin f, LowerPair N) → ℂ) :
    deriv (deriv fun t : ℝ => c * flagPs N p i hi fun q => (t • v) ⟨τ, q⟩) 0 =
      c * (2 * tailSum p i (lowerMatrix fun q => v ⟨τ, q⟩)) := by
  rw [deriv_const_mul_field', deriv_const_mul_field']
  exact congrArg (c * ·) (deriv_deriv_flagPs p i hi fun q => v ⟨τ, q⟩)

/- English proof (translation)
Rewrite using `[levi_eq_deriv_deriv (contDiffAt_flagTerm f N p lam j) w]`. Distinguish the cases in `h : j.2.val + 1 < N`. Simplify using `only [flagTerm, h, dif_pos]`. Rewrite using `[deriv_deriv_term, deriv_deriv_term, show (fun q => (Complex.I • w) ⟨j.1, q⟩) = Complex.I • (fun q => w ⟨j.1, q⟩) from rfl, tailSum_I]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [flagTerm, h, dif_neg, not_false_eq_true]`. Simplify using the standard rewrite rules.
-/
theorem levi_flagTerm (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (j : Fin f × Fin N)
    (w : (Σ _ : Fin f, LowerPair N) → ℂ) :
    levi (flagTerm f N p lam j) 0 w = if h : j.2.val + 1 < N then
      (lam j.1 j.2 - lam j.1 ⟨j.2.val + 1, h⟩) * tailSum p (j.2.val + 1)
        (lowerMatrix fun q => w ⟨j.1, q⟩) else 0 := by
  rw [levi_eq_deriv_deriv (contDiffAt_flagTerm f N p lam j) w]
  by_cases h : j.2.val + 1 < N
  · simp only [flagTerm, h, dif_pos]
    rw [deriv_deriv_term, deriv_deriv_term,
      show (fun q => (Complex.I • w) ⟨j.1, q⟩) = Complex.I • (fun q => w ⟨j.1, q⟩) from rfl,
      tailSum_I]
    ring
  · simp only [flagTerm, h, dif_neg, not_false_eq_true]
    simp

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[show b + (m + 1) = b + m + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_Ico_telescope (Λ : ℕ → ℝ) (b m : ℕ) :
    ∑ k ∈ Finset.Ico b (b + m), (Λ k - Λ (k + 1)) = Λ b - Λ (b + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show b + (m + 1) = b + m + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]
    ring

/- English proof (translation)
Rewrite using `[show (∑ k : Fin N, (if b ≤ k.val ∧ k.val < c then Λ k - Λ (k.val + 1) else 0)) = ∑ k ∈ Finset.range N, (if b ≤ k ∧ k < c then Λ k - Λ (k + 1) else 0) from Fin.sum_univ_eq_sum_range (fun k => if b ≤ k ∧ k < c then Λ k - Λ (k + 1) else 0) N]`. Rewrite using `[← Finset.sum_filter]`. Establish `: (Finset.range N).filter (fun k => b ≤ k ∧ k < c) = Finset.Ico b (b + (c - b))`. Use extensionality with `k`. Simplify using `only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[this, sum_Ico_telescope, Nat.add_sub_cancel' hbc.le]`.
-/
theorem sum_fin_telescope {N : ℕ} (Λ : ℕ → ℝ) (b c : ℕ) (hbc : b < c) (hc : c ≤ N) :
    ∑ k : Fin N, (if b ≤ k.val ∧ k.val < c then Λ k - Λ (k.val + 1) else 0) = Λ b - Λ c := by
  rw [show (∑ k : Fin N, (if b ≤ k.val ∧ k.val < c then Λ k - Λ (k.val + 1) else 0)) =
      ∑ k ∈ Finset.range N, (if b ≤ k ∧ k < c then Λ k - Λ (k + 1) else 0) from
    Fin.sum_univ_eq_sum_range (fun k => if b ≤ k ∧ k < c then Λ k - Λ (k + 1) else 0) N]
  rw [← Finset.sum_filter]
  have : (Finset.range N).filter (fun k => b ≤ k ∧ k < c) = Finset.Ico b (b + (c - b)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, sum_Ico_telescope, Nat.add_sub_cancel' hbc.le]

/- English proof (translation)
Use `set Λ : ℕ → ℝ := fun n => if h : n < N then lam ⟨n, h⟩ else 0 with hΛ`. Use `set A : Fin N → Fin N → ℝ := fun a b => sigSign p b * sigSign p a * ‖lowerMatrix u a b‖ ^ 2 with hA`. Establish `step1 : ∀ k : Fin N, (if h : k.val + 1 < N then (lam k - lam ⟨k.val + 1, h⟩) * tailSum p (k.val + 1) (lowerMatrix u) else 0) = ∑ b : Fin N, ∑ a : Fin N, (if b.val ≤ k.val ∧ k.val < a.val then Λ k - Λ (k.val + 1) else 0) * A a b`. Introduce `k`. Distinguish the cases in `h : k.val + 1 < N`.

Rewrite using `[dif_pos h, tailSum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `e1 : Λ k = lam k` using `by simp [hΛ, k.isLt]`.

Establish `e2 : Λ (k.val + 1) = lam ⟨k.val + 1, h⟩` using `by simp [hΛ, h]`. Distinguish the cases in `hba : b.val ≤ k.val ∧ k.val < a.val`. Rewrite using `[if_pos (by omega), if_pos hba, e1, e2, hA]`. Rewrite using `[if_neg (by omega), if_neg hba]`. Simplify using the standard rewrite rules.

Rewrite using `[dif_neg h]`. Use `symm`. Use `Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg (by have := a.isLt; omega)]`. Simplify using the standard rewrite rules.

Establish `step2 : (∑ k : Fin N, ∑ b : Fin N, ∑ a : Fin N, (if b.val ≤ k.val ∧ k.val < a.val then Λ k - Λ (k.val + 1) else 0) * A a b) = ∑ a : Fin N, ∑ b : Fin N, if b < a then (Λ b - Λ a) * A a b else 0`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_congr rfl fun b _ => Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_mul]`. Distinguish the cases in `hba : b < a`. Rewrite using `[if_pos hba, sum_fin_telescope Λ b.val a.val hba a.isLt.le]`. Establish `hba' : ¬ b.val < a.val` using `fun h' => hba h'`. Rewrite using `[if_neg hba, Finset.sum_eq_zero (fun k _ => if_neg (by omega)), zero_mul]`.

Establish `step3 : ∑ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 = ∑ a : Fin N, ∑ b : Fin N, if b < a then (Λ b - Λ a) * A a b else 0`. Establish `e : ∀ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 = (fun x : Fin N × Fin N => if x.2 < x.1 then (Λ x.2 - Λ x.1) * A x.1 x.2 else 0) q.1`. Introduce and unpack `⟨⟨a, b⟩, hab⟩`. Use `show _ = if b < a then (Λ b - Λ a) * A a b else 0`. Rewrite using `[if_pos hab]`.

Establish `hl : lowerMatrix u a b = u ⟨(a, b), hab⟩` using `by simp [lowerMatrix, hab]`. Establish `hab' : b.val < a.val` using `hab`. Simplify using `only [hA, hΛ, hl, rootPairing, sigSign, dif_pos a.isLt, dif_pos b.isLt, Fin.eta]`. Apply the tactic sequence `split_ifs <;> first | ring1 | (exfalso; omega)`. Rewrite using `[Fintype.sum_congr _ _ e]`.

Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun x : Fin N × Fin N => x.2 < x.1) (by simp) (fun x : Fin N × Fin N => if x.2 < x.1 then (Λ x.2 - Λ x.1) * A x.1 x.2 else 0)]`. Rewrite using `[Finset.sum_filter_of_ne (fun x _ hx => by by_contra h; exact hx (if_neg h)), Fintype.sum_prod_type]`. Rewrite using `[Finset.sum_congr rfl fun k _ => step1 k, step2, step3]`.
-/
theorem sum_steps_eq_rootPairing (N p : ℕ) (lam : Fin N → ℝ) (u : LowerPair N → ℂ) :
    ∑ k : Fin N, (if h : k.val + 1 < N then
      (lam k - lam ⟨k.val + 1, h⟩) * tailSum p (k.val + 1) (lowerMatrix u) else 0) =
      ∑ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 := by
  set Λ : ℕ → ℝ := fun n => if h : n < N then lam ⟨n, h⟩ else 0 with hΛ
  set A : Fin N → Fin N → ℝ := fun a b => sigSign p b * sigSign p a * ‖lowerMatrix u a b‖ ^ 2
    with hA
  have step1 : ∀ k : Fin N, (if h : k.val + 1 < N then
      (lam k - lam ⟨k.val + 1, h⟩) * tailSum p (k.val + 1) (lowerMatrix u) else 0) =
      ∑ b : Fin N, ∑ a : Fin N,
        (if b.val ≤ k.val ∧ k.val < a.val then Λ k - Λ (k.val + 1) else 0) * A a b := by
    intro k
    by_cases h : k.val + 1 < N
    · rw [dif_pos h, tailSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have e1 : Λ k = lam k := by simp [hΛ, k.isLt]
      have e2 : Λ (k.val + 1) = lam ⟨k.val + 1, h⟩ := by simp [hΛ, h]
      by_cases hba : b.val ≤ k.val ∧ k.val < a.val
      · rw [if_pos (by omega), if_pos hba, e1, e2, hA]
      · rw [if_neg (by omega), if_neg hba]
        simp
    · rw [dif_neg h]
      symm
      refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => ?_
      rw [if_neg (by have := a.isLt; omega)]
      simp
  have step2 : (∑ k : Fin N, ∑ b : Fin N, ∑ a : Fin N,
      (if b.val ≤ k.val ∧ k.val < a.val then Λ k - Λ (k.val + 1) else 0) * A a b) =
      ∑ a : Fin N, ∑ b : Fin N, if b < a then (Λ b - Λ a) * A a b else 0 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul]
    by_cases hba : b < a
    · rw [if_pos hba, sum_fin_telescope Λ b.val a.val hba a.isLt.le]
    · have hba' : ¬ b.val < a.val := fun h' => hba h'
      rw [if_neg hba, Finset.sum_eq_zero (fun k _ => if_neg (by omega)), zero_mul]
  have step3 : ∑ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 =
      ∑ a : Fin N, ∑ b : Fin N, if b < a then (Λ b - Λ a) * A a b else 0 := by
    have e : ∀ q : LowerPair N, rootPairing N p lam q * ‖u q‖ ^ 2 =
        (fun x : Fin N × Fin N => if x.2 < x.1 then (Λ x.2 - Λ x.1) * A x.1 x.2 else 0) q.1 := by
      rintro ⟨⟨a, b⟩, hab⟩
      show _ = if b < a then (Λ b - Λ a) * A a b else 0
      rw [if_pos hab]
      have hl : lowerMatrix u a b = u ⟨(a, b), hab⟩ := by simp [lowerMatrix, hab]
      have hab' : b.val < a.val := hab
      simp only [hA, hΛ, hl, rootPairing, sigSign, dif_pos a.isLt, dif_pos b.isLt, Fin.eta]
      split_ifs <;> first | ring1 | (exfalso; omega)
    rw [Fintype.sum_congr _ _ e]
    rw [← Finset.sum_subtype (Finset.univ.filter fun x : Fin N × Fin N => x.2 < x.1) (by simp)
      (fun x : Fin N × Fin N => if x.2 < x.1 then (Λ x.2 - Λ x.1) * A x.1 x.2 else 0)]
    rw [Finset.sum_filter_of_ne (fun x _ hx => by by_contra h; exact hx (if_neg h)),
      Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun k _ => step1 k, step2, step3]

/- English proof (translation)
Introduce `f N p lam w`. Rewrite using `[flagWeightProd_eq, levi_finset_sum _ _ (fun j _ => contDiffAt_flagTerm f N p lam j)]`. Simplify using `only [levi_flagTerm]`. Rewrite using `[Fintype.sum_prod_type, Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Conclude with `sum_steps_eq_rootPairing N p (lam τ) (fun q => w ⟨τ, q⟩)`.
-/
theorem FlagWeightLevi.proof : FlagWeightLevi.Statement := by
  intro f N p lam w
  rw [flagWeightProd_eq,
    levi_finset_sum _ _ (fun j _ => contDiffAt_flagTerm f N p lam j)]
  simp only [levi_flagTerm]
  rw [Fintype.sum_prod_type, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact sum_steps_eq_rootPairing N p (lam τ) (fun q => w ⟨τ, q⟩)

end

end GroundTheory.Heights₂.Heights.FourB
