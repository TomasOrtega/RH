import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.DoubleSumDiagSplit

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

def highestWeightBoundConst {n : ℕ} (ε : Fin n → Bool) (d Λ₀ : Fin n → ℝ) : ℝ :=
  |nsq (rho n) - nsq (rhoN ε - rhoC ε)| + 2 * ∑ a, |d a| + 2 * ∑ a, |Λ₀ a| + 1

/- English proof (translation)
Unfold `highestWeightBoundConst`. Establish `h1 : 0 ≤ ∑ a, |d a|` using `sum_nonneg fun a _ => abs_nonneg _`. Establish `h2 : 0 ≤ ∑ a, |Λ₀ a|` using `sum_nonneg fun a _ => abs_nonneg _`. Establish `h3` using `abs_nonneg (nsq (rho n) - nsq (rhoN ε - rhoC ε))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_highestWeightBoundConst {n : ℕ} (ε : Fin n → Bool) (d Λ₀ : Fin n → ℝ) : 1 ≤ highestWeightBoundConst ε d Λ₀ := by
  unfold highestWeightBoundConst
  have h1 : 0 ≤ ∑ a, |d a| := sum_nonneg fun a _ => abs_nonneg _
  have h2 : 0 ≤ ∑ a, |Λ₀ a| := sum_nonneg fun a _ => abs_nonneg _
  have h3 := abs_nonneg (nsq (rho n) - nsq (rhoN ε - rhoC ε))
  linarith

/- English proof (translation)
Establish `h1 : C * s ^ 2 ≤ (C * s) ^ 2`. Use polynomial arithmetic with `[mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ C - 1) (by linarith : (0:ℝ) ≤ C)) (sq_nonneg s)]`. Establish `h2 : 0 ≤ C * s` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem le_mul_of_sq_le_mul_sq {x C s : ℝ} (_hx : 0 ≤ x) (hC : 1 ≤ C) (hs : 1 ≤ s) (h : x ^ 2 ≤ C * s ^ 2) :
    x ≤ C * s := by
  have h1 : C * s ^ 2 ≤ (C * s) ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ C - 1) (by linarith : (0:ℝ) ≤ C))
      (sq_nonneg s)]
  have h2 : 0 ≤ C * s := by positivity
  nlinarith

section Datum

variable {n : ℕ} {ε : Fin n → Bool} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {w : M}

/- English proof (translation)
Establish `hb` using `b2Id`. Unfold `RaisingLoweringNormIdentities at hb`. Establish `h3` using `(hb n ε M E lam w hw).2.2`. Establish `h1 : ‖E b a w‖ ^ 2 ≤ ∑ b' ∈ univ.filter (fun b' => a < b' ∧ ε a ≠ ε b'), ‖E b' a w‖ ^ 2` using `single_le_sum (f := fun b' => ‖E b' a w‖ ^ 2) (fun _ _ => sq_nonneg _) (by simp [hab, hne])`. Establish `h2 : (∑ b' ∈ univ.filter (fun b' => a < b' ∧ ε a ≠ ε b'), ‖E b' a w‖ ^ 2) ≤ ∑ a', ∑ b' ∈ univ.filter (fun b' => a' < b' ∧ ε a' ≠ ε b'), ‖E b' a' w‖ ^ 2` using `single_le_sum (f := fun a' => ∑ b' ∈ univ.filter (fun b' => a' < b' ∧ ε a' ≠ ε b'), ‖E b' a' w‖ ^ 2) (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_univ a)`.

Establish `h4 : 0 ≤ ∑ a', ∑ b' ∈ univ.filter (fun b' => a' < b' ∧ ε a' ≠ ε b'), ‖E b' a' w‖ ^ 2` using `sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _`. Establish `h5` using `le_abs_self (nsq (rho n) - nsq (rhoN ε - rhoC ε))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem noncompact_lowering_norm_small (hw : IsHWDatum ε E lam w) {a b : Fin n} (hab : a < b) (hne : ε a ≠ ε b) :
    ‖E b a w‖ ^ 2 ≤ |nsq (rho n) - nsq (rhoN ε - rhoC ε)| := by
  have hb := b2Id
  unfold RaisingLoweringNormIdentities at hb
  have h3 := (hb n ε M E lam w hw).2.2
  have h1 : ‖E b a w‖ ^ 2 ≤ ∑ b' ∈ univ.filter (fun b' => a < b' ∧ ε a ≠ ε b'), ‖E b' a w‖ ^ 2 :=
    single_le_sum (f := fun b' => ‖E b' a w‖ ^ 2) (fun _ _ => sq_nonneg _) (by simp [hab, hne])
  have h2 : (∑ b' ∈ univ.filter (fun b' => a < b' ∧ ε a ≠ ε b'), ‖E b' a w‖ ^ 2) ≤
      ∑ a', ∑ b' ∈ univ.filter (fun b' => a' < b' ∧ ε a' ≠ ε b'), ‖E b' a' w‖ ^ 2 :=
    single_le_sum (f := fun a' => ∑ b' ∈ univ.filter (fun b' => a' < b' ∧ ε a' ≠ ε b'), ‖E b' a' w‖ ^ 2)
      (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (mem_univ a)
  have h4 : 0 ≤ ∑ a', ∑ b' ∈ univ.filter (fun b' => a' < b' ∧ ε a' ≠ ε b'), ‖E b' a' w‖ ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have h5 := le_abs_self (nsq (rho n) - nsq (rhoN ε - rhoC ε))
  linarith

/- English proof (translation)
Establish `hb` using `b2Id`. Unfold `RaisingLoweringNormIdentities at hb`. Take `⟨hI1, hI2, -⟩` from `hb n ε M E lam w hw`. Establish `hw1 : ‖w‖ = 1` using `hw.2.2.1`. Establish `hdiag : ∀ a, E a a w = ((lowK ε lam a : ℝ) : ℂ) • w` using `hw.2.2.2.1.1`.

Establish `hup : ∀ a b, a < b → ε a = ε b → E a b w = 0` using `hw.2.2.2.1.2`. Use `set C := highestWeightBoundConst ε d Λ₀ with hCdef`. Use `set K0 := nsq (rho n) - nsq (rhoN ε - rhoC ε) with hK0`. Use `set S := ∑ a, |d a| with hS`. Use `set T := ∑ a, |Λ₀ a| with hT`.

Establish `hC1 : 1 ≤ C` using `one_le_highestWeightBoundConst ε d Λ₀`. Establish `hCe : C = |K0| + 2 * S + 2 * T + 1` using `rfl`. Establish `hS0 : 0 ≤ S` using `sum_nonneg fun a _ => abs_nonneg _`. Establish `hT0 : 0 ≤ T` using `sum_nonneg fun a _ => abs_nonneg _`. Establish `hK0a` using `abs_nonneg K0`.

Establish `hdS : ∀ a, |d a| ≤ S` using `fun a => single_le_sum (f := fun a => |d a|) (fun _ _ => abs_nonneg _) (mem_univ a)`. Establish `hΛT : ∀ a, |Λ₀ a| ≤ T` using `fun a => single_le_sum (f := fun a => |Λ₀ a|) (fun _ _ => abs_nonneg _) (mem_univ a)`. Establish `hL : ∀ a, lowK ε lam a = t * d a + Λ₀ a`. Introduce `a`. Rewrite using `[hΛ]`.

Simplify using `[Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Establish `ht0 : 0 ≤ t` using `by linarith`. Establish `hdiff : ∀ a b, lowK ε lam a - lowK ε lam b ≤ (2 * S + 2 * T) * t`. Introduce `a b`. Rewrite using `[hL, hL]`.

Establish `e1 : t * d a ≤ t * |d a|` using `mul_le_mul_of_nonneg_left (le_abs_self _) ht0`. Establish `e2 : -(t * d b) ≤ t * |d b|`. Use `mul_le_mul_of_nonneg_left (neg_abs_le (d b)) ht0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e3` using `le_abs_self (Λ₀ a)`.

Establish `e4` using `neg_abs_le (Λ₀ b)`. Establish `e5 : t * |d a| ≤ t * S` using `mul_le_mul_of_nonneg_left (hdS a) ht0`. Establish `e6 : t * |d b| ≤ t * S` using `mul_le_mul_of_nonneg_left (hdS b) ht0`. Establish `e7` using `hΛT a`. Establish `e8` using `hΛT b`.

Establish `e9 : T ≤ T * t` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsqb : ∀ a b, a ≠ b → ‖E a b w‖ ^ 2 ≤ C * t`. Introduce `a b hab`. Establish `hKt : |K0| ≤ |K0| * t` using `by nlinarith`.

Apply the tactic sequence `rcases lt_or_gt_of_ne hab with h | h <;> by_cases he : ε a = ε b`. Rewrite using `[hup a b h he]`. Simplify using the standard rewrite rules. Check the signs of the components of the expression. Establish `h1` using `hI2 a b h he`.

Establish `h2` using `noncompact_lowering_norm_small hw h he`. Establish `h3` using `hdiff a b`. Rewrite using `[h1]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h1` using `hI1 b a h he.symm`.

Establish `h3` using `hdiff b a`. Rewrite using `[h1]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2` using `noncompact_lowering_norm_small hw h (Ne.symm he)`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hsq1 : 1 ≤ Real.sqrt t`. Rewrite using `[show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]`. Conclude with `Real.sqrt_le_sqrt ht`. Establish `hsq2 : Real.sqrt t ^ 2 = t` using `Real.sq_sqrt ht0`. Establish `hdg : ∀ a, ‖E a a w - (((t * d a : ℝ)) : ℂ) • w‖ = |Λ₀ a|`.

Introduce `a`. Rewrite using `[hdiag a, ← sub_smul, ← Complex.ofReal_sub, norm_smul, hw1, mul_one, hL a]`. Rewrite using `[show t * d a + Λ₀ a - t * d a = Λ₀ a by ring, Complex.norm_real, Real.norm_eq_abs]`. Apply the tactic sequence `have hentry : ∀ a b, ‖E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w‖ ≤ C * Real.sqrt t := by`. Introduce `a b`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, hdg]`. Use `hΛT a` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[if_neg hab, zero_smul, sub_zero]`. Conclude with `le_mul_of_sq_le_mul_sq (norm_nonneg _) hC1 hsq1 (by rw [hsq2]; exact hsqb a b hab)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Break down `hab with ⟨h, he, -⟩ | ⟨h, he⟩` into its components or cases.

Rewrite using `[hup a b h he, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `noncompact_lowering_norm_small hw h (Ne.symm he)`. Use `le_mul_of_sq_le_mul_sq (norm_nonneg (E a b w)) hC1 le_rfl (by nlinarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `a b hab`. Take `⟨he, hd⟩` from `hab`. Distinguish the cases in `h0 : a = b`. Substitute `h0` using the available equality. Rewrite using `[if_pos rfl, hdg]`.

Use `hΛT a` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg h0, zero_smul, sub_zero]`. Break down `lt_or_gt_of_ne h0 with h | h` into its components or cases. Rewrite using `[hup a b h he, norm_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hI1 b a h he.symm`. Rewrite `h1` using `[hL, hL, hd]`. Establish `e7` using `hΛT a`. Establish `e8` using `hΛT b`.

Establish `e3` using `neg_abs_le (Λ₀ a)`. Establish `e4` using `le_abs_self (Λ₀ b)`. Use `le_mul_of_sq_le_mul_sq (norm_nonneg (E a b w)) hC1 le_rfl (by rw [h1]; nlinarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `X`.

Establish `key : actM E X w - ((t : ℂ) * trace (dMat d * X)) • w = ∑ a, ∑ b, X a b • (E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w)`. Simplify using `only [smul_sub, Finset.sum_sub_distrib]`. Use `congr 1`. Simplify using `[actM, LinearMap.sum_apply]`. Simplify using `only [Matrix.trace, dMat, Matrix.diag, Matrix.diagonal_mul, ite_smul, zero_smul, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, smul_smul, Finset.mul_sum, Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_smul]`. Apply the tactic sequence `exact mul_le_mul_of_nonneg_left (hentry a b) (norm_nonneg _)))`. Use `_ = C * Real.sqrt t * l1 X := by`. Unfold `l1`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem highest_weight_datum_bounds {d Λ₀ : Fin n → ℝ} {t : ℝ} (ht : 1 ≤ t) (hw : IsHWDatum ε E lam w)
    (hΛ : lowK ε lam = t • d + Λ₀) :
    (∀ a b, InNP ε d a b → ‖E a b w‖ ≤ highestWeightBoundConst ε d Λ₀) ∧
      (∀ a b, InLL ε d a b →
        ‖E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w‖ ≤ highestWeightBoundConst ε d Λ₀) ∧
      ∀ X : Matrix (Fin n) (Fin n) ℂ,
        ‖actM E X w - ((t : ℂ) * trace (dMat d * X)) • w‖ ≤
          highestWeightBoundConst ε d Λ₀ * Real.sqrt t * l1 X := by
  have hb := b2Id
  unfold RaisingLoweringNormIdentities at hb
  obtain ⟨hI1, hI2, -⟩ := hb n ε M E lam w hw
  have hw1 : ‖w‖ = 1 := hw.2.2.1
  have hdiag : ∀ a, E a a w = ((lowK ε lam a : ℝ) : ℂ) • w := hw.2.2.2.1.1
  have hup : ∀ a b, a < b → ε a = ε b → E a b w = 0 := hw.2.2.2.1.2
  set C := highestWeightBoundConst ε d Λ₀ with hCdef
  set K0 := nsq (rho n) - nsq (rhoN ε - rhoC ε) with hK0
  set S := ∑ a, |d a| with hS
  set T := ∑ a, |Λ₀ a| with hT
  have hC1 : 1 ≤ C := one_le_highestWeightBoundConst ε d Λ₀
  have hCe : C = |K0| + 2 * S + 2 * T + 1 := rfl
  have hS0 : 0 ≤ S := sum_nonneg fun a _ => abs_nonneg _
  have hT0 : 0 ≤ T := sum_nonneg fun a _ => abs_nonneg _
  have hK0a := abs_nonneg K0
  have hdS : ∀ a, |d a| ≤ S := fun a =>
    single_le_sum (f := fun a => |d a|) (fun _ _ => abs_nonneg _) (mem_univ a)
  have hΛT : ∀ a, |Λ₀ a| ≤ T := fun a =>
    single_le_sum (f := fun a => |Λ₀ a|) (fun _ _ => abs_nonneg _) (mem_univ a)
  have hL : ∀ a, lowK ε lam a = t * d a + Λ₀ a := by
    intro a; rw [hΛ]; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have ht0 : 0 ≤ t := by linarith
  have hdiff : ∀ a b, lowK ε lam a - lowK ε lam b ≤ (2 * S + 2 * T) * t := by
    intro a b
    rw [hL, hL]
    have e1 : t * d a ≤ t * |d a| := mul_le_mul_of_nonneg_left (le_abs_self _) ht0
    have e2 : -(t * d b) ≤ t * |d b| := by
      have := mul_le_mul_of_nonneg_left (neg_abs_le (d b)) ht0; linarith
    have e3 := le_abs_self (Λ₀ a)
    have e4 := neg_abs_le (Λ₀ b)
    have e5 : t * |d a| ≤ t * S := mul_le_mul_of_nonneg_left (hdS a) ht0
    have e6 : t * |d b| ≤ t * S := mul_le_mul_of_nonneg_left (hdS b) ht0
    have e7 := hΛT a
    have e8 := hΛT b
    have e9 : T ≤ T * t := by nlinarith
    nlinarith
  have hsqb : ∀ a b, a ≠ b → ‖E a b w‖ ^ 2 ≤ C * t := by
    intro a b hab
    have hKt : |K0| ≤ |K0| * t := by nlinarith
    rcases lt_or_gt_of_ne hab with h | h <;> by_cases he : ε a = ε b
    · rw [hup a b h he]; simp; positivity
    · have h1 := hI2 a b h he
      have h2 := noncompact_lowering_norm_small hw h he
      have h3 := hdiff a b
      rw [h1]; nlinarith
    · have h1 := hI1 b a h he.symm
      have h3 := hdiff b a
      rw [h1]; nlinarith
    · have h2 := noncompact_lowering_norm_small hw h (Ne.symm he)
      nlinarith
  have hsq1 : 1 ≤ Real.sqrt t := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt ht
  have hsq2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
  have hdg : ∀ a, ‖E a a w - (((t * d a : ℝ)) : ℂ) • w‖ = |Λ₀ a| := by
    intro a
    rw [hdiag a, ← sub_smul, ← Complex.ofReal_sub, norm_smul, hw1, mul_one, hL a]
    rw [show t * d a + Λ₀ a - t * d a = Λ₀ a by ring, Complex.norm_real, Real.norm_eq_abs]
  have hentry : ∀ a b,
      ‖E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w‖ ≤ C * Real.sqrt t := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, hdg]
      have := hΛT a
      nlinarith
    · rw [if_neg hab, zero_smul, sub_zero]
      exact le_mul_of_sq_le_mul_sq (norm_nonneg _) hC1 hsq1 (by rw [hsq2]; exact hsqb a b hab)
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    rcases hab with ⟨h, he, -⟩ | ⟨h, he⟩
    · rw [hup a b h he, norm_zero]; linarith
    · have h2 := noncompact_lowering_norm_small hw h (Ne.symm he)
      have := le_mul_of_sq_le_mul_sq (norm_nonneg (E a b w)) hC1 le_rfl (by nlinarith)
      linarith
  · intro a b hab
    obtain ⟨he, hd⟩ := hab
    by_cases h0 : a = b
    · subst h0
      rw [if_pos rfl, hdg]
      have := hΛT a
      linarith
    · rw [if_neg h0, zero_smul, sub_zero]
      rcases lt_or_gt_of_ne h0 with h | h
      · rw [hup a b h he, norm_zero]; linarith
      · have h1 := hI1 b a h he.symm
        rw [hL, hL, hd] at h1
        have e7 := hΛT a
        have e8 := hΛT b
        have e3 := neg_abs_le (Λ₀ a)
        have e4 := le_abs_self (Λ₀ b)
        have := le_mul_of_sq_le_mul_sq (norm_nonneg (E a b w)) hC1 le_rfl (by rw [h1]; nlinarith)
        linarith
  · intro X
    have key : actM E X w - ((t : ℂ) * trace (dMat d * X)) • w =
        ∑ a, ∑ b, X a b • (E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      congr 1
      · simp [actM, LinearMap.sum_apply]
      · simp only [Matrix.trace, dMat, Matrix.diag, Matrix.diagonal_mul, ite_smul, zero_smul,
          smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, smul_smul,
          Finset.mul_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        push_cast
        ring
    rw [key]
    calc ‖∑ a, ∑ b, X a b • (E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w)‖
        ≤ ∑ a, ∑ b, ‖X a b‖ * (C * Real.sqrt t) :=
          (norm_sum_le _ _).trans (sum_le_sum fun a _ => (norm_sum_le _ _).trans
            (sum_le_sum fun b _ => by
              rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hentry a b) (norm_nonneg _)))
      _ = C * Real.sqrt t * l1 X := by
          unfold l1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring

end Datum

/- English proof (translation)
Introduce `n ε d Λ₀`. Use `⟨highestWeightBoundConst ε d Λ₀, le_trans zero_le_one (one_le_highestWeightBoundConst ε d Λ₀), ?_⟩` and prove the remaining obligations. Introduce `t ht M _ _ E lam w hw hΛ`. Conclude with `highest_weight_datum_bounds ht hw hΛ`.
-/
theorem b2 : HighestWeightVectorUniformBounds := by
  intro n ε d Λ₀
  refine ⟨highestWeightBoundConst ε d Λ₀, le_trans zero_le_one (one_le_highestWeightBoundConst ε d Λ₀), ?_⟩
  intro t ht M _ _ E lam w hw hΛ
  exact highest_weight_datum_bounds ht hw hΛ

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
