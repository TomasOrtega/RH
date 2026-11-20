import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.PolynomialBound

open Matrix

noncomputable section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section aux

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/- English proof (translation)
Distinguish the cases in `hv : v = 0`. Simplify using `[hv]`. Distinguish the cases in `hφ : DifferentiableAt ℝ φ t`. Conclude with `deriv_smul_const hφ v`. Establish `hn : ¬ DifferentiableAt ℝ (fun s => φ s • v) t`.

Introduce `h`. Take `⟨ℓ, -, hℓ⟩` from `exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)`. Apply `hφ` to reduce the goal to its premises. Establish `hv' : ℓ v ≠ 0` using `by rw [hℓ]; simpa using hv`. Establish `h2` using `(((ℓ.restrictScalars ℝ).differentiableAt).comp t h).const_mul (ℓ v)⁻¹`.

Use `h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)` and prove the remaining obligations. Use `show φ s = (ℓ v)⁻¹ * ℓ (φ s • v)`. Rewrite using `[map_smul, smul_eq_mul, mul_comm (φ s), ← mul_assoc, inv_mul_cancel₀ hv', one_mul]`. Rewrite using `[deriv_zero_of_not_differentiableAt hφ, deriv_zero_of_not_differentiableAt hn, zero_smul]`.
-/
private lemma deriv_smul_const_vec (φ : ℝ → ℂ) (v : E) (t : ℝ) :
    deriv (fun s => φ s • v) t = deriv φ t • v := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases hφ : DifferentiableAt ℝ φ t
  · exact deriv_smul_const hφ v
  · have hn : ¬ DifferentiableAt ℝ (fun s => φ s • v) t := by
      intro h
      obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.mpr hv)
      apply hφ
      have hv' : ℓ v ≠ 0 := by rw [hℓ]; simpa using hv
      have h2 := (((ℓ.restrictScalars ℝ).differentiableAt).comp t h).const_mul (ℓ v)⁻¹
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show φ s = (ℓ v)⁻¹ * ℓ (φ s • v)
      rw [map_smul, smul_eq_mul, mul_comm (φ s), ← mul_assoc, inv_mul_cancel₀ hv', one_mul]
    rw [deriv_zero_of_not_differentiableAt hφ, deriv_zero_of_not_differentiableAt hn, zero_smul]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `Dx`. Use `split_ifs`. Conclude with `deriv_smul_const_vec _ v 0`. Conclude with `deriv_smul_const_vec _ v 0`.
-/
private lemma Dx_smul_const (x : Bool × B.Mat k r) (f : B.Mat k r → ℂ) (v : E) :
    Dx x (fun g => f g • v) = fun g => Dx x f g • v := by
  funext g
  unfold Dx
  split_ifs
  · exact deriv_smul_const_vec _ v 0
  · exact deriv_smul_const_vec _ v 0

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons x w ih => show Dx x (Dw w (fun g => f g • v)) = fun g => Dx x (Dw w f) g • v`. Rewrite using `[ih]`. Conclude with `Dx_smul_const x _ v`.
-/
private lemma Dw_smul_const (w : List (Bool × B.Mat k r)) (f : B.Mat k r → ℂ) (v : E) :
    Dw w (fun g => f g • v) = fun g => Dw w f g • v := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w (fun g => f g • v)) = fun g => Dx x (Dw w f) g • v
    rw [ih]
    exact Dx_smul_const x _ v

/- English proof (translation)
Take `⟨q, hq, hPq⟩` from `h`. Use `⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, ?_⟩` and prove the remaining obligations. Use `(MvPolynomial.totalDegree_rename_le _ _).trans (le_trans ?_ hq)` and prove the remaining obligations. Conclude with `MvPolynomial.totalDegree_le_of_support_subset (MvPolynomial.support_map_subset (f := starRingEnd ℂ) q)`. Introduce `g`.

Establish `key : ∀ (p : MvPolynomial ((Fin N × Fin N) ⊕ (Fin N × Fin N)) ℂ) (y : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℂ), star (MvPolynomial.eval y p) = MvPolynomial.eval₂ (starRingEnd ℂ) (fun i => star (y i)) p`. Introduce `p y`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C c => rw [MvPolynomial.eval_C, MvPolynomial.eval₂_C, Complex.star_def]`. Consider the case `add p p' hp hp' => rw [map_add, star_add, hp, hp', MvPolynomial.eval₂_add]`.

Consider the case `mul_X p i hp`. Rewrite using `[map_mul, star_mul', hp, MvPolynomial.eval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]`. Use `show star (P g) = _`. Rewrite using `[MvPolynomial.eval_rename, MvPolynomial.eval_map, hPq g, key]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases i with ⟨a, b⟩ | ⟨a, b⟩ <;> simp`.
-/
theorem polyOK_star {N a : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : IsPolyDeg a P) :
    IsPolyDeg a (fun g => star (P g)) := by
  obtain ⟨q, hq, hPq⟩ := h

  refine ⟨MvPolynomial.rename Sum.swap (MvPolynomial.map (starRingEnd ℂ) q), ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_rename_le _ _).trans (le_trans ?_ hq)
    exact MvPolynomial.totalDegree_le_of_support_subset (MvPolynomial.support_map_subset (f := starRingEnd ℂ) q)
  · intro g

    have key : ∀ (p : MvPolynomial ((Fin N × Fin N) ⊕ (Fin N × Fin N)) ℂ) (y : (Fin N × Fin N) ⊕ (Fin N × Fin N) → ℂ),
        star (MvPolynomial.eval y p) = MvPolynomial.eval₂ (starRingEnd ℂ) (fun i => star (y i)) p := by
      intro p y
      induction p using MvPolynomial.induction_on with
      | C c => rw [MvPolynomial.eval_C, MvPolynomial.eval₂_C, Complex.star_def]
      | add p p' hp hp' => rw [map_add, star_add, hp, hp', MvPolynomial.eval₂_add]
      | mul_X p i hp =>
        rw [map_mul, star_mul', hp, MvPolynomial.eval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    show star (P g) = _
    rw [MvPolynomial.eval_rename, MvPolynomial.eval_map, hPq g, key]
    congr 1
    funext i
    rcases i with ⟨a, b⟩ | ⟨a, b⟩ <;> simp

/- English proof (translation)
Take `⟨hs, -⟩` from `polynomial_bound k r κ P hP`. Introduce `g₀ _`. Conclude with `⟨Set.univ, fun g => P g • v, isOpen_univ, Set.mem_univ _, (hs.smul contDiff_const).contDiffOn, fun _ _ _ => rfl⟩`.
-/
theorem polyOK_ck {κ : ℕ} {P : B.Mat k r → ℂ} (hP : IsPolyDeg κ P) (v : E) (UU : Set (B.Mat k r)) :
    B.CkOn ⊤ UU (fun g => P g • v) := by
  obtain ⟨hs, -⟩ := polynomial_bound k r κ P hP
  intro g₀ _
  exact ⟨Set.univ, fun g => P g • v, isOpen_univ, Set.mem_univ _,
    (hs.smul contDiff_const).contDiffOn, fun _ _ _ => rfl⟩

/- English proof (translation)
Take `⟨-, hB⟩` from `polynomial_bound k r κ P hP`. Take `⟨C₀, hC₀⟩` from `hB m`. Use `⟨max C₀ 0 * ‖v‖, mul_nonneg (le_max_right _ _) (norm_nonneg _), ?_⟩` and prove the remaining obligations. Introduce `u w hu hw hl g hg`. Establish `h1` using `hC₀ u w hu hw hl g hg`.

Establish `hs : ((u ++ w).map (fun _ : B.Mat k r => (0 : ℕ))).sum = 0` using `by simp`. Rewrite `h1` using `[hs, Nat.cast_zero, add_zero, dLR_eq]`. Establish `hg1 : 1 ≤ B.gN g` using `gN_ge_one hg`. Establish `e0 : 0 ≤ B.gN g ^ (κ : ℝ)` using `Real.rpow_nonneg (zero_le_one.trans hg1) _`. Establish `hpow : B.gN g ^ (κ : ℝ) ≤ B.gN g ^ d` using `Real.rpow_le_rpow_of_exponent_le hg1 hd`.

Establish `hC : ‖Dw (wL u ++ wR w) P g‖ ≤ max C₀ 0 * B.gN g ^ d` using `h1.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) e0).trans (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))`. Rewrite using `[dLR_eq, Dw_smul_const, norm_smul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem polyOK_bound {κ : ℕ} {P : B.Mat k r → ℂ} (hP : IsPolyDeg κ P) (v : E) {d : ℝ} (hd : (κ : ℝ) ≤ d) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u w : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) →
      u.length + w.length ≤ m → ∀ g ∈ B.GV k r, ‖B.dLR u w (fun g => P g • v) g‖ ≤ C * B.gN g ^ d := by
  obtain ⟨-, hB⟩ := polynomial_bound k r κ P hP
  obtain ⟨C₀, hC₀⟩ := hB m
  refine ⟨max C₀ 0 * ‖v‖, mul_nonneg (le_max_right _ _) (norm_nonneg _), ?_⟩
  intro u w hu hw hl g hg
  have h1 := hC₀ u w hu hw hl g hg
  have hs : ((u ++ w).map (fun _ : B.Mat k r => (0 : ℕ))).sum = 0 := by simp
  rw [hs, Nat.cast_zero, add_zero, dLR_eq] at h1

  have hg1 : 1 ≤ B.gN g := gN_ge_one hg
  have e0 : 0 ≤ B.gN g ^ (κ : ℝ) := Real.rpow_nonneg (zero_le_one.trans hg1) _
  have hpow : B.gN g ^ (κ : ℝ) ≤ B.gN g ^ d := Real.rpow_le_rpow_of_exponent_le hg1 hd
  have hC : ‖Dw (wL u ++ wR w) P g‖ ≤ max C₀ 0 * B.gN g ^ d :=
    h1.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) e0).trans
      (mul_le_mul_of_nonneg_left hpow (le_max_right _ _)))
  rw [dLR_eq, Dw_smul_const, norm_smul]
  calc ‖Dw (wL u ++ wR w) P g‖ * ‖v‖ ≤ max C₀ 0 * B.gN g ^ d * ‖v‖ :=
        mul_le_mul_of_nonneg_right hC (norm_nonneg _)
    _ = max C₀ 0 * ‖v‖ * B.gN g ^ d := by ring

end aux

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact Nat.zero_le _`. Consider the case `cons a l ih => exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))`.
-/
private lemma foldr_max_zero_le_of_forall_le {o : ℕ} (l : List ℕ) (h : ∀ a ∈ l, a ≤ o) : l.foldr max 0 ≤ o := by

  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih => exact max_le (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ o κ Θ hΘ`. Use `⟨fun UU T hT => ?_, fun d hd T hT => ?_, ?_⟩` and prove the remaining obligations. Take `⟨-, P, hP, hc, hca⟩` from `hΘ T hT`. Rewrite using `[show T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hc, show T.coefAdj = fun g => star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hca]`. Conclude with `⟨polyOK_ck hP _ UU, polyOK_ck (polyOK_star hP) _ UU⟩`.

Take `⟨-, P, hP, hc, hca⟩` from `hΘ T hT`. Rewrite using `[show T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hc, show T.coefAdj = fun g => star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hca]`. Use `⟨polyOK_ck hP _ _, polyOK_ck (polyOK_star hP) _ _, fun m => ?_⟩` and prove the remaining obligations. Take `⟨C₁, -, h₁⟩` from `polyOK_bound hP (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) hd m`. Take `⟨C₂, -, h₂⟩` from `polyOK_bound (polyOK_star hP) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) hd m`.

Use `⟨max C₁ C₂, fun u w hu hw hl g hg => ?_⟩` and prove the remaining obligations. Establish `hx : 0 ≤ B.gN g ^ d` using `Real.rpow_nonneg (zero_le_one.trans (gN_ge_one hg)) d`. Conclude with `⟨(h₁ u w hu hw hl g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx), (h₂ u w hu hw hl g hg).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)⟩`. Use `show (Θ.map fun T => T.word.length).foldr max 0 ≤ o`. Use `foldr_max_zero_le_of_forall_le _ fun a ha => ?_` and prove the remaining obligations.

Take `⟨T, hT, rfl⟩` from `List.mem_map.mp ha`. Conclude with `(hΘ T hT).1`.
-/
theorem polyOp_ok : Formalism.FourierDecayAlt.P.CutMP.JDPolyOK := by
  intro k r Wp Wq _ _ _ _ _ o κ Θ hΘ
  refine ⟨fun UU T hT => ?_, fun d hd T hT => ?_, ?_⟩
  · obtain ⟨-, P, hP, hc, hca⟩ := hΘ T hT
    rw [show T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hc,
      show T.coefAdj = fun g => star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hca]
    exact ⟨polyOK_ck hP _ UU, polyOK_ck (polyOK_star hP) _ UU⟩
  · obtain ⟨-, P, hP, hc, hca⟩ := hΘ T hT
    rw [show T.coef = fun g => P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hc,
      show T.coefAdj = fun g => star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) from funext hca]
    refine ⟨polyOK_ck hP _ _, polyOK_ck (polyOK_star hP) _ _, fun m => ?_⟩
    obtain ⟨C₁, -, h₁⟩ := polyOK_bound hP (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) hd m
    obtain ⟨C₂, -, h₂⟩ := polyOK_bound (polyOK_star hP) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) hd m
    refine ⟨max C₁ C₂, fun u w hu hw hl g hg => ?_⟩
    have hx : 0 ≤ B.gN g ^ d := Real.rpow_nonneg (zero_le_one.trans (gN_ge_one hg)) d
    exact ⟨(h₁ u w hu hw hl g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx),
      (h₂ u w hu hw hl g hg).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx)⟩
  · show (Θ.map fun T => T.word.length).foldr max 0 ≤ o
    refine foldr_max_zero_le_of_forall_le _ fun a ha => ?_
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp ha
    exact (hΘ T hT).1

end GlobalTheory.HatNF
