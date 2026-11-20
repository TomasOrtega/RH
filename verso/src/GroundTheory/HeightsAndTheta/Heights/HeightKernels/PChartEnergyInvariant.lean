import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyInvariant
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergySwap
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartMassAffine
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartMassInvariant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyInvariance

open ChartMongeAmpereAffineInvariance

def EnergyInvariantUnder {e : ℕ} (C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : Prop :=
  ∀ M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ, M.PosDef → N.PosDef → ∀ k : ℕ,
    chartMixedEnergy (Cᴴ * M * C) (Cᴴ * N * C) k = chartMixedEnergy M N k

variable {e : ℕ}

/- English proof (translation)
The claim follows from `hM.conjTranspose_mul_mul_same (mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)))`.
-/
theorem posDef_conj {M C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (hC : C.det ≠ 0) :
    (Cᴴ * M * C).PosDef :=
  hM.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)))

/- English proof (translation)
Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem conj_mul (M A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    (A * B)ᴴ * M * (A * B) = Bᴴ * (Aᴴ * M * A) * B := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/- English proof (translation)
Introduce `M N hM hN k`. Rewrite using `[conj_mul, conj_mul, hB _ _ (posDef_conj hM hAdet) (posDef_conj hN hAdet), hA M N hM hN]`.
-/
theorem invariantUnder_mul {A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hA : EnergyInvariantUnder A)
    (hB : EnergyInvariantUnder B) (hAdet : A.det ≠ 0) : EnergyInvariantUnder (A * B) := by
  intro M N hM hN k
  rw [conj_mul, conj_mul, hB _ _ (posDef_conj hM hAdet) (posDef_conj hN hAdet), hA M N hM hN]

/- English proof (translation)
Introduce `M N hM hN k`. Rewrite using `[← hV _ _ (posDef_conj hM hC) (posDef_conj hN hC), ← conj_mul, ← conj_mul, hCV M N hM hN]`.
-/
theorem invariantUnder_of_mul_right {C V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hCV : EnergyInvariantUnder (C * V)) (hV : EnergyInvariantUnder V) (hC : C.det ≠ 0) :
    EnergyInvariantUnder C := by
  intro M N hM hN k
  rw [← hV _ _ (posDef_conj hM hC) (posDef_conj hN hC), ← conj_mul, ← conj_mul, hCV M N hM hN]

/- English proof (translation)
Establish `hQ : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det` using `(RingHom.map_det (starRingEnd ℂ) P).symm`. Establish `hH : ∀ j, cxHessian (fun y => φ j (c + P *ᵥ y) + κ) z = Pᵀ * cxHessian (φ j) (c + P *ᵥ z) * P.map (starRingEnd ℂ)` using `fun j => cxHessian_comp_affine (φ j) c P hP κ z`. Simplify using `only [maDensity, hH]`. Rewrite using `[mixedDisc_mul_mul (Pᵀ) (P.map (starRingEnd ℂ)) (fun j => cxHessian (φ j) (c + P *ᵥ z)), det_transpose, hQ, Complex.mul_conj, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDensity_comp_affine_family {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (c : Fin D → ℂ)
    (P : Matrix (Fin D) (Fin D) ℂ) (hP : P.det ≠ 0) (κ : ℝ) (z : Fin D → ℂ) :
    maDensity (fun j => fun y => φ j (c + P *ᵥ y) + κ) z =
      Complex.normSq P.det * maDensity φ (c + P *ᵥ z) := by
  have hQ : (P.map (starRingEnd ℂ)).det = starRingEnd ℂ P.det := (RingHom.map_det (starRingEnd ℂ) P).symm
  have hH : ∀ j, cxHessian (fun y => φ j (c + P *ᵥ y) + κ) z =
      Pᵀ * cxHessian (φ j) (c + P *ᵥ z) * P.map (starRingEnd ℂ) := fun j =>
    cxHessian_comp_affine (φ j) c P hP κ z
  simp only [maDensity, hH]
  rw [mixedDisc_mul_mul (Pᵀ) (P.map (starRingEnd ℂ)) (fun j => cxHessian (φ j) (c + P *ᵥ z)), det_transpose, hQ,
    Complex.mul_conj, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Introduce `M N hM hN k`. Establish `ht : T 0 0 ≠ 0` using `fun h => hdet (by rw [det_of_row_zero T hT, h, zero_mul])`. Establish `hC : (T.submatrix Fin.succ Fin.succ).det ≠ 0` using `fun h => hdet (by rw [det_of_row_zero T hT, h, mul_zero])`. Use `set P := (T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ with hPdef`. Use `set c : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) with hcdef`.

Establish `hP : P.det ≠ 0`. Rewrite using `[hPdef, det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hC`. Establish `hfM : hermChartPot (Tᴴ * M * T) = fun y => hermChartPot M (c + P *ᵥ y) + Real.log ‖T 0 0‖`. Use function extensionality and compare the values at `(hermChartPot_conj M T hM hT ht)`.

Establish `hfN : hermChartPot (Tᴴ * N * T) = fun y => hermChartPot N (c + P *ᵥ y) + Real.log ‖T 0 0‖`. Use function extensionality and compare the values at `(hermChartPot_conj N T hN hT ht)`. Use `set Φ : Fin e → (Fin e → ℂ) → ℝ := fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ`. Establish `hfam : (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) = fun j => fun y => Φ j (c + P *ᵥ y) + Real.log ‖T 0 0‖`. Use function extensionality and compare the values at `j y`.

Apply the tactic sequence `by_cases h : (j : ℕ) < k <;> simp [hΦ, h, hfM, hfN]`. Use `set f : (Fin e → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf`. Establish `hpt : ∀ y, (hermChartPot (Tᴴ * M * T) y - hermChartPot (Tᴴ * N * T) y) * maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) y = Complex.normSq P.det * f (c + P *ᵥ y)` using `fun y => by`. Rewrite using `[hfam, maDensity_comp_affine_family Φ c P hP, hfM, hfN, hf]`. Expand and normalize the polynomial expressions, which then agree.

Unfold `chartMixedEnergy`. Repeatedly rewrite using `[hpt]`. Rewrite using `[integral_const_mul, integral_comp_affine f c P hP, ← mul_assoc, mul_inv_cancel₀ (Complex.normSq_pos.mpr hP).ne', one_mul]`.
-/
theorem invariantUnder_of_row_zero (T : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hT : ∀ j : Fin e, T 0 j.succ = 0)
    (hdet : T.det ≠ 0) : EnergyInvariantUnder T := by
  intro M N hM hN k
  have ht : T 0 0 ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, zero_mul])
  have hC : (T.submatrix Fin.succ Fin.succ).det ≠ 0 := fun h => hdet (by rw [det_of_row_zero T hT, h, mul_zero])
  set P := (T 0 0)⁻¹ • T.submatrix Fin.succ Fin.succ with hPdef
  set c : Fin e → ℂ := (T 0 0)⁻¹ • (fun i => T i.succ 0) with hcdef
  have hP : P.det ≠ 0 := by
    rw [hPdef, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht)) hC
  have hfM : hermChartPot (Tᴴ * M * T) = fun y => hermChartPot M (c + P *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj M T hM hT ht)
  have hfN : hermChartPot (Tᴴ * N * T) = fun y => hermChartPot N (c + P *ᵥ y) + Real.log ‖T 0 0‖ :=
    funext (hermChartPot_conj N T hN hT ht)
  set Φ : Fin e → (Fin e → ℂ) → ℝ := fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ
  have hfam : (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) =
      fun j => fun y => Φ j (c + P *ᵥ y) + Real.log ‖T 0 0‖ := by
    funext j y
    by_cases h : (j : ℕ) < k <;> simp [hΦ, h, hfM, hfN]
  set f : (Fin e → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf
  have hpt : ∀ y, (hermChartPot (Tᴴ * M * T) y - hermChartPot (Tᴴ * N * T) y) *
      maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot (Tᴴ * M * T) else hermChartPot (Tᴴ * N * T)) y =
      Complex.normSq P.det * f (c + P *ᵥ y) := fun y => by
    rw [hfam, maDensity_comp_affine_family Φ c P hP, hfM, hfN, hf]
    ring
  unfold chartMixedEnergy
  simp_rw [hpt]
  rw [integral_const_mul, integral_comp_affine f c P hP, ← mul_assoc,
    mul_inv_cancel₀ (Complex.normSq_pos.mpr hP).ne', one_mul]

/- English proof (translation)
Establish `h01 : (0 : Fin (e + 1 + 1)) ≠ 1` using `by simp`. Use `set S : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ := swapFirstTwo e with hSdef`. Establish `hSinv : EnergyInvariantUnder S` using `fun M N hM hN k => hS e M N hM hN k`. Establish `hSdet : S.det ≠ 0`. Rewrite using `[hSdef, swapFirstTwo, det_permutation, Equiv.Perm.sign_swap h01]`.

Evaluate the numerical expressions. Use `set T : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ := (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ).updateRow 1 (C 0) with hTdef`. Establish `hT0 : ∀ j : Fin (e + 1), T 0 j.succ = 0` using `fun j => by`. Rewrite using `[hTdef, updateRow_ne h01, one_apply_ne (Fin.succ_ne_zero j).symm]`. Establish `hTdet : T.det = C 0 1`.

Establish `hrow : ∑ m, C 0 m • (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) m = C 0`. Use function extensionality and compare the values at `p`. Simplify using `[Finset.sum_apply, Matrix.one_apply]`. Establish `h` using `det_updateRow_sum (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) 1 (C 0)`. Rewrite `h` using `[hrow]`.

Simplify using `using h`. Establish `hTdet' : T.det ≠ 0` using `by rw [hTdet]; exact h1`. Establish `hST0 : ∀ m, C 0 m = (S * T) 0 m` using `fun m => by`. Rewrite using `[hSdef, swapFirstTwo, PEquiv.toMatrix_toPEquiv_mul, submatrix_apply, Equiv.swap_apply_left, id, hTdef, updateRow_self]`. Establish `hSTdet : (S * T).det ≠ 0`.

Rewrite using `[det_mul]`. Conclude with `mul_ne_zero hSdet hTdet'`. Establish `hU : IsUnit (S * T).det` using `isUnit_iff_ne_zero.mpr hSTdet`. Use `set A := C * (S * T)⁻¹ with hAdef`. Establish `hCA : C = A * (S * T)` using `by rw [hAdef, Matrix.mul_assoc, nonsing_inv_mul _ hU, Matrix.mul_one]`.

Establish `hA0 : ∀ j : Fin (e + 1), A 0 j.succ = 0` using `fun j => by`. Rewrite using `[hAdef, mul_apply]`. Repeatedly rewrite using `[hST0]`. Rewrite using `[← mul_apply, mul_nonsing_inv _ hU, one_apply_ne (Fin.succ_ne_zero j).symm]`. Establish `hAdet : A.det ≠ 0` using `fun h => hC (by rw [hCA, det_mul, h, zero_mul])`.

Establish `h` using `invariantUnder_mul (invariantUnder_of_row_zero A hA0 hAdet) (invariantUnder_mul hSinv (invariantUnder_of_row_zero T hT0 hTdet') hSdet) hAdet`. Rewrite `h` using `[← hCA]`. Then use the resulting hypothesis.
-/
theorem invariantUnder_of_row_one (hS : ChartEnergySwapInvariant.Statement)
    (C : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hC : C.det ≠ 0) (h1 : C 0 1 ≠ 0) :
    EnergyInvariantUnder C := by
  have h01 : (0 : Fin (e + 1 + 1)) ≠ 1 := by simp
  set S : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ := swapFirstTwo e with hSdef
  have hSinv : EnergyInvariantUnder S := fun M N hM hN k => hS e M N hM hN k
  have hSdet : S.det ≠ 0 := by
    rw [hSdef, swapFirstTwo, det_permutation, Equiv.Perm.sign_swap h01]
    norm_num
  set T : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
    (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ).updateRow 1 (C 0) with hTdef
  have hT0 : ∀ j : Fin (e + 1), T 0 j.succ = 0 := fun j => by
    rw [hTdef, updateRow_ne h01, one_apply_ne (Fin.succ_ne_zero j).symm]
  have hTdet : T.det = C 0 1 := by
    have hrow : ∑ m, C 0 m • (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) m = C 0 := by
      funext p
      simp [Finset.sum_apply, Matrix.one_apply]
    have h := det_updateRow_sum (1 : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) 1 (C 0)
    rw [hrow] at h
    simpa using h
  have hTdet' : T.det ≠ 0 := by rw [hTdet]; exact h1
  have hST0 : ∀ m, C 0 m = (S * T) 0 m := fun m => by
    rw [hSdef, swapFirstTwo, PEquiv.toMatrix_toPEquiv_mul, submatrix_apply, Equiv.swap_apply_left, id, hTdef,
      updateRow_self]
  have hSTdet : (S * T).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero hSdet hTdet'
  have hU : IsUnit (S * T).det := isUnit_iff_ne_zero.mpr hSTdet
  set A := C * (S * T)⁻¹ with hAdef
  have hCA : C = A * (S * T) := by rw [hAdef, Matrix.mul_assoc, nonsing_inv_mul _ hU, Matrix.mul_one]
  have hA0 : ∀ j : Fin (e + 1), A 0 j.succ = 0 := fun j => by
    rw [hAdef, mul_apply]
    simp_rw [hST0]
    rw [← mul_apply, mul_nonsing_inv _ hU, one_apply_ne (Fin.succ_ne_zero j).symm]
  have hAdet : A.det ≠ 0 := fun h => hC (by rw [hCA, det_mul, h, zero_mul])
  have h := invariantUnder_mul (invariantUnder_of_row_zero A hA0 hAdet)
    (invariantUnder_mul hSinv (invariantUnder_of_row_zero T hT0 hTdet') hSdet) hAdet
  rwa [← hCA] at h

end ChartEnergyInvariance

open ChartEnergyInvariance in

/- English proof (translation)
Introduce `e M N C hM hN hC k`. Distinguish the cases in `hrow : ∀ j : Fin e, C 0 j.succ = 0`. Conclude with `invariantUnder_of_row_zero C hrow hC M N hM hN k`. Use `push Not at hrow`. Take `⟨j, hj⟩` from `hrow`.

Consider the cases of `e with`. Consider the case `zero => exact j.elim0`. Consider the case `succ e => set V : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ := (Equiv.swap (1 : Fin (e + 1 + 1)) j.succ).permMatrix ℂ with hVdef`. Establish `hs0 : Equiv.swap (1 : Fin (e + 1 + 1)) j.succ 0 = 0` using `Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.succ_ne_zero j).symm`. Establish `hV0 : ∀ m : Fin (e + 1), V 0 m.succ = 0` using `fun m => by`.

Simplify using `[hVdef, PEquiv.toMatrix_apply, hs0, (Fin.succ_ne_zero m).symm]`. Establish `hVdet : V.det ≠ 0`. Rewrite using `[hVdef, det_permutation]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (1 : Fin (e + 1 + 1)) j.succ)) with h | h <;>`. Simplify using `[h]`.

Establish `hCV1 : (C * V) 0 1 ≠ 0`. Rewrite using `[hVdef, PEquiv.mul_toMatrix_toPEquiv, submatrix_apply, Equiv.symm_swap, Equiv.swap_apply_left, id]`. Conclude with `hj`. Establish `hCVdet : (C * V).det ≠ 0`. Rewrite using `[det_mul]`.

Conclude with `mul_ne_zero hC hVdet`. Conclude with `invariantUnder_of_mul_right (invariantUnder_of_row_one hS (C * V) hCVdet hCV1) (invariantUnder_of_row_zero V hV0 hVdet) hC M N hM hN k`.
-/
theorem ChartEnergyLinearInvariant.proof (hS : ChartEnergySwapInvariant.Statement) :
    ChartEnergyLinearInvariant.Statement := by
  intro e M N C hM hN hC k
  by_cases hrow : ∀ j : Fin e, C 0 j.succ = 0
  · exact invariantUnder_of_row_zero C hrow hC M N hM hN k
  · push Not at hrow
    obtain ⟨j, hj⟩ := hrow
    cases e with
    | zero => exact j.elim0
    | succ e =>
      set V : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
        (Equiv.swap (1 : Fin (e + 1 + 1)) j.succ).permMatrix ℂ with hVdef
      have hs0 : Equiv.swap (1 : Fin (e + 1 + 1)) j.succ 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.succ_ne_zero j).symm
      have hV0 : ∀ m : Fin (e + 1), V 0 m.succ = 0 := fun m => by
        simp [hVdef, PEquiv.toMatrix_apply, hs0, (Fin.succ_ne_zero m).symm]
      have hVdet : V.det ≠ 0 := by
        rw [hVdef, det_permutation]
        rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (1 : Fin (e + 1 + 1)) j.succ)) with h | h <;>
          simp [h]
      have hCV1 : (C * V) 0 1 ≠ 0 := by
        rw [hVdef, PEquiv.mul_toMatrix_toPEquiv, submatrix_apply, Equiv.symm_swap, Equiv.swap_apply_left, id]
        exact hj
      have hCVdet : (C * V).det ≠ 0 := by
        rw [det_mul]
        exact mul_ne_zero hC hVdet
      exact invariantUnder_of_mul_right (invariantUnder_of_row_one hS (C * V) hCVdet hCV1)
        (invariantUnder_of_row_zero V hV0 hVdet) hC M N hM hN k

end

end GroundTheory.Heights₂.Heights
