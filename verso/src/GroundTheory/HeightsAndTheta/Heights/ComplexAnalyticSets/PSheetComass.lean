import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetComass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFrameJacobianSum
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace SheetComassAlt

/- English proof (translation)
Use `set S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ ((fderiv ℂ s y : (Fin d → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).toLinearMap with hS`. Establish `hR : fderiv ℝ s y = (fderiv ℂ s y).restrictScalars ℝ` using `hs.fderiv_restrictScalars ℝ`. Establish `e : (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap ∘ₗ ((fderiv ℝ s y : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℂ)) ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap = S.restrictScalars ℝ`. Use extensionality with `v : 1`. Simplify using `[hS, hR]`.

Rewrite using `[sheetJac, e, FrameJacobianSumAlt.areaJacobian_restrictScalars, FrameJacobianSumAlt.det_adjoint_comp]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `[hS, Matrix.mul_apply, ReciprocityTheory.AnForm.A.jacC, PiLp.inner_apply, mul_comm]`.
-/
theorem sheetJac_eq_norm_det {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ)
    (hs : DifferentiableAt ℂ s y) :
    sheetJac s y = ‖((ReciprocityTheory.AnForm.A.jacC s y)ᴴ * ReciprocityTheory.AnForm.A.jacC s y).det‖ := by
  set S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
      ((fderiv ℂ s y : (Fin d → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
        (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).toLinearMap with hS
  have hR : fderiv ℝ s y = (fderiv ℂ s y).restrictScalars ℝ := hs.fderiv_restrictScalars ℝ
  have e : (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
      ((fderiv ℝ s y : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℂ)) ∘ₗ
        (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap = S.restrictScalars ℝ := by
    ext v : 1
    simp [hS, hR]
  rw [sheetJac, e, FrameJacobianSumAlt.areaJacobian_restrictScalars,
    FrameJacobianSumAlt.det_adjoint_comp]
  congr 2
  ext i j
  simp [hS, Matrix.mul_apply, ReciprocityTheory.AnForm.A.jacC, PiLp.inner_apply, mul_comm]

end SheetComassAlt

/- English proof (translation)
Introduce `n d J A φ R hφ`. Use `choose U hUo hZU hφU using hφ`. Establish `hK : IsCompact (zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R)` using `(isCompact_closedBall (0 : Fin n → ℂ) R).inter_left (SheetSumMeasurable.isClosed_zeroSet J)`. Take `⟨c, hc, hb⟩` from `TubeFormComparison.exists_hessC_bound φ _ hK U hUo (fun i => Set.inter_subset_left.trans (hZU i)) (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))`. Use `⟨(d.factorial : ℝ) * (2 / Real.pi) ^ d * (3 ^ d * c ^ d), fun x hx s hs => ?_⟩` and prove the remaining obligations.

Take `⟨V, hV, hyV, hsd, hsx, -, -⟩` from `hs`. Establish `hsa : AnalyticAt ℂ s (A *ᵥ x)` using `IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hV hsd _ hyV`. Establish `hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x))` using `fun i => by`. Rewrite using `[hsx]`. Conclude with `((hφU i).contDiffAt ((hUo i).mem_nhds (hZU i hx.1))).of_le (WithTop.coe_le_coe.2 le_top)`.

Use `set Jc := ReciprocityTheory.AnForm.A.jacC s (A *ᵥ x) with hJc`. Use `set B := Jc.map (starRingEnd ℂ) with hB`. Establish `hBJ : Bᴴ = Jcᵀ`. Use extensionality with `a b`. Simplify using `[hB]`.

Establish `hA : ∀ i, hessC (φ i ∘ s) (A *ᵥ x) = Bᴴ * hessC (φ i) x * B` using `fun i => by`. Establish `h` using `ReciprocityTheory.AnForm.A.hessC_comp (φ i) s _ hsa (hφx i)`. Rewrite `h` using `[hsx]`. Rewrite using `[hBJ]`. Conclude with `h`.

Establish `hle : ∀ k, ((fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k - (fun k => hessC (φ k ∘ s) (A *ᵥ x)) k).PosSemidef` using `fun k => by`. Establish `e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC (φ k) x * B = Bᴴ * (-hessC (φ k) x + (c : ℂ) • 1) * B`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Normalize the expressions using the abelian group laws. Simplify using `only [hA, e]`.

Conclude with `(hb k x hx).2.conjTranspose_mul_mul_same B`. Establish `hge : ∀ k, ((fun k => hessC (φ k ∘ s) (A *ᵥ x)) k + (fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k).PosSemidef` using `fun k => by`. Establish `e : Bᴴ * hessC (φ k) x * B + (c : ℂ) • (Bᴴ * B) = Bᴴ * (hessC (φ k) x + (c : ℂ) • 1) * B`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`. Simplify using `only [hA, e]`.

Conclude with `(hb k x hx).1.conjTranspose_mul_mul_same B`. Establish `key` using `ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le _ _ hle hge`. Rewrite `key` using `[ReciprocityTheory.AnForm.A.mdisc_const, Matrix.det_smul, Fintype.card_fin]`. Establish `hconj : Bᴴ * B = (Jcᴴ * Jc).map (starRingEnd ℂ)`. Rewrite using `[hBJ, hB]`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, mul_comm]`. Establish `hdet : ‖(Bᴴ * B).det‖ = sheetJac s (A *ᵥ x)`. Establish `hm : ((Jcᴴ * Jc).map (starRingEnd ℂ)).det = starRingEnd ℂ (Jcᴴ * Jc).det` using `(RingHom.map_det _ _).symm`. Rewrite using `[SheetComassAlt.sheetJac_eq_norm_det s _ (hsd.differentiableAt (hV.mem_nhds hyV)), hconj, hm, Complex.norm_conj]`.

Establish `hre : (((c : ℂ) ^ d * (Bᴴ * B).det).re) ≤ c ^ d * sheetJac s (A *ᵥ x)`. Use `(Complex.re_le_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc, hdet]`. Establish `hm : |(mdisc fun k => hessC (φ k ∘ s) (A *ᵥ x)).re| ≤ 3 ^ d * (c ^ d * sheetJac s (A *ᵥ x))` using `(Complex.abs_re_le_norm _).trans (key.trans (mul_le_mul_of_nonneg_left hre (by positivity)))`. Unfold `maDens`.

Rewrite using `[abs_mul, abs_of_nonneg (by positivity), mul_assoc _ (3 ^ d * c ^ d), mul_assoc (3 ^ d)]`. Conclude with `mul_le_mul_of_nonneg_left hm (by positivity)`.
-/
theorem SheetComass.proof : SheetComass.Statement := by
  intro n d J A φ R hφ
  choose U hUo hZU hφU using hφ
  have hK : IsCompact (zeroSet J ∩ Metric.closedBall (0 : Fin n → ℂ) R) :=
    (isCompact_closedBall (0 : Fin n → ℂ) R).inter_left (SheetSumMeasurable.isClosed_zeroSet J)
  obtain ⟨c, hc, hb⟩ := TubeFormComparison.exists_hessC_bound φ _ hK U hUo
    (fun i => Set.inter_subset_left.trans (hZU i))
    (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  refine ⟨(d.factorial : ℝ) * (2 / Real.pi) ^ d * (3 ^ d * c ^ d), fun x hx s hs => ?_⟩
  obtain ⟨V, hV, hyV, hsd, hsx, -, -⟩ := hs
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_differentiableOn hV hsd _ hyV
  have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
    rw [hsx]
    exact ((hφU i).contDiffAt ((hUo i).mem_nhds (hZU i hx.1))).of_le (WithTop.coe_le_coe.2 le_top)
  set Jc := ReciprocityTheory.AnForm.A.jacC s (A *ᵥ x) with hJc
  set B := Jc.map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = Jcᵀ := by
    ext a b
    simp [hB]
  have hA : ∀ i, hessC (φ i ∘ s) (A *ᵥ x) = Bᴴ * hessC (φ i) x * B := fun i => by
    have h := ReciprocityTheory.AnForm.A.hessC_comp (φ i) s _ hsa (hφx i)
    rw [hsx] at h
    rw [hBJ]
    exact h
  have hle : ∀ k, ((fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k -
      (fun k => hessC (φ k ∘ s) (A *ᵥ x)) k).PosSemidef := fun k => by
    have e : (c : ℂ) • (Bᴴ * B) - Bᴴ * hessC (φ k) x * B =
        Bᴴ * (-hessC (φ k) x + (c : ℂ) • 1) * B := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      abel
    simp only [hA, e]
    exact (hb k x hx).2.conjTranspose_mul_mul_same B
  have hge : ∀ k, ((fun k => hessC (φ k ∘ s) (A *ᵥ x)) k +
      (fun _ : Fin d => (c : ℂ) • (Bᴴ * B)) k).PosSemidef := fun k => by
    have e : Bᴴ * hessC (φ k) x * B + (c : ℂ) • (Bᴴ * B) =
        Bᴴ * (hessC (φ k) x + (c : ℂ) • 1) * B := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    simp only [hA, e]
    exact (hb k x hx).1.conjTranspose_mul_mul_same B
  have key := ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le _ _ hle hge
  rw [ReciprocityTheory.AnForm.A.mdisc_const, Matrix.det_smul, Fintype.card_fin] at key
  have hconj : Bᴴ * B = (Jcᴴ * Jc).map (starRingEnd ℂ) := by
    rw [hBJ, hB]
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  have hdet : ‖(Bᴴ * B).det‖ = sheetJac s (A *ᵥ x) := by
    have hm : ((Jcᴴ * Jc).map (starRingEnd ℂ)).det = starRingEnd ℂ (Jcᴴ * Jc).det :=
      (RingHom.map_det _ _).symm
    rw [SheetComassAlt.sheetJac_eq_norm_det s _ (hsd.differentiableAt (hV.mem_nhds hyV)), hconj, hm,
      Complex.norm_conj]
  have hre : (((c : ℂ) ^ d * (Bᴴ * B).det).re) ≤ c ^ d * sheetJac s (A *ᵥ x) := by
    refine (Complex.re_le_norm _).trans (le_of_eq ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hc, hdet]
  have hm : |(mdisc fun k => hessC (φ k ∘ s) (A *ᵥ x)).re| ≤ 3 ^ d * (c ^ d * sheetJac s (A *ᵥ x)) :=
    (Complex.abs_re_le_norm _).trans (key.trans (mul_le_mul_of_nonneg_left hre (by positivity)))
  unfold maDens
  rw [abs_mul, abs_of_nonneg (by positivity), mul_assoc _ (3 ^ d * c ^ d), mul_assoc (3 ^ d)]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

end

end GroundTheory.Heights₂.Heights
