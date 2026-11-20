import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.InfNorm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Introduce `F _ _ _ g b hb k hk hg`. Take `⟨hdk, hab⟩` from `M.detK F k hk`. Use `set t := Matrix.GeneralLinearGroup.det k with ht`. Establish `hk' : (dM t)⁻¹ * k ∈ Reduction.maxCompact (K` using `F) (n := 2) := mul_mem (inv_mem hdk) hk`. Establish `hd : Matrix.GeneralLinearGroup.det (dM t) = t`.

Use `Units.ext ?_` and prove the remaining obligations. Simplify using `[dM, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`. Establish `hdet : Matrix.GeneralLinearGroup.det ((dM t)⁻¹ * k) = 1`. Rewrite using `[map_mul, map_inv, hd, ← ht, inv_mul_cancel]`. Set `s : G1 F` to `⟨((dM t)⁻¹ * k).val, by`.

Establish `h1` using `congrArg Units.val hdet`. Simplify `h1⟩` using `[Matrix.GeneralLinearGroup.val_det_apply]`. Establish `hs : gl s = (dM t)⁻¹ * k` using `Units.ext rfl`. Establish `hsK : s ∈ KK F`. Rewrite using `[(M.kkCpt F).1]`.

Use `show gl s ∈ Reduction.maxCompact (K := F) (n := 2)`. Rewrite using `[hs]`. Conclude with `hk'`. Establish `hc : gl (g * s⁻¹) = b * dM t`. Establish `hm : ∀ x y : G1 F, gl (x * y) = gl x * gl y` using `fun x y => map_mul _ x y`.

Establish `h1 : gl (g * s⁻¹) = gl g * (gl s)⁻¹`. Rewrite using `[hm, eq_inv_of_mul_eq_one_left (a := gl s⁻¹) (b := gl s) (by rw [← hm, inv_mul_cancel]; exact map_one _)]`. Rewrite using `[h1, hs, hg]`. Use `group`. Establish `hv : (g * s⁻¹).1 = (b : Matrix (Fin 2) (Fin 2) (A F)) * (dM t).val` using `congrArg Units.val hc`.

Establish `hlow : (b : Matrix (Fin 2) (Fin 2) (A F)) 1 0 = 0` using `(Reduction.mem_adelicBorel.1 hb) (show (0 : Fin 2) < 1 by decide)`. Establish `e00 : (g * s⁻¹).1 0 0 = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0`. Rewrite using `[hv]`. Simplify using `[dM, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e01 : (g * s⁻¹).1 0 1 = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F)`.

Rewrite using `[hv]`. Simplify using `[dM, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e10 : (g * s⁻¹).1 1 0 = 0`. Rewrite using `[hv]`. Simplify using `[dM, Matrix.mul_apply, Fin.sum_univ_two, hlow]`.

Establish `e11 : (g * s⁻¹).1 1 1 = (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F)`. Rewrite using `[hv]`. Simplify using `[dM, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `hdet2 : (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 * ((b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F)) = 1`. Establish `h1` using `(g * s⁻¹).det_coe`.

Rewrite `h1` using `[Matrix.det_fin_two, e00, e01, e10, e11, mul_zero, sub_zero]`. Conclude with `h1`. Set `a : (A F)ˣ` to `(Reduction.isUnit_apply_self_of_mem_adelicBorel hb 0).unit`. Establish `ha : (a : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0` using `IsUnit.unit_spec _`. Establish `hinv : ((a⁻¹ : (A F)ˣ) : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F)` using `Units.inv_eq_of_mul_eq_one_right (by rw [ha]; exact hdet2)`.

Establish `hh : g * s⁻¹ = nU ((b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) * (a : A F)) * mD a`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[M.val_mul (nU _) (mD a)]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`.

Simplify `e00` using `[nU, mD, Matrix.mul_apply, Fin.sum_univ_two, ha]`. Simplify `e01` using `[nU, mD, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]`. Simplify `e10` using `[nU, mD, Matrix.mul_apply, Fin.sum_univ_two]`. Simplify `e11` using `[nU, mD, Matrix.mul_apply, Fin.sum_univ_two, hinv]`. Use `⟨(b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) * (a : A F), a, s, hsK, ?_, ha, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hh, inv_mul_cancel_right]`. Establish `hb11 : (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 = ((a⁻¹ * t⁻¹ : (A F)ˣ) : A F)`. Rewrite using `[Units.val_mul, hinv, mul_assoc, Units.mul_inv, mul_one]`. Rewrite using `[hb11, Reduction.adeleAbs_units]`. Use `show ab (a⁻¹ * t⁻¹) = _`.

Rewrite using `[M.ab_mul, M.ab_inv, M.ab_inv, hab, inv_one, mul_one]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.M.fromGL :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∀ (g : G1 F), ∀ b ∈ Reduction.adelicBorel (K := F) (n := 2), ∀ k ∈ Reduction.maxCompact (K := F) (n := 2), gl g = b * k → ∃ (x : A F) (a : (A F)ˣ), ∃ k' ∈ KK F, g = nU x * mD a * k' ∧ (a : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 ∧ Reduction.adeleAbs ((b : Matrix (Fin 2) (Fin 2) (A F)) 1 1) = (ab a)⁻¹ := by
  intro F _ _ _ g b hb k hk hg
  obtain ⟨hdk, hab⟩ := M.detK F k hk
  set t := Matrix.GeneralLinearGroup.det k with ht
  have hk' : (dM t)⁻¹ * k ∈ Reduction.maxCompact (K := F) (n := 2) := mul_mem (inv_mem hdk) hk
  have hd : Matrix.GeneralLinearGroup.det (dM t) = t := by
    refine Units.ext ?_
    simp [dM, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have hdet : Matrix.GeneralLinearGroup.det ((dM t)⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hd, ← ht, inv_mul_cancel]
  let s : G1 F := ⟨((dM t)⁻¹ * k).val, by
    have h1 := congrArg Units.val hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using h1⟩
  have hs : gl s = (dM t)⁻¹ * k := Units.ext rfl
  have hsK : s ∈ KK F := by
    rw [(M.kkCpt F).1]
    show gl s ∈ Reduction.maxCompact (K := F) (n := 2)
    rw [hs]
    exact hk'
  have hc : gl (g * s⁻¹) = b * dM t := by
    have hm : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
    have h1 : gl (g * s⁻¹) = gl g * (gl s)⁻¹ := by
      rw [hm, eq_inv_of_mul_eq_one_left (a := gl s⁻¹) (b := gl s) (by rw [← hm, inv_mul_cancel]; exact map_one _)]
    rw [h1, hs, hg]
    group
  have hv : (g * s⁻¹).1 = (b : Matrix (Fin 2) (Fin 2) (A F)) * (dM t).val :=
    congrArg Units.val hc
  have hlow : (b : Matrix (Fin 2) (Fin 2) (A F)) 1 0 = 0 :=
    (Reduction.mem_adelicBorel.1 hb) (show (0 : Fin 2) < 1 by decide)
  have e00 : (g * s⁻¹).1 0 0 = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * s⁻¹).1 0 1 = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * s⁻¹).1 1 0 = 0 := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two, hlow]
  have e11 : (g * s⁻¹).1 1 1 = (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F) := by
    rw [hv]; simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet2 : (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 * ((b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F)) = 1 := by
    have h1 := (g * s⁻¹).det_coe
    rw [Matrix.det_fin_two, e00, e01, e10, e11, mul_zero, sub_zero] at h1
    exact h1
  let a : (A F)ˣ := (Reduction.isUnit_apply_self_of_mem_adelicBorel hb 0).unit
  have ha : (a : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 0 0 := IsUnit.unit_spec _
  have hinv : ((a⁻¹ : (A F)ˣ) : A F) = (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 * (t : A F) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [ha]; exact hdet2)
  have hh : g * s⁻¹ = nU ((b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) * (a : A F)) * mD a := by
    refine Subtype.ext ?_
    rw [M.val_mul (nU _) (mD a)]
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, ha] using e00
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc] using e01
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two] using e10
    · simpa [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, hinv] using e11
  refine ⟨(b : Matrix (Fin 2) (Fin 2) (A F)) 0 1 * (t : A F) * (a : A F), a, s, hsK, ?_, ha, ?_⟩
  · rw [← hh, inv_mul_cancel_right]
  · have hb11 : (b : Matrix (Fin 2) (Fin 2) (A F)) 1 1 = ((a⁻¹ * t⁻¹ : (A F)ˣ) : A F) := by
      rw [Units.val_mul, hinv, mul_assoc, Units.mul_inv, mul_one]
    rw [hb11, Reduction.adeleAbs_units]
    show ab (a⁻¹ * t⁻¹) = _
    rw [M.ab_mul, M.ab_inv, M.ab_inv, hab, inv_one, mul_one]
