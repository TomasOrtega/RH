import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Wedge

open ComplexOrder in

/- English proof (translation)
Introduce `hD ι κ _ _ _ U W`. Establish `hG : (Uᴴ * U).PosSemidef` using `posSemidef_conjTranspose_mul_self U`. Establish `hH : (Wᴴ * W).PosSemidef` using `posSemidef_conjTranspose_mul_self W`. Establish `hHn : 0 ≤ ((Wᴴ * W).det).re` using `(Complex.le_def.1 hH.det_nonneg).1`. Establish `hGn : 0 ≤ ((Uᴴ * U).det).re` using `(Complex.le_def.1 hG.det_nonneg).1`.

Establish `hGim : ((Uᴴ * U).det).im = 0` using `((Complex.le_def.1 hG.det_nonneg).2).symm`. Unfold `nI`. Distinguish the cases in `hdet : (Uᴴ * U).det = 0`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 hdet`. Establish `hUv : U *ᵥ v = 0`.

Use `(Matrix.conjTranspose_mul_self_mulVec_eq_zero U v).1 hv` as an intermediate fact. Conclude with `this`. Establish `hM : ((Uᴴ * W)ᴴ) *ᵥ v = 0`. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec, hUv, Matrix.mulVec_zero]`. Establish `hd : ((Uᴴ * W)ᴴ).det = 0` using `Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, hM⟩`.

Establish `hd' : (Uᴴ * W).det = 0`. Rewrite `hd` using `[det_conjTranspose]`. Simplify using `using hd`. Rewrite using `[hd', norm_zero]`. Establish `: ((Uᴴ * U).det).re * ((Wᴴ * W).det).re ≥ 0` using `mul_nonneg hGn hHn`.

Simplify using `using this`. Use `set G := Uᴴ * U with hGdef set M := Uᴴ * W with hMdef`. Establish `hu : IsUnit G.det` using `isUnit_iff_ne_zero.2 hdet`. Establish `hGi : G * G⁻¹ = 1` using `mul_nonsing_inv _ hu`. Establish `hiG : G⁻¹ * G = 1` using `nonsing_inv_mul _ hu`.

Establish `hGh : Gᴴ = G` using `hG.isHermitian`. Establish `hih : (G⁻¹)ᴴ = G⁻¹` using `by rw [conjTranspose_nonsing_inv, hGh]`. Establish `hMh : Mᴴ = Wᴴ * U`. Rewrite using `[hMdef, conjTranspose_mul, conjTranspose_conjTranspose]`. Use `set T := G⁻¹ * M with hT`.

Establish `hTh : Tᴴ = Mᴴ * G⁻¹` using `by rw [hT, conjTranspose_mul, hih]`. Establish `hGT : G * T = M` using `by rw [hT, ← Matrix.mul_assoc, hGi, Matrix.one_mul]`. Establish `hX : (Tᴴ * G * T).PosSemidef` using `hG.conjTranspose_mul_mul_same T`. Establish `hXe : Tᴴ * G * T = Mᴴ * T`. Rewrite using `[Matrix.mul_assoc, hGT, hTh, Matrix.mul_assoc, ← hT]`.

Establish `hXp : (Mᴴ * T).PosSemidef` using `hXe ▸ hX`. Establish `e1 : Wᴴ * (U * T) = Mᴴ * T` using `by rw [hMh, Matrix.mul_assoc]`. Establish `e2 : Tᴴ * Uᴴ * W = Mᴴ * T`. Rewrite using `[Matrix.mul_assoc, ← hMdef, hTh, Matrix.mul_assoc, ← hT]`. Establish `e3 : Tᴴ * Uᴴ * (U * T) = Mᴴ * T`.

Rewrite using `[← hXe, hGdef]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hZ : (W - U * T)ᴴ * (W - U * T) = Wᴴ * W - Mᴴ * T`. Rewrite using `[conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, e1, e2, e3]`. Normalize the expressions using the abelian group laws.

Establish `hmono : ((Mᴴ * T).det).re ≤ ((Wᴴ * W).det).re` using `hD κ _ _ hXp (hZ ▸ posSemidef_conjTranspose_mul_self (W - U * T))`. Establish `hiGd : (G⁻¹).det * G.det = 1` using `by rw [← det_mul, hiG, det_one]`. Establish `hdX : (Mᴴ * T).det * G.det = ((‖M.det‖ ^ 2 : ℝ) : ℂ)`. Establish `hc : (starRingEnd ℂ) M.det * M.det = ((‖M.det‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.conj_mul']`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[det_mul, hT, det_mul, det_conjTranspose, ← hc, Complex.star_def]`. Take the linear combination `((starRingEnd ℂ) M.det * M.det) * hiGd`. Establish `hre : ((Mᴴ * T).det).re * G.det.re = ‖M.det‖ ^ 2`.

Use `congrArg Complex.re hdX` as an intermediate fact. Rewrite `this` using `[Complex.mul_re, hGim, mul_zero, sub_zero, Complex.ofReal_re]`. Conclude with `this`. Rewrite using `[← hre, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_left hmono hGn`.
-/
theorem pairI_of_detMono : DetMono → PairI := by
  intro hD ι κ _ _ _ U W
  have hG : (Uᴴ * U).PosSemidef := posSemidef_conjTranspose_mul_self U
  have hH : (Wᴴ * W).PosSemidef := posSemidef_conjTranspose_mul_self W
  have hHn : 0 ≤ ((Wᴴ * W).det).re := (Complex.le_def.1 hH.det_nonneg).1
  have hGn : 0 ≤ ((Uᴴ * U).det).re := (Complex.le_def.1 hG.det_nonneg).1
  have hGim : ((Uᴴ * U).det).im = 0 := ((Complex.le_def.1 hG.det_nonneg).2).symm
  unfold nI
  by_cases hdet : (Uᴴ * U).det = 0
  ·
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hUv : U *ᵥ v = 0 := by
      have := (Matrix.conjTranspose_mul_self_mulVec_eq_zero U v).1 hv
      exact this
    have hM : ((Uᴴ * W)ᴴ) *ᵥ v = 0 := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec, hUv,
        Matrix.mulVec_zero]
    have hd : ((Uᴴ * W)ᴴ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, hM⟩
    have hd' : (Uᴴ * W).det = 0 := by
      rw [det_conjTranspose] at hd
      simpa using hd
    rw [hd', norm_zero]
    have : ((Uᴴ * U).det).re * ((Wᴴ * W).det).re ≥ 0 := mul_nonneg hGn hHn
    simpa using this
  · set G := Uᴴ * U with hGdef
    set M := Uᴴ * W with hMdef
    have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
    have hGi : G * G⁻¹ = 1 := mul_nonsing_inv _ hu
    have hiG : G⁻¹ * G = 1 := nonsing_inv_mul _ hu
    have hGh : Gᴴ = G := hG.isHermitian
    have hih : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hGh]
    have hMh : Mᴴ = Wᴴ * U := by
      rw [hMdef, conjTranspose_mul, conjTranspose_conjTranspose]
    set T := G⁻¹ * M with hT
    have hTh : Tᴴ = Mᴴ * G⁻¹ := by rw [hT, conjTranspose_mul, hih]
    have hGT : G * T = M := by rw [hT, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
    have hX : (Tᴴ * G * T).PosSemidef := hG.conjTranspose_mul_mul_same T
    have hXe : Tᴴ * G * T = Mᴴ * T := by
      rw [Matrix.mul_assoc, hGT, hTh, Matrix.mul_assoc, ← hT]
    have hXp : (Mᴴ * T).PosSemidef := hXe ▸ hX
    have e1 : Wᴴ * (U * T) = Mᴴ * T := by rw [hMh, Matrix.mul_assoc]
    have e2 : Tᴴ * Uᴴ * W = Mᴴ * T := by
      rw [Matrix.mul_assoc, ← hMdef, hTh, Matrix.mul_assoc, ← hT]
    have e3 : Tᴴ * Uᴴ * (U * T) = Mᴴ * T := by
      rw [← hXe, hGdef]
      simp only [Matrix.mul_assoc]

    have hZ : (W - U * T)ᴴ * (W - U * T) = Wᴴ * W - Mᴴ * T := by
      rw [conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
        e1, e2, e3]
      abel
    have hmono : ((Mᴴ * T).det).re ≤ ((Wᴴ * W).det).re :=
      hD κ _ _ hXp (hZ ▸ posSemidef_conjTranspose_mul_self (W - U * T))
    have hiGd : (G⁻¹).det * G.det = 1 := by rw [← det_mul, hiG, det_one]
    have hdX : (Mᴴ * T).det * G.det = ((‖M.det‖ ^ 2 : ℝ) : ℂ) := by
      have hc : (starRingEnd ℂ) M.det * M.det = ((‖M.det‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul']
        push_cast
        rfl
      rw [det_mul, hT, det_mul, det_conjTranspose, ← hc, Complex.star_def]
      linear_combination ((starRingEnd ℂ) M.det * M.det) * hiGd
    have hre : ((Mᴴ * T).det).re * G.det.re = ‖M.det‖ ^ 2 := by
      have := congrArg Complex.re hdX
      rw [Complex.mul_re, hGim, mul_zero, sub_zero, Complex.ofReal_re] at this
      exact this
    rw [← hre, mul_comm]
    exact mul_le_mul_of_nonneg_left hmono hGn

end GlobalTheory.CompanionTheory.Wedge
