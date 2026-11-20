import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InvCancelRight

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ} {lam : Fin n → ℤ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lefΓ_apply : lefΓ n lam = cjL lam (gamM (-1 : Matrix (Md n) (Md n) ℂ) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lefS_apply (s : ℝ) : lefS n lam s =
    cjL lam (gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lefT_apply : lefT n lam = cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam) := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem lefS_zero : lefS n lam 0 =
    cjL lam (gamM (0 : Matrix (Md n) (Md n) ℂ) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := by
  rw [lefS_apply, Complex.ofReal_zero, zero_smul]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem neg_kron' {ι₁ ι₂ : Type*} (A : Matrix ι₁ ι₁ ℂ) (B : Matrix ι₂ ι₂ ℂ) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext i j; simp [kroneckerMap_apply, neg_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem smul_one_mulVec' {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁] (s : ℂ) (v : ι₁ → ℂ) :
    (s • (1 : Matrix ι₁ ι₁ ℂ)) *ᵥ v = s • v := by
  rw [Matrix.smul_mulVec, one_mulVec]

section

variable (hu : IsUnit (sqQ lam)) (hG : GamMul) (hC : GamCre)
include hu hG

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gam_mul' (g h : Matrix (Md n) (Md n) ℂ) : gamM g * gamM h = gamM (g * h) := ((hG n).2 g h).symm

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem Γsq_f : lefΓ n lam * lefΓ n lam = 1 := by
  rw [lefΓ_apply, cj_mul hu, ← mul_kronecker_mul, gam_mul' hu hG, neg_one_mul, neg_neg, (hG n).1, mul_one,
    one_kronecker_one, cj_one hu]

include hC in
/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem Γε_f (H : Mat n) : lefΓ n lam * lefε n lam H = -(lefε n lam H * lefΓ n lam) := by
  have hk : gamM (-1 : Matrix (Md n) (Md n) ℂ) * creL n (cf n H) = -(creL n (cf n H) * gamM (-1 : Matrix (Md n) (Md n) ℂ)) := by
    rw [(hC n (-1) (cf n H) 0).1, Matrix.neg_mulVec, Matrix.one_mulVec, map_neg, neg_mul]
  rw [lefΓ_apply, lefε_apply, cj_mul hu, cj_mul hu, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hk,
    neg_kron', map_neg]

include hC in
/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem Γι_f (H : Mat n) : lefΓ n lam * lefι n lam H = -(lefι n lam H * lefΓ n lam) := by
  have hk : gamM (-1 : Matrix (Md n) (Md n) ℂ) * annL n (cf n H) = -(annL n (cf n H) * gamM (-1 : Matrix (Md n) (Md n) ℂ)) := by
    rw [(hC n (-1) 0 (cf n H)).2, Matrix.transpose_neg, Matrix.transpose_one, Matrix.neg_mulVec, Matrix.one_mulVec,
      map_neg, mul_neg, neg_neg]
  rw [lefΓ_apply, lefι_apply, cj_mul hu, cj_mul hu, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hk,
    neg_kron', map_neg]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ΓFr_f (x : Mat n) : lefΓ n lam * lefFr n lam x = lefFr n lam x * lefΓ n lam := by
  rw [lefΓ_apply, lefFr_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    gam_mul' hu hG, gam_mul' hu hG, neg_one_mul, mul_neg_one, one_mul, mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ΓT_f : lefΓ n lam * lefT n lam = lefT n lam * lefΓ n lam := by
  rw [lefΓ_apply, lefT_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one,
    one_mul, mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem sym_one_eq_one : lefS n lam 1 = 1 := by
  rw [lefS_apply, Complex.ofReal_one, one_smul, (hG n).1, one_kronecker_one, cj_one hu]

include hC in
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem Sε_f (s : ℝ) (H : Mat n) : lefS n lam s * lefε n lam H = (s : ℂ) • (lefε n lam H * lefS n lam s) := by
  rw [lefS_apply, lefε_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, (hC n _ _ 0).1,
    smul_one_mulVec', map_smul, smul_mul_assoc, smul_kronecker, map_smul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem SΓ_f (s : ℝ) : lefΓ n lam * lefS n lam s = lefS n lam s * lefΓ n lam := by
  rw [lefS_apply, lefΓ_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, gam_mul' hu hG,
    gam_mul' hu hG, mul_neg_one, neg_one_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem S0sq_f : lefS n lam 0 * lefS n lam 0 = lefS n lam 0 := by
  rw [lefS_zero, cj_mul hu, ← mul_kronecker_mul, gam_mul' hu hG, mul_zero, mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem S0Γ_f : lefΓ n lam * lefS n lam 0 = lefS n lam 0 := by
  rw [lefS_zero, lefΓ_apply, cj_mul hu, ← mul_kronecker_mul, gam_mul' hu hG, mul_zero, mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem sym_zero_comm_frame_matrix (x : Mat n) : lefS n lam 0 * lefFr n lam x = lefFr n lam x * lefS n lam 0 := by
  rw [lefS_zero, lefFr_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    gam_mul' hu hG, gam_mul' hu hG, zero_mul, mul_zero, one_mul, mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem time_comm_sym_zero_matrix : lefT n lam * lefS n lam 0 = lefS n lam 0 * lefT n lam := by
  rw [lefS_zero, lefT_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one,
    one_mul, mul_one]

end

section

variable (hu : IsUnit (sqQ lam)) (hS : SwapLaws)
include hu hS

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem Tsq_f : lefT n lam * lefT n lam = 1 := by
  rw [lefT_apply, cj_mul hu, ← mul_kronecker_mul, mul_one, (hS n lam).1, one_kronecker_one, cj_one hu]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem Tε_f (H : Mat n) : lefT n lam * lefε n lam H = lefε n lam H * lefT n lam := by
  rw [lefT_apply, lefε_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one,
    one_mul, mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem Tι_f (H : Mat n) : lefT n lam * lefι n lam H = lefι n lam H * lefT n lam := by
  rw [lefT_apply, lefι_apply, cj_mul hu, cj_mul hu, ← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one,
    one_mul, mul_one]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem unit_inv_conj (k : Matrix.unitaryGroup (Fin n) ℂ) : (k.1ᴴ)⁻¹ = k.1 := by
  apply Matrix.inv_eq_right_inv
  have h := Unitary.star_mul_self_of_mem k.2
  rwa [Matrix.star_eq_conjTranspose] at h

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem isUnit_det_unitary (k : Matrix.unitaryGroup (Fin n) ℂ) : IsUnit (k.1).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := (k.1)ᴴ)
  have h := Unitary.mul_star_self_of_mem k.2
  rwa [Matrix.star_eq_conjTranspose] at h

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem swap_rhoW_k (k : Matrix.unitaryGroup (Fin n) ℂ) : swapJ lam * rhoW lam k.1 = rhoW lam k.1 * swapJ lam := by
  have := (hS n lam).2.2.1 k.1 (isUnit_det_unitary hu hS k)
  rwa [unit_inv_conj hu hS k] at this

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem TK_f (k : Matrix.unitaryGroup (Fin n) ℂ) : lefT n lam * lefFr n lam k.1 = lefFr n lam k.1 * lefT n lam := by
  rw [lefT_apply, lefFr_apply, frame_zero_apply, cj_mul hu, cj_mul hu, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    swap_rhoW_k hu hS k, one_mul, mul_one]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem S0θ_f (hG : GamMul) (x : Mat n) (hx : x ∈ GLs n) :
    lefT n lam * lefFr n lam (xᴴ⁻¹) * lefS n lam 0 = lefFr n lam x * lefT n lam * lefS n lam 0 := by
  have hd : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  rw [lefT_apply, lefFr_apply, lefFr_apply, frame_zero_apply, frame_zero_apply, lefS_zero, cj_mul hu, cj_mul hu, cj_mul hu, cj_mul hu]
  simp only [← Matrix.mul_kronecker_mul, ← (hG n).2, mul_zero, one_mul, mul_one]
  rw [(hS n lam).2.2.1 x hd]

end

end PositivityTheory.RgBcC
