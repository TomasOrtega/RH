import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigOf

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {lam : Fin n → ℤ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem trace_clm (A : Matrix (Ix n lam) (Ix n lam) ℂ) :
    LinearMap.trace ℂ (EV n lam) ((clm lam A : EV n lam →L[ℂ] EV n lam) : EV n lam →ₗ[ℂ] EV n lam) = A.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Ix n lam) ℂ).toBasis]
  congr 1
  ext i j
  simp [LinearMap.toMatrix_apply, clm, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem trace_cj (hu : IsUnit (sqQ lam)) (A : Matrix (Ix n lam) (Ix n lam) ℂ) :
    LinearMap.trace ℂ (EV n lam) ((cjL lam A : EV n lam →L[ℂ] EV n lam) : EV n lam →ₗ[ℂ] EV n lam) = A.trace := by
  rw [cjL_apply, ContinuousLinearMap.coe_mul, ContinuousLinearMap.coe_mul, LinearMap.trace_mul_comm, ← mul_assoc,
    ← ContinuousLinearMap.coe_mul, ← ContinuousLinearMap.coe_mul, Ring.inverse_mul_cancel _ hu, one_mul, trace_clm]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem weylChar_conj (u : Fin n → ℂ) : weylChar lam (fun a => conj (u a)) = conj (weylChar lam u) := by
  unfold weylChar
  rw [map_div₀, RingHom.map_det, RingHom.map_det]
  congr 2 <;> ext i j <;> simp [map_zpow₀, map_pow]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem trace_gamma_zero_eq_one (hScal : GamScal) : (gamM (0 : Matrix (Md n) (Md n) ℂ)).trace = 1 := by
  have e : (0 : Matrix (Md n) (Md n) ℂ) = (0 : ℂ) • 1 := by rw [zero_smul]
  rw [e, hScal n 0, trace_diagonal, Finset.sum_eq_single (∅ : Finset (Md n))]
  · simp
  · intro A _ hA
    exact zero_pow (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hA))
  · simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem diag_unit_prod (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) :
    (diagonal z)ᴴ * (diagonal z)⁻¹ = diagonal (fun a => conj (z a ^ 2)) ∧ IsUnit (diagonal z).det ∧
      IsUnit ((diagonal z)ᴴ).det ∧ IsUnit ((diagonal z)⁻¹).det := by
  have hc : ∀ a, z a * conj (z a) = 1 := fun a => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]; simp
  have hinv : (diagonal z)⁻¹ = diagonal fun a => conj (z a) :=
    Matrix.inv_eq_right_inv (by rw [diagonal_mul_diagonal]; simp [hc])
  have hne : ∀ a, z a ≠ 0 := fun a h => by simpa [h] using hz a
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hinv, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1; ext a; simp [pow_two, map_mul]
  · rw [det_diagonal]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hne a)
  · rw [diagonal_conjTranspose, det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => by simpa using hne a)
  · rw [hinv, det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => by simpa using hne a)

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem char_f (hu : IsUnit (sqQ lam)) (hG : GamMul) (hScal : GamScal) (hS : SwapLaws) (hRL : RmLaws) (hRC : RmChar)
    (hlam : Antitone lam) (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) (hinj : Function.Injective fun a => z a ^ 2) :
    LinearMap.trace ℂ (EV n lam) ((lefS n lam 0 * lefFr n lam (diagonal z) * lefT n lam : EV n lam →L[ℂ] EV n lam) :
      EV n lam →ₗ[ℂ] EV n lam) = conj (weylChar lam fun a => z a ^ 2) := by
  obtain ⟨hprod, hd, hdH, hdi⟩ := diag_unit_prod z hz
  rw [lefS_zero, lefFr_apply, lefT_apply, cj_mul hu, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, ← mul_kronecker_mul,
    gam_mul' hu hG, zero_mul, mul_one, one_mul, trace_cj hu, trace_kronecker, trace_gamma_zero_eq_one hScal, one_mul,
    rhoW, (hS n lam).2.2.2.2, ← transpose_mul, trace_transpose]
  have hR := hRL n lam
  have hinvR : (Rm lam (diagonal z))⁻¹ = Rm lam (diagonal z)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [← hR.2.1 _ _ hd hdi, Matrix.mul_nonsing_inv _ hd, hR.1]
  rw [hinvR, ← hR.2.1 _ _ hdH hdi, hprod]
  have ht : ∀ a, (fun a => conj (z a ^ 2)) a ≠ 0 := fun a h => by
    have : z a ≠ 0 := fun h0 => by simpa [h0] using hz a
    simp only [map_eq_zero] at h
    exact this (pow_eq_zero_iff two_ne_zero |>.mp h)
  have hti : Function.Injective fun a => conj (z a ^ 2) := fun a b h => hinj (by
    have h' : conj (z a ^ 2) = conj (z b ^ 2) := h
    exact (RingHom.injective (starRingEnd ℂ)) h')
  rw [hRC n lam hlam _ ht hti, ← weylChar_conj]

end PositivityTheory.RgBcC
