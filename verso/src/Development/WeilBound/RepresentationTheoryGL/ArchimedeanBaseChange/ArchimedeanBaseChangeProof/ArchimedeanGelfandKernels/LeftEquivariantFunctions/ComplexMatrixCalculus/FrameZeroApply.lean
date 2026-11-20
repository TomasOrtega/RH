import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.EigLocal

noncomputable section

open Matrix
open scoped Kronecker ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ} {lam : Fin n → ℤ}

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem cjL_apply (A : Matrix (Ix n lam) (Ix n lam) ℂ) : cjL lam A = sqQ lam * clm lam A * Ring.inverse (sqQ lam) := by
  simp [cjL, mul_assoc]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem clm_mul' (A B : Matrix (Ix n lam) (Ix n lam) ℂ) : clm lam (A * B) = clm lam A * clm lam B := map_mul _ A B

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem clm_one' : clm lam (1 : Matrix (Ix n lam) (Ix n lam) ℂ) = 1 := map_one _

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cj_mul (hu : IsUnit (sqQ lam)) (A B : Matrix (Ix n lam) (Ix n lam) ℂ) :
    cjL lam A * cjL lam B = cjL lam (A * B) := by
  rw [cjL_apply, cjL_apply, cjL_apply, clm_mul']
  have h : Ring.inverse (sqQ lam) * sqQ lam = 1 := Ring.inverse_mul_cancel _ hu
  calc sqQ lam * clm lam A * Ring.inverse (sqQ lam) * (sqQ lam * clm lam B * Ring.inverse (sqQ lam))
      = sqQ lam * clm lam A * (Ring.inverse (sqQ lam) * sqQ lam) * clm lam B * Ring.inverse (sqQ lam) := by
        simp only [mul_assoc]
    _ = sqQ lam * (clm lam A * clm lam B) * Ring.inverse (sqQ lam) := by rw [h, mul_one]; simp only [mul_assoc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cj_one (hu : IsUnit (sqQ lam)) : cjL lam 1 = 1 := by
  rw [cjL_apply, clm_one', mul_one]
  exact Ring.mul_inverse_cancel _ hu

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lefε_apply (H : Mat n) : lefε n lam H = cjL lam (creL n (cf n H) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lefι_apply (H : Mat n) : lefι n lam H = cjL lam (annL n (cf n H) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lefFr_apply (x : Mat n) : lefFr n lam x = cjL lam (fr0 lam x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frame_zero_apply (x : Mat n) : fr0 lam x = gamM (Mt x⁻¹)ᵀ ⊗ₖ rhoW lam x := rfl

end PositivityTheory.RgBcC
