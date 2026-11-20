import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovariantHatPairReindex.SumSgnLProdCol
import Formalism.PeriodIntegrals.ContractionsCovariantIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.FormalDegreeBessel.FinalIO

open Matrix Finset

namespace PI.QnCovHat2W

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

/- English proof (translation)
Rewrite using `[quantumMinorRowSkew_holds A n m E x y π u, Int.cast_smul_eq_zsmul, zsmul_eq_mul]`.
-/
theorem qminor_row_alt {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (u : ℂ)
    (x y : Fin m → Fin n) (π : Equiv.Perm (Fin m)) :
    qminor E (x ∘ π) y u = ((Equiv.Perm.sign π : ℤ) : ℂ) • qminor E x y u := by
  rw [quantumMinorRowSkew_holds A n m E x y π u, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

/- English proof (translation)
Rewrite using `[quantumMinorColSkew_holds A n m E hE x y π u, Int.cast_smul_eq_zsmul, zsmul_eq_mul]`.
-/
theorem qminor_col_alt {A : Type} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (u : ℂ) (x y : Fin m → Fin n) (π : Equiv.Perm (Fin m)) :
    qminor E x (y ∘ π) u = ((Equiv.Perm.sign π : ℤ) : ℂ) • qminor E x y u := by
  rw [quantumMinorColSkew_holds A n m E hE x y π u, Int.cast_smul_eq_zsmul, zsmul_eq_mul]

/- English proof (translation)
Introduce `A _ _ n E P Q hE hQP hPQ u a a' β β'`. Break down `n with _ | _ | m` into its components or cases. Simplify using `[chat2A]`. Simplify using `[chat2A]`. Establish `hE' : GlRel (Econj E P Q)` using `glRelAd A (m + 2) E P Q hE hQP`.

Establish `h1` using `GG_eq (fun x y : Fin m → Fin (m + 2) => qminor E x y u) (fun x y π => qminor_row_alt E u x y π) (fun x y π => qminor_col_alt E hE u x y π) β β' a a'`. Establish `h2` using `GG_eq (fun x y : Fin m → Fin (m + 2) => qminor (Econj E P Q) x y u) (fun x y π => qminor_row_alt (Econj E P Q) u x y π) (fun x y π => qminor_col_alt (Econj E P Q) hE' u x y π) (β ᵥ* P) (β' ᵥ* P) (Q *ᵥ a) (Q *ᵥ a')`. Establish `h3` using `GG_cov (fun x y : Fin m → Fin (m + 2) => qminor E x y u) (fun x y : Fin m → Fin (m + 2) => qminor (Econj E P Q) x y u) P Q (fun x y => hLin A (m + 2) m E P Q hQP x y u) β β' a a'`. Establish `hdet : P.det * Q.det = 1` using `by rw [← Matrix.det_mul, hPQ, Matrix.det_one]`. Rewrite `h3` using `[hdet, one_smul, h1, h2]`.

Establish `hne : ((m.factorial : ℂ) * m.factorial) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)) (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))`. Establish `h4` using `congrArg (fun z => ((m.factorial : ℂ) * m.factorial)⁻¹ • z) h3`. Simplify using `only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4`. Conclude with `h4`.
-/
theorem qnCovHat2_of_lin (hLin : PI.QnCovLin) : PI.QnCovHat2 := by
  intro A _ _ n E P Q hE hQP hPQ u a a' β β'
  rcases n with _ | _ | m
  · simp [chat2A]
  · simp [chat2A]
  · have hE' : GlRel (Econj E P Q) := glRelAd A (m + 2) E P Q hE hQP
    have h1 := GG_eq (fun x y : Fin m → Fin (m + 2) => qminor E x y u)
      (fun x y π => qminor_row_alt E u x y π) (fun x y π => qminor_col_alt E hE u x y π) β β' a a'
    have h2 := GG_eq (fun x y : Fin m → Fin (m + 2) => qminor (Econj E P Q) x y u)
      (fun x y π => qminor_row_alt (Econj E P Q) u x y π)
      (fun x y π => qminor_col_alt (Econj E P Q) hE' u x y π) (β ᵥ* P) (β' ᵥ* P) (Q *ᵥ a) (Q *ᵥ a')
    have h3 := GG_cov (fun x y : Fin m → Fin (m + 2) => qminor E x y u)
      (fun x y : Fin m → Fin (m + 2) => qminor (Econj E P Q) x y u) P Q
      (fun x y => hLin A (m + 2) m E P Q hQP x y u) β β' a a'
    have hdet : P.det * Q.det = 1 := by rw [← Matrix.det_mul, hPQ, Matrix.det_one]
    rw [hdet, one_smul, h1, h2] at h3
    have hne : ((m.factorial : ℂ) * m.factorial) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
        (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m))
    have h4 := congrArg (fun z => ((m.factorial : ℂ) * m.factorial)⁻¹ • z) h3
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
    exact h4

end PI.QnCovHat2W
