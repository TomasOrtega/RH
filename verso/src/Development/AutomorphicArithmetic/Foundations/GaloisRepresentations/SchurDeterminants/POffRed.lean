import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

open Finset MvPolynomial UpperTheory.Gal.Schur

namespace UpperTheory.Gal.Schur

end UpperTheory.Gal.Schur

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Schur.offClrRed_of :
    OffClrPow → OffClrRed := by
  intro h R _ _ n lam g y
  have key := h (Polynomial R) n lam (fun k => Polynomial.C (g k)) Polynomial.X
  have key' := (Polynomial.isRegular_X_pow ((n - 1).choose 2)).left key
  let φ : Polynomial R →ₐ[ℚ] R := (Polynomial.evalRingHom y).toRatAlgHom
  have hφ : ∀ (f : Fin n → Polynomial R) (p : MvPolynomial (Fin n) ℚ),
      φ (MvPolynomial.aeval f p) = MvPolynomial.aeval (fun k => φ (f k)) p := by
    intro f p
    rw [← MvPolynomial.comp_aeval]
    rfl
  have hC : ∀ r : R, φ (Polynomial.C r) = r := fun r => by simp [φ]
  have hX : φ Polynomial.X = y := by simp [φ]
  have hs : ∀ i, (fun k => φ (scaleOff Polynomial.X i (fun k => Polynomial.C (g k)) k)) = scaleOff y i g := by
    intro i
    funext k
    simp only [scaleOff]
    split_ifs
    · simp [hC]
    · rw [map_mul, hC, hX]
  have := congrArg φ key'
  simp only [map_sum, map_mul, map_prod, map_pow, map_sub, map_neg, map_one, sch, hφ, vdmAway, vdm,
    hs, hC, hX] at this
  simpa [sch, vdmAway, vdm] using this
