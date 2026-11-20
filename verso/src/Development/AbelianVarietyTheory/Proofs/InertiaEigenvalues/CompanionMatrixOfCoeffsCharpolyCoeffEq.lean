import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariants
open GlobalTheory.JR Matrix

namespace GlobalTheory.JR.CompanionCharpoly

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem companion_map {k k' : Type} [CommRing k] [CommRing k'] (f : k →+* k') {r : ℕ} (p : Fin r → k) :
    (companion p).map f = companion (fun i => f (p i)) := by
  ext i j
  simp only [Matrix.map_apply, companion, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem coeff_universal (r : ℕ) (i : Fin r) :
    (companion (fun j : Fin r => (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))).charpoly.coeff (i : ℕ) =
      MvPolynomial.X i := by
  set R := MvPolynomial (Fin r) ℤ
  set K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  apply hinj
  have h := GlobalTheory.JR.NormalFormL.charpoly_companion_coeff
    (fun j : Fin r => algebraMap R K (MvPolynomial.X j)) i
  rw [← companion_map, Matrix.charpoly_map, Polynomial.coeff_map] at h
  exact h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem charpoly_companion_coeff_ring :
    ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by
  intro k _ r p i
  let f : MvPolynomial (Fin r) ℤ →+* k := MvPolynomial.eval₂Hom (Int.castRingHom k) p
  have hp : companion p = (companion (fun j : Fin r => (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))).map f := by
    rw [companion_map]
    congr 1
    funext j
    simp [f]
  rw [hp, Matrix.charpoly_map, Polynomial.coeff_map, coeff_universal]
  simp [f]

end GlobalTheory.JR.CompanionCharpoly
