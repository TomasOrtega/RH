import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariants
open GlobalTheory.JR Matrix

namespace GlobalTheory.JR.CompanionCharpoly

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, companion, Matrix.of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem companion_map {k k' : Type} [CommRing k] [CommRing k'] (f : k →+* k') {r : ℕ} (p : Fin r → k) :
    (companion p).map f = companion (fun i => f (p i)) := by
  ext i j
  simp only [Matrix.map_apply, companion, Matrix.of_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `set R := MvPolynomial (Fin r) ℤ`. Use `set K := FractionRing R`. Establish `hinj : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Apply `hinj` to reduce the goal to its premises. Establish `h` using `GlobalTheory.JR.NormalFormL.charpoly_companion_coeff (fun j : Fin r => algebraMap R K (MvPolynomial.X j)) i`.

Rewrite `h` using `[← companion_map, Matrix.charpoly_map, Polynomial.coeff_map]`. Conclude with `h`.
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
Introduce `k _ r p i`. Set `f : MvPolynomial (Fin r) ℤ →+* k` to `MvPolynomial.eval₂Hom (Int.castRingHom k) p`. Establish `hp : companion p = (companion (fun j : Fin r => (MvPolynomial.X j : MvPolynomial (Fin r) ℤ))).map f`. Rewrite using `[companion_map]`. Use `congr 1`.

Use function extensionality and compare the values at `j`. Simplify using `[f]`. Rewrite using `[hp, Matrix.charpoly_map, Polynomial.coeff_map, coeff_universal]`. Simplify using `[f]`.
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
