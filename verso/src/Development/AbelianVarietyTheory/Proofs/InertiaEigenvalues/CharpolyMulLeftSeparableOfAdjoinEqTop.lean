import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `E A _ _ _ _ _ y htop hred`. Establish `hint : IsIntegral E y` using `Algebra.IsIntegral.isIntegral y`. Set `pb` to `PowerBasis.ofAdjoinEqTop hint htop`. Establish `hfin : Module.finrank E A = (minpoly E y).natDegree` using `pb.finrank`. Establish `hmin : minpoly E (LinearMap.mulLeft E y) = minpoly E y`.

Establish `h` using `minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective (R := E) (A := A)) y`. Rewrite using `[← h]`. Both sides reduce to the same expression. Establish `hdvd : minpoly E y ∣ (LinearMap.mulLeft E y).charpoly` using `hmin ▸ LinearMap.minpoly_dvd_charpoly _`. Establish `heq : (LinearMap.mulLeft E y).charpoly = minpoly E y` using `eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (LinearMap.charpoly_monic _) hdvd (by rw [LinearMap.charpoly_natDegree, hfin])`.

Rewrite using `[heq]`. Establish `hsq : Squarefree (minpoly E y)` using `(minpoly.isRadical E y).squarefree (minpoly.ne_zero hint)`. Conclude with `PerfectField.separable_iff_squarefree.mpr hsq`.
-/
theorem charpoly_mulLeft_separable_of_adjoin_eq_top : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A]
    [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A →
    (LinearMap.mulLeft E y).charpoly.Separable := by
  intro E A _ _ _ _ _ y htop hred
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  let pb := PowerBasis.ofAdjoinEqTop hint htop
  have hfin : Module.finrank E A = (minpoly E y).natDegree := pb.finrank
  have hmin : minpoly E (LinearMap.mulLeft E y) = minpoly E y := by
    have h := minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective (R := E) (A := A)) y
    rw [← h]
    rfl
  have hdvd : minpoly E y ∣ (LinearMap.mulLeft E y).charpoly :=
    hmin ▸ LinearMap.minpoly_dvd_charpoly _
  have heq : (LinearMap.mulLeft E y).charpoly = minpoly E y :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (LinearMap.charpoly_monic _) hdvd
      (by rw [LinearMap.charpoly_natDegree, hfin])
  rw [heq]
  have hsq : Squarefree (minpoly E y) := (minpoly.isRadical E y).squarefree (minpoly.ne_zero hint)
  exact PerfectField.separable_iff_squarefree.mpr hsq

end GlobalTheory
