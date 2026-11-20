import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice

noncomputable section

namespace PIW.AdelicOrbitU

open Matrix Formalism.UG

section Refl

variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem hform_eq_dot (x y : Fin n → S) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hform_sub_left (x y z : Fin n → S) :
    hform s J (x - y) z = hform s J x z - hform s J y z := by
  simp only [hform_eq_dot, dotProduct, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hform_sub_right (x y z : Fin n → S) :
    hform s J x (y - z) = hform s J x y - hform s J x z := by
  simp only [hform_eq_dot, dotProduct, Matrix.mulVec_sub, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hform_smul_left (a : S) (x y : Fin n → S) :
    hform s J (a • x) y = s a * hform s J x y := by
  simp only [hform_eq_dot, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hform_smul_right (a : S) (x y : Fin n → S) :
    hform s J x (a • y) = a * hform s J x y := by
  simp only [hform_eq_dot, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify to obtain the desired conclusion from the available facts. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_conj (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (x y : Fin n → S) :
    s (hform s J x y) = hform s J y x := by
  have hJ' : ∀ i j, s (J i j) = J j i := fun i j => by
    have h1 := congrFun (congrFun hJ j) i
    unfold cT at h1
    simpa [Matrix.transpose_apply, Matrix.map_apply] using h1
  unfold hform
  simp only [map_sum, map_mul, hs, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem hform_single (i j : Fin n) :
    hform s J (Pi.single i 1) (Pi.single j 1) = J i j := by
  have hs : ∀ k, s ((Pi.single i (1 : S) : Fin n → S) k) = (Pi.single i (1 : S) : Fin n → S) k := fun k => by
    by_cases h : k = i
    · subst h
      simp
    · simp [h]
  unfold hform
  simp only [hs]
  simp [Pi.single_apply]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem hform_entry (T : Matrix (Fin n) (Fin n) S) (i j : Fin n) :
    (cT s T * J * T) i j = hform s J (T *ᵥ Pi.single i 1) (T *ᵥ Pi.single j 1) := by
  have hv : ∀ m, T *ᵥ Pi.single m (1 : S) = fun k => T k m := fun m => by
    ext k
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold cT hform
  simp only [hv, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

end Refl

end PIW.AdelicOrbitU
