import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.JacRev

open MvPolynomial Matrix

noncomputable section

namespace PI.OddDualWeyl

namespace Intw

section General

variable {A : Type*} [CommRing A] {n : ℕ}

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem transvection_mul_apply (b a : Fin n) (c : A) (N : Matrix (Fin n) (Fin n) A) (i s : Fin n) :
    (transvection b a c * N) i s = N i s + if i = b then c * N a s else 0 := by
  by_cases h : i = b
  · subst h
    simp [transvection_mul_apply_same]
  · simp [transvection_mul_apply_of_ne, h]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem mul_transvection_apply (b a : Fin n) (c : A) (N : Matrix (Fin n) (Fin n) A) (p i : Fin n) :
    (N * transvection b a c) p i = N p i + if i = a then N p b * c else 0 := by
  by_cases h : i = a
  · subst h
    rw [mul_transvection_apply_same, if_pos rfl]
    ring
  · simp [mul_transvection_apply_of_ne, h]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem adjugate_transvection {i j : Fin n} (h : i ≠ j) (c : A) :
    adjugate (transvection i j c) = transvection i j (-c) := by
  have h1 : transvection i j c * transvection i j (-c) = 1 := by
    rw [transvection_mul_transvection_same i j h, add_neg_cancel, transvection_zero]
  calc adjugate (transvection i j c)
      = adjugate (transvection i j c) * (transvection i j c * transvection i j (-c)) := by
        rw [h1, Matrix.mul_one]
    _ = (adjugate (transvection i j c) * transvection i j c) * transvection i j (-c) := by
        rw [Matrix.mul_assoc]
    _ = transvection i j (-c) := by
        rw [adjugate_mul, det_transvection_of_ne i j h, one_smul, Matrix.one_mul]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem coeff_comp_neg_X (p : Polynomial A) (m : ℕ) :
    (p.comp (-Polynomial.X)).coeff m = (-1) ^ m * p.coeff m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
  | monomial e a =>
    have hX : (-Polynomial.X : Polynomial A) ^ e = Polynomial.C ((-1) ^ e) * Polynomial.X ^ e := by
      rw [neg_pow]
      simp
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_pow_comp, hX, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C_mul_X_pow]
    split_ifs with hm
    · subst hm
      ring
    · simp

end General

variable {R : Type} [CommRing R] {k : ℕ}

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem rowGen_genM (a b : Fin k) :
    (rowGen R a b).toRingHom.mapMatrix (genM R k) =
      transvection b a (Polynomial.X) *
        (Polynomial.C : MvPolynomial (Fin k × Fin k) R →+* _).mapMatrix (genM R k) := by
  ext i s
  rw [transvection_mul_apply]
  simp [PI.OddDualWeyl.genM, PI.OddDualWeyl.rowGen]

/- English proof (translation)
Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.
-/
theorem rowGen_det (a b : Fin k) (hab : a ≠ b) :
    rowGen R a b (genM R k).det = Polynomial.C (genM R k).det := by
  calc PI.OddDualWeyl.rowGen R a b (PI.OddDualWeyl.genM R k).det
      = ((PI.OddDualWeyl.rowGen R a b).toRingHom.mapMatrix (PI.OddDualWeyl.genM R k)).det :=
        RingHom.map_det (PI.OddDualWeyl.rowGen R a b).toRingHom (PI.OddDualWeyl.genM R k)
    _ = Polynomial.C (PI.OddDualWeyl.genM R k).det := by
        rw [rowGen_genM, det_mul, det_transvection_of_ne b a hab.symm, one_mul,
          ← RingHom.map_det]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation.
-/
theorem rowGen_dualM (a b : Fin k) (hab : a ≠ b) (i j : Fin k) :
    rowGen R a b (dualM R k i j) = Polynomial.C (dualM R k i j) -
      (if i = a then Polynomial.X * Polynomial.C (dualM R k b j) else 0) := by
  have hadj : (rowGen R a b).toRingHom.mapMatrix (adjugate (genM R k)) =
      (Polynomial.C : MvPolynomial (Fin k × Fin k) R →+* _).mapMatrix (adjugate (genM R k)) *
        transvection b a (-Polynomial.X) := by
    rw [RingHom.map_adjugate, rowGen_genM, adjugate_mul_distrib,
      adjugate_transvection (Ne.symm hab), ← RingHom.map_adjugate]
  have h2 := congrFun (congrFun hadj (Fin.rev j)) i
  rw [mul_transvection_apply] at h2
  simp only [RingHom.mapMatrix_apply, map_apply] at h2
  have e1 : dualM R k i j = adjugate (genM R k) (Fin.rev j) i := rfl
  have e2 : dualM R k b j = adjugate (genM R k) (Fin.rev j) b := rfl
  rw [e1, e2]
  change (rowGen R a b).toRingHom _ = _
  rw [h2]
  split_ifs <;> ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem key (a b : Fin k) (hab : a ≠ b) (f' : MvPolynomial (Fin k × Fin k) R) :
    rowGen R a b (dualSub R k f') =
      (Polynomial.map (dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _)
        (rowGen R b a f')).comp (-Polynomial.X) := by
  refine MvPolynomial.induction_on (motive := fun g => PI.OddDualWeyl.rowGen R a b (PI.OddDualWeyl.dualSub R k g) =
      (Polynomial.map (PI.OddDualWeyl.dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _)
        (PI.OddDualWeyl.rowGen R b a g)).comp (-Polynomial.X)) f' ?_ ?_ ?_
  · intro r
    simp [PI.OddDualWeyl.dualSub, PI.OddDualWeyl.rowGen]
  · intro p q hp hq
    rw [map_add, map_add, hp, hq, map_add, Polynomial.map_add, Polynomial.add_comp]
  · intro p v hp
    have hv : PI.OddDualWeyl.rowGen R a b (PI.OddDualWeyl.dualSub R k (X v)) =
        (Polynomial.map (PI.OddDualWeyl.dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _)
          (PI.OddDualWeyl.rowGen R b a (X v))).comp (-Polynomial.X) := by
      obtain ⟨i, j⟩ := v
      have e1 : (PI.OddDualWeyl.dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _) (X (i, j)) =
          PI.OddDualWeyl.dualM R k i j := by
        show PI.OddDualWeyl.dualSub R k (X (i, j)) = _
        simp only [PI.OddDualWeyl.dualSub, aeval_X]
      have e2 : (PI.OddDualWeyl.dualSub R k : MvPolynomial (Fin k × Fin k) R →+* _) (X (b, j)) =
          PI.OddDualWeyl.dualM R k b j := by
        show PI.OddDualWeyl.dualSub R k (X (b, j)) = _
        simp only [PI.OddDualWeyl.dualSub, aeval_X]
      have e3 : PI.OddDualWeyl.rowGen R b a (X (i, j) : MvPolynomial (Fin k × Fin k) R) =
          Polynomial.C (X (i, j)) + (if i = a then Polynomial.X * Polynomial.C (X (b, j)) else 0) := by
        simp only [PI.OddDualWeyl.rowGen, aeval_X]
      have e4 : PI.OddDualWeyl.dualSub R k (X (i, j) : MvPolynomial (Fin k × Fin k) R) =
          PI.OddDualWeyl.dualM R k i j := e1
      rw [e4, rowGen_dualM a b hab, e3]
      split_ifs with h
      · rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, Polynomial.map_X,
          Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.C_comp,
          Polynomial.X_comp, e1, e2]
        ring
      · rw [sub_zero, add_zero, Polynomial.map_C, Polynomial.C_comp, e1]
    rw [map_mul, map_mul, hp, hv, map_mul, Polynomial.map_mul, Polynomial.mul_comp]

end Intw

open Intw in
/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem rowOpIntertwining : W1 := by
  unfold W1
  intro R _ k M a b j f f' hab hrel
  unfold Rel at hrel ⊢
  unfold rowDiv
  have h := congrArg (fun p => Polynomial.coeff p j) (PI.OddDualWeyl.Intw.key a b hab f')
  rw [coeff_comp_neg_X, Polynomial.coeff_map, hrel, map_mul, map_pow,
    PI.OddDualWeyl.Intw.rowGen_det a b hab, ← Polynomial.C_pow, Polynomial.coeff_C_mul] at h
  rw [map_mul, map_pow, map_neg, map_one]
  exact h.symm

end PI.OddDualWeyl
