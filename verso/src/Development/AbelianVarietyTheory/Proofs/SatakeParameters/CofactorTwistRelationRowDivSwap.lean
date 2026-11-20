import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

noncomputable section

namespace GlobalTheory.ValCmp

/- English proof (translation)
Establish `h1 : Matrix.transvection a b c * Matrix.transvection a b (-c) = 1`. Rewrite using `[Matrix.transvection_mul_transvection_same a b hab, add_neg_cancel, Matrix.transvection_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, Matrix.mul_one]`. Use `_ = Matrix.transvection a b (-c) := by`.

Rewrite using `[← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.det_transvection_of_ne a b hab, one_smul, Matrix.one_mul]`.
-/
theorem adjugate_transvection_of_ne {A : Type} [CommRing A] {n : ℕ} (a b : Fin n) (hab : a ≠ b) (c : A) :
    (Matrix.transvection a b c).adjugate = Matrix.transvection a b (-c) := by
  have h1 : Matrix.transvection a b c * Matrix.transvection a b (-c) = 1 := by
    rw [Matrix.transvection_mul_transvection_same a b hab, add_neg_cancel, Matrix.transvection_zero]
  calc (Matrix.transvection a b c).adjugate
      = (Matrix.transvection a b c).adjugate * (Matrix.transvection a b c * Matrix.transvection a b (-c)) := by
        rw [h1, Matrix.mul_one]
    _ = Matrix.transvection a b (-c) := by
        rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.det_transvection_of_ne a b hab, one_smul,
          Matrix.one_mul]

/- English proof (translation)
Use `ext1 i s`. Distinguish the cases in `hi : i = a`. Substitute `hi` using the available equality. Rewrite using `[Matrix.transvection_mul_apply_same]`. Simplify using `[genM, rowGen]`.

Rewrite using `[Matrix.transvection_mul_apply_of_ne _ _ _ _ hi]`. Simplify using `[genM, rowGen, hi]`.
-/
theorem rowGen_map_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) :
    (rowGen R (n := n) b a).toRingHom.mapMatrix (genM R n) =
      Matrix.transvection a b Polynomial.X * (Polynomial.C (R := MP R n)).mapMatrix (genM R n) := by
  ext1 i s
  by_cases hi : i = a
  · subst hi
    rw [Matrix.transvection_mul_apply_same]
    simp [genM, rowGen]
  · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hi]
    simp [genM, rowGen, hi]

/- English proof (translation)
Establish `h` using `RingHom.map_det (rowGen R (n := n) b a).toRingHom (genM R n)`. Rewrite `h` using `[rowGen_map_genM, Matrix.det_mul, Matrix.det_transvection_of_ne a b hab, one_mul, ← RingHom.map_det]`. Conclude with `h`.
-/
theorem rowGen_det_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    rowGen R (n := n) b a (genM R n).det = Polynomial.C (genM R n).det := by
  have h := RingHom.map_det (rowGen R (n := n) b a).toRingHom (genM R n)
  rw [rowGen_map_genM, Matrix.det_mul, Matrix.det_transvection_of_ne a b hab, one_mul,
    ← RingHom.map_det] at h
  exact h

/- English proof (translation)
Establish `h` using `RingHom.map_adjugate (rowGen R (n := n) b a).toRingHom (genM R n)`. Rewrite `h` using `[rowGen_map_genM, Matrix.adjugate_mul_distrib, adjugate_transvection_of_ne a b hab, ← RingHom.map_adjugate]`. Establish `h2` using `congrFun (congrFun h t) i`. Use `Eq.trans h2 ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = b`.

Substitute `hi` using the available equality. Rewrite using `[Matrix.mul_transvection_apply_same]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_transvection_apply_of_ne _ _ _ _ hi]`. Simplify using `[hi]`.
-/
theorem rowGen_adjugate_genM (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (t i : Fin n) :
    rowGen R (n := n) b a ((genM R n).adjugate t i) =
      Polynomial.C ((genM R n).adjugate t i) +
        (if i = b then -Polynomial.X * Polynomial.C ((genM R n).adjugate t a) else 0) := by
  have h := RingHom.map_adjugate (rowGen R (n := n) b a).toRingHom (genM R n)
  rw [rowGen_map_genM, Matrix.adjugate_mul_distrib, adjugate_transvection_of_ne a b hab,
    ← RingHom.map_adjugate] at h
  have h2 := congrFun (congrFun h t) i
  refine Eq.trans h2 ?_
  by_cases hi : i = b
  · subst hi
    rw [Matrix.mul_transvection_apply_same]
    simp
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hi]
    simp [hi]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C x`. Establish `e1 : (C x : MP R n) = algebraMap R _ x` using `rfl`. Rewrite using `[e1, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, Polynomial.algebraMap_apply, Polynomial.map_C, Polynomial.C_comp]`. Conclude with `congrArg Polynomial.C ((cofAct R n).commutes x).symm`.

Consider the case `add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add, Polynomial.add_comp]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, Polynomial.map_mul, Polynomial.mul_comp]`. Use `congrArg₂ (· * ·) rfl ?_` and prove the remaining obligations. Establish `e1 : ∀ w : Fin n × Fin n, cofAct R n (X w) = (genM R n).adjugate w.2.rev w.1` using `fun w => by`.

Simplify using `[cofAct]`. Rewrite using `[e1, rowGen_adjugate_genM R n a b hab]`. Distinguish the cases in `hv : v.1 = b`. Simplify using `[rowGen, hv, e1]`. Simplify using `[rowGen, hv, e1]`.
-/
theorem rowGen_cofAct (R : Type) [CommRing R] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (f : MP R n) :
    rowGen R (n := n) b a (cofAct R n f) =
      ((rowGen R (n := n) a b f).map (cofAct R n).toRingHom).comp (Polynomial.C (-1) * Polynomial.X) := by
  induction f using MvPolynomial.induction_on with
  | C x =>
    have e1 : (C x : MP R n) = algebraMap R _ x := rfl
    rw [e1, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes, Polynomial.algebraMap_apply,
      Polynomial.map_C, Polynomial.C_comp]
    exact congrArg Polynomial.C ((cofAct R n).commutes x).symm
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add, Polynomial.add_comp]
  | mul_X p v hp =>
    simp only [map_mul, hp, Polynomial.map_mul, Polynomial.mul_comp]
    refine congrArg₂ (· * ·) rfl ?_
    have e1 : ∀ w : Fin n × Fin n, cofAct R n (X w) = (genM R n).adjugate w.2.rev w.1 := fun w => by
      simp [cofAct]
    rw [e1, rowGen_adjugate_genM R n a b hab]
    by_cases hv : v.1 = b
    · simp [rowGen, hv, e1]
    · simp [rowGen, hv, e1]

/- English proof (translation)
Unfold `CofRel at h ⊢`. Establish `h1` using `congrArg (fun p => (rowGen R (n := m + 1) b a p).coeff k) h`. Simplify using `only [map_mul, map_pow, rowGen_det_genM R _ a b hab, rowGen_cofAct R _ a b hab, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map] at h1`. Rewrite `h1` using `[← map_pow, Polynomial.coeff_C_mul]`. Establish `h2 : ((-1 : MP R (m + 1)) ^ k) * (-1) ^ k = 1` using `by rw [← mul_pow]; simp`.

Unfold `rowDiv`. Rewrite using `[zsmul_eq_mul, mul_left_comm, h1]`. Use `push_cast`. Rewrite using `[mul_left_comm, h2, mul_one]`. Both sides reduce to the same expression.
-/
theorem cofRel_rowDiv (R : Type) [CommRing R] (m : ℕ) (ν : Fin (m + 1) → ℕ) (a b : Fin (m + 1)) (k : ℕ)
    (f g : MP R (m + 1)) (hab : a ≠ b) (h : CofRel R m ν f g) :
    CofRel R m ν (rowDiv R a b k f) (((-1 : ℤ) ^ k) • rowDiv R b a k g) := by
  unfold CofRel at h ⊢
  have h1 := congrArg (fun p => (rowGen R (n := m + 1) b a p).coeff k) h
  simp only [map_mul, map_pow, rowGen_det_genM R _ a b hab, rowGen_cofAct R _ a b hab,
    Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map] at h1
  rw [← map_pow, Polynomial.coeff_C_mul] at h1
  have h2 : ((-1 : MP R (m + 1)) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  unfold rowDiv
  rw [zsmul_eq_mul, mul_left_comm, h1]
  push_cast
  rw [mul_left_comm, h2, mul_one]
  rfl

end GlobalTheory.ValCmp
