import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SatisfiesGlRelationsBilinearLeft
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowDivStable
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.HWRaise

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

def pol (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin m) R →ₗ[R] MvPolynomial (Fin r × Fin m) R :=
  ∑ s : Fin m, (LinearMap.mulLeft R (X (a, s))) ∘ₗ
    ((pderiv (b, s) : Derivation R (MvPolynomial (Fin r × Fin m) R) (MvPolynomial (Fin r × Fin m) R)).toLinearMap)

/- English proof (translation)
Simplify using `[pol, LinearMap.sum_apply]`.
-/
theorem pol_apply (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    pol R a b f = ∑ s : Fin m, X (a, s) * pderiv (b, s) f := by
  simp [pol, LinearMap.sum_apply]

/- English proof (translation)
Simplify using `only [pol_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun s _ => by ring` and prove the remaining obligations.
-/
theorem pol_mul (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f g : MvPolynomial (Fin r × Fin m) R) :
    pol R a b (f * g) = pol R a b f * g + f * pol R a b g := by
  simp only [pol_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => by ring

/- English proof (translation)
Rewrite using `[pol_apply]`. Distinguish the cases in `hv : v.1 = b`. Rewrite using `[if_pos hv, Finset.sum_eq_single v.2]`. Establish `: (b, v.2) = v` using `by rw [← hv]`. Rewrite using `[this, pderiv_X_self, mul_one]`.

Introduce `s _ hs`. Rewrite using `[pderiv_X_of_ne, mul_zero]`. Introduce `h; exact hs (by rw [h])`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hv]`.

Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_X_of_ne, mul_zero]`. Introduce `h; exact hv (by rw [h])`.
-/
theorem pol_X (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (v : Fin r × Fin m) :
    pol R a b (X v) = if v.1 = b then X (a, v.2) else 0 := by
  classical
  rw [pol_apply]
  by_cases hv : v.1 = b
  · rw [if_pos hv, Finset.sum_eq_single v.2]
    · have : (b, v.2) = v := by rw [← hv]
      rw [this, pderiv_X_self, mul_one]
    · intro s _ hs
      rw [pderiv_X_of_ne, mul_zero]
      intro h; exact hs (by rw [h])
    · simp
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [pderiv_X_of_ne, mul_zero]
    intro h; exact hv (by rw [h])

/- English proof (translation)
Simplify using `[pol_apply]`.
-/
theorem pol_C (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (c : R) :
    pol R a b (C c : MvPolynomial (Fin r × Fin m) R) = 0 := by
  simp [pol_apply]

/- English proof (translation)
Simplify using `[rowGen]`.
-/
theorem rowGen_X' (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (v : Fin r × Fin m) :
    rowGen R a b (X v) = Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) := by
  simp [rowGen]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c`. Rewrite using `[pol_C, map_zero]`. Establish `: rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c)`. Simplify using `[rowGen]`.

Rewrite using `[this, Polynomial.derivative_C, mul_zero]`. Consider the case `add p q hp hq => rw [map_add, Polynomial.derivative_add, mul_add, hp, hq, map_add, map_add]`. Consider the case `mul_X p v hp`. Rewrite using `[map_mul, Polynomial.derivative_mul, mul_add, pol_mul, map_add, map_mul, map_mul, ← hp, pol_X]`. Establish `hg : (if a = b then 1 + Polynomial.X else 1) * Polynomial.derivative (rowGen R a b (X v)) = rowGen R a b (if v.1 = b then X (a, v.2) else 0)`.

Rewrite using `[rowGen_X']`. Distinguish the cases in `hv : v.1 = b`. Simplify using `only [hv, if_true, Polynomial.derivative_add, Polynomial.derivative_C, zero_add, Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, mul_zero, add_zero, rowGen_X']`. Distinguish the cases in `hab : a = b`. Simplify using `[hab]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[hab]`. Simplify using `[hv]`. Rewrite using `[← hg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deriv_rowGen (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    (if a = b then 1 + Polynomial.X else 1) * Polynomial.derivative (rowGen R a b f) =
      rowGen R a b (pol R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [pol_C, map_zero]
    have : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c) := by
      simp [rowGen]
    rw [this, Polynomial.derivative_C, mul_zero]
  | add p q hp hq => rw [map_add, Polynomial.derivative_add, mul_add, hp, hq, map_add, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, mul_add, pol_mul, map_add, map_mul, map_mul, ← hp, pol_X]
    have hg : (if a = b then 1 + Polynomial.X else 1) * Polynomial.derivative (rowGen R a b (X v)) =
        rowGen R a b (if v.1 = b then X (a, v.2) else 0) := by
      rw [rowGen_X']
      by_cases hv : v.1 = b
      · simp only [hv, if_true, Polynomial.derivative_add, Polynomial.derivative_C, zero_add,
          Polynomial.derivative_mul, Polynomial.derivative_X, one_mul, mul_zero, add_zero, rowGen_X']
        by_cases hab : a = b
        · simp [hab]; ring
        · simp [hab]
      · simp [hv]
    rw [← hg]; ring

/- English proof (translation)
Rewrite using `[Polynomial.coeff_zero_eq_eval_zero]`. Establish `hh : ((Polynomial.aeval (0 : MvPolynomial (Fin r × Fin m) R)).restrictScalars R).comp (rowGen R a b) = AlgHom.id R _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[rowGen]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h2` using `congrArg (fun φ => φ f) hh`. Simplify `h2` using `[Polynomial.coe_aeval_eq_eval]`.
-/
theorem rowGen_coeff_zero (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    (rowGen R a b f).coeff 0 = f := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have hh : ((Polynomial.aeval (0 : MvPolynomial (Fin r × Fin m) R)).restrictScalars R).comp (rowGen R a b) =
      AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowGen]
    split_ifs <;> simp
  have h2 := congrArg (fun φ => φ f) hh
  simpa [Polynomial.coe_aeval_eq_eval] using h2

/- English proof (translation)
The claim follows from `rowGen_coeff_zero R a b f`.
-/
theorem rowDiv_zero (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b 0 f = f := rowGen_coeff_zero R a b f

/- English proof (translation)
Establish `h` using `congrArg (fun p => Polynomial.coeff p k) (deriv_rowGen R a b f)`. Unfold `rowDiv`. Rewrite using `[← h]`. Distinguish the cases in `hab : a = b`. Simplify using `only [hab, if_true, add_mul, one_mul, Polynomial.coeff_add]`.

Rewrite using `[Polynomial.coeff_derivative]`. Consider the cases of `k with`. Consider the case `zero => simp [Polynomial.coeff_derivative]`. Consider the case `succ k`. Rewrite using `[Polynomial.coeff_X_mul, Polynomial.coeff_derivative]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hab, if_false, one_mul, add_zero, Polynomial.coeff_derivative]`.
-/
theorem rowDiv_succ (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b (k + 1) f * ((k : MvPolynomial (Fin r × Fin m) R) + 1) +
      (if a = b then rowDiv R a b k f * (k : MvPolynomial (Fin r × Fin m) R) else 0) =
      rowDiv R a b k (pol R a b f) := by
  have h := congrArg (fun p => Polynomial.coeff p k) (deriv_rowGen R a b f)
  unfold rowDiv
  rw [← h]
  by_cases hab : a = b
  · simp only [hab, if_true, add_mul, one_mul, Polynomial.coeff_add]
    rw [Polynomial.coeff_derivative]
    cases k with
    | zero => simp [Polynomial.coeff_derivative]
    | succ k =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      push_cast; ring
  · simp only [hab, if_false, one_mul, add_zero, Polynomial.coeff_derivative]

/- English proof (translation)
Establish `h` using `rowDiv_succ R a b 0 f`. Simplify using `only [Nat.cast_zero, zero_add, mul_one, mul_zero, ite_self, add_zero, rowDiv_zero] at h`. Conclude with `h.symm`.
-/
theorem pol_eq_rowDiv (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) :
    pol R a b f = rowDiv R a b 1 f := by
  have h := rowDiv_succ R a b 0 f
  simp only [Nat.cast_zero, zero_add, mul_one, mul_zero, ite_self, add_zero, rowDiv_zero] at h
  exact h.symm

/- English proof (translation)
Simplify using `[pol_apply, pderiv_map, map_sum]`.
-/
theorem pol_map {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {r m : ℕ} (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin m) R) :
    pol S a b (MvPolynomial.map ψ f) = MvPolynomial.map ψ (pol R a b f) := by
  simp [pol_apply, pderiv_map, map_sum]

/- English proof (translation)
Rewrite using `[pol_eq_rowDiv]`. Conclude with `dualWeylModuleRowDividedPowerStable R r m ν a b 1 f hf`.
-/
theorem pol_mem_dualWeyl (R : Type) [CommRing R] {r m : ℕ} (ν : Fin m → ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin m) R) (hf : f ∈ dualWeyl R r m ν) : pol R a b f ∈ dualWeyl R r m ν := by
  rw [pol_eq_rowDiv]; exact dualWeylModuleRowDividedPowerStable R r m ν a b 1 f hf

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Simplify using `[pol_apply, Formalism.REAL.Eg, Formalism.REAL.bpl, Formalism.REAL.bop, Formalism.REAL.sgnv, LinearMap.sum_apply]`.
-/
theorem pol_eq_Eg {r m : ℕ} (a b : Fin r) :
    pol ℂ (m := m) a b = Formalism.REAL.Eg (fun _ => true) (fun _ => true) a b := by
  apply LinearMap.ext; intro f
  simp [pol_apply, Formalism.REAL.Eg, Formalism.REAL.bpl, Formalism.REAL.bop, Formalism.REAL.sgnv, LinearMap.sum_apply]

/- English proof (translation)
Establish `h` using `(Formalism.REAL.fockPairGl_of Formalism.REAL.canonicalCommutation_holds r m (fun _ => true) (fun _ => true)).1`. Introduce `a b c d`. Simplify using `only [pol_eq_Eg]`. Conclude with `h a b c d`.
-/
theorem pol_glRel (r m : ℕ) : Formalism.REAL.GlRel (fun a b : Fin r => (pol ℂ (m := m) a b : Module.End ℂ _)) := by
  have h := (Formalism.REAL.fockPairGl_of Formalism.REAL.canonicalCommutation_holds r m (fun _ => true) (fun _ => true)).1
  intro a b c d
  simp only [pol_eq_Eg]
  exact h a b c d

end PI.WGL
