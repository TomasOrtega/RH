import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePosOf
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model.TS (fockR)

/- English proof (translation)
Unfold `RE`. Simplify using `only [pderiv_X]`. Distinguish the cases in `h : v.1 = b`. Rewrite using `[if_pos h, Finset.sum_eq_single v.2]`. Establish `: ((b, v.2) : Fin k × Fin k) = v` using `Prod.ext h.symm rfl`.

Rewrite using `[this, Pi.single_eq_same, mul_one]`. Introduce `t _ ht`. Rewrite using `[Pi.single_eq_of_ne, mul_zero]`. Introduce `hv`. Apply `ht` to reduce the goal to its premises.

Rewrite using `[hv]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `t _`.

Rewrite using `[Pi.single_eq_of_ne, mul_zero]`. Introduce `hv`. Apply `h` to reduce the goal to its premises. Rewrite using `[hv]`.
-/
theorem RE_X (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (v : Fin k × Fin k) :
    RE K k a b (X v) = if v.1 = b then X (a, v.2) else 0 := by
  unfold RE
  simp only [pderiv_X]
  by_cases h : v.1 = b
  · rw [if_pos h, Finset.sum_eq_single v.2]
    · have : ((b, v.2) : Fin k × Fin k) = v := Prod.ext h.symm rfl
      rw [this, Pi.single_eq_same, mul_one]
    · intro t _ ht
      rw [Pi.single_eq_of_ne, mul_zero]
      intro hv
      apply ht
      rw [hv]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro t _
    rw [Pi.single_eq_of_ne, mul_zero]
    intro hv
    apply h
    rw [hv]

/- English proof (translation)
Unfold `RE`. Simplify using the standard rewrite rules.
-/
theorem RE_C (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (r : K) : RE K k a b (C r) = 0 := by
  unfold RE
  simp

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C r => simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq]`. Consider the case `mul_X p v hp`. Rewrite using `[map_mul, Polynomial.mul_coeff_zero, hp]`.

Use `congr 1`. Simplify using `only [rowGen, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem rowGen_coeff_zero (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    (rowGen K a b f).coeff 0 = f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp

/- English proof (translation)
Unfold `rowDiv`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C r => rw [RE_C]`. Simplify using `[rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, Polynomial.coeff_C]`. Consider the case `add p q hp hq => rw [RE_add, map_add, Polynomial.coeff_add, hp, hq]`.

Consider the case `mul_X p v hp`. Rewrite using `[RE_mul, map_mul, Polynomial.mul_coeff_one, rowGen_coeff_zero, rowGen_coeff_zero, hp, RE_X]`. Establish `: (rowGen K a b (X v)).coeff 1 = if v.1 = b then X (a, v.2) else 0`. Simplify using `only [rowGen, aeval_X]`. Apply the tactic sequence `split_ifs <;> simp [Polynomial.coeff_C]`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem RE_eq_rowDiv (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b f = rowDiv K a b 1 f := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on with
  | C r => rw [RE_C]; simp [rowGen, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, Polynomial.coeff_C]
  | add p q hp hq => rw [RE_add, map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [RE_mul, map_mul, Polynomial.mul_coeff_one, rowGen_coeff_zero, rowGen_coeff_zero, hp, RE_X]
    have : (rowGen K a b (X v)).coeff 1 = if v.1 = b then X (a, v.2) else 0 := by
      simp only [rowGen, aeval_X]
      split_ifs <;> simp [Polynomial.coeff_C]
    rw [this]
    ring

/- English proof (translation)
Introduce `K _ k a b P Q`. Rewrite using `[RE_eq_rowDiv, RE_eq_rowDiv]`. Conclude with `Formalism.L2.G.Model.TS.Top.fockRRowDivAdj K k k a b 1 P Q`.
-/
theorem restAdj : RestAdj := by
  intro K _ k a b P Q
  rw [RE_eq_rowDiv, RE_eq_rowDiv]
  exact Formalism.L2.G.Model.TS.Top.fockRRowDivAdj K k k a b 1 P Q

/- English proof (translation)
Introduce `K _ _ k ν a b P hP`. Rewrite using `[RE_eq_rowDiv]`. Conclude with `rowDivStable K k k ν a b 1 P hP`.
-/
theorem restStab : RestStab := by
  intro K _ _ k ν a b P hP
  rw [RE_eq_rowDiv]
  exact rowDivStable K k k ν a b 1 P hP

end Formalism.MainNotions.TestSideCounting
