import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

/- English proof (translation)
Establish `hc : Commute X (γ.map (algebraMap K R))` using `hX`. Establish `key : ∀ h : K[X], Commute X (((algebraMap K R).mapMatrix (m` using `Fin n)) (aeval γ h)) := by`. Introduce `h`. Proceed by induction on `h using Polynomial.induction_on' with`. Consider the case `add p q hp hq`.

Rewrite using `[map_add, map_add]`. Conclude with `hp.add_right hq`. Consider the case `monomial k a`. Rewrite using `[aeval_monomial, map_mul, map_pow]`. Establish `h1 : ((algebraMap K R).mapMatrix (m` using `Fin n)) γ = γ.map (algebraMap K R) := rfl`.

Rewrite using `[h1]`. Use `Commute.mul_right ?_ (hc.pow_right k)` and prove the remaining obligations. Establish `h2 : ((algebraMap K R).mapMatrix (m` using `Fin n)) (algebraMap K (Matrix (Fin n) (Fin n) K) a) = (algebraMap K R a) • (1 : Matrix (Fin n) (Fin n) R) := by`. Use extensionality with `i j`. Simplify using `[Matrix.algebraMap_matrix_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one]`.

Rewrite using `[h2]`. Conclude with `(Commute.one_right X).smul_right _`. Conclude with `key h`.
-/
theorem map_aeval_commute_of_commute {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin n) R)
    (hX : X * γ.map (algebraMap K R) = γ.map (algebraMap K R) * X) (h : K[X]) :
    X * (aeval γ h).map (algebraMap K R) = (aeval γ h).map (algebraMap K R) * X := by
  have hc : Commute X (γ.map (algebraMap K R)) := hX
  have key : ∀ h : K[X], Commute X (((algebraMap K R).mapMatrix (m := Fin n)) (aeval γ h)) := by
    intro h
    induction h using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, map_add]
      exact hp.add_right hq
    | monomial k a =>
      rw [aeval_monomial, map_mul, map_pow]
      have h1 : ((algebraMap K R).mapMatrix (m := Fin n)) γ = γ.map (algebraMap K R) := rfl
      rw [h1]
      refine Commute.mul_right ?_ (hc.pow_right k)
      have h2 : ((algebraMap K R).mapMatrix (m := Fin n)) (algebraMap K (Matrix (Fin n) (Fin n) K) a)
          = (algebraMap K R a) • (1 : Matrix (Fin n) (Fin n) R) := by
        ext i j
        simp [Matrix.algebraMap_matrix_apply, Matrix.one_apply, Algebra.algebraMap_eq_smul_one]
      rw [h2]
      exact (Commute.one_right X).smul_right _
  exact key h

/- English proof (translation)
Use `choose h hh using fun j : Fin n => hv (Pi.single j 1)`. Use `set φ := algebraMap K R with hφ`. Use `set A : Fin n → Matrix (Fin n) (Fin n) R := fun j => (aeval γ (h j)).map φ with hA`. Use `set vR : Fin n → R := φ ∘ v with hvR`. Establish `hAv : ∀ j, A j *ᵥ vR = Pi.single j 1`.

Introduce `j`. Use extensionality with `i`. Use `RingHom.map_mulVec φ (aeval γ (h j)) v i` as an intermediate fact. Rewrite using `[hA, hvR]`. Simplify using `only`.

Rewrite using `[← this, ← hh j]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hij]`.

Use `set w := X *ᵥ vR with hw`. Use `set X' : Matrix (Fin n) (Fin n) R := ∑ j, w j • A j with hX'`. Establish `hX'v : X' *ᵥ vR = w`. Rewrite using `[hX', Matrix.sum_mulVec]`. Simplify using `only [Matrix.smul_mulVec, hAv]`.

Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `hXA : ∀ j, X * A j = A j * X` using `fun j => map_aeval_commute_of_commute γ X hX (h j)`. Establish `hYA : ∀ j, Y * A j = A j * Y` using `fun j => map_aeval_commute_of_commute γ Y hY (h j)`. Establish `hAA : ∀ i j, A i * A j = A j * A i`.

Introduce `i j`. Simplify using `only [hA]`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul, mul_comm]`. Establish `hX'A : ∀ j, X' * A j = A j * X'`. Introduce `j`.

Rewrite using `[hX', Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, hAA i j]`. Establish `hD : ∀ j, (X - X') *ᵥ (Pi.single j 1 : Fin n → R) = 0`. Introduce `j`.

Rewrite using `[← hAv j, Matrix.mulVec_mulVec, sub_mul, hXA j, hX'A j, ← mul_sub, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, hX'v, ← hw, sub_self, Matrix.mulVec_zero]`. Establish `hXX' : X = X'`. Use `sub_eq_zero.mp ?_` and prove the remaining obligations. Use extensionality with `i j`. Use `congrFun (hD j) i` as an intermediate fact.

Simplify using `using this`. Rewrite using `[hXX', hX', Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, hYA j]`.
-/
theorem commute_of_commute_cyclic (K : Type) [Field K] (R : Type) [CommRing R] [Algebra K R] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (hv : ∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v)
    (X Y : Matrix (Fin n) (Fin n) R)
    (hX : X * γ.map (algebraMap K R) = γ.map (algebraMap K R) * X)
    (hY : Y * γ.map (algebraMap K R) = γ.map (algebraMap K R) * Y) : X * Y = Y * X := by
  classical
  choose h hh using fun j : Fin n => hv (Pi.single j 1)
  set φ := algebraMap K R with hφ
  set A : Fin n → Matrix (Fin n) (Fin n) R := fun j => (aeval γ (h j)).map φ with hA
  set vR : Fin n → R := φ ∘ v with hvR
  have hAv : ∀ j, A j *ᵥ vR = Pi.single j 1 := by
    intro j
    ext i
    have := RingHom.map_mulVec φ (aeval γ (h j)) v i
    rw [hA, hvR]
    simp only
    rw [← this, ← hh j]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  set w := X *ᵥ vR with hw
  set X' : Matrix (Fin n) (Fin n) R := ∑ j, w j • A j with hX'
  have hX'v : X' *ᵥ vR = w := by
    rw [hX', Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec, hAv]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hXA : ∀ j, X * A j = A j * X := fun j => map_aeval_commute_of_commute γ X hX (h j)
  have hYA : ∀ j, Y * A j = A j * Y := fun j => map_aeval_commute_of_commute γ Y hY (h j)
  have hAA : ∀ i j, A i * A j = A j * A i := by
    intro i j
    simp only [hA]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← map_mul, ← map_mul, mul_comm]
  have hX'A : ∀ j, X' * A j = A j * X' := by
    intro j
    rw [hX', Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hAA i j]
  have hD : ∀ j, (X - X') *ᵥ (Pi.single j 1 : Fin n → R) = 0 := by
    intro j
    rw [← hAv j, Matrix.mulVec_mulVec, sub_mul, hXA j, hX'A j, ← mul_sub, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, hX'v, ← hw, sub_self, Matrix.mulVec_zero]
  have hXX' : X = X' := by
    refine sub_eq_zero.mp ?_
    ext i j
    have := congrFun (hD j) i
    simpa using this
  rw [hXX', hX', Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, hYA j]

end GlobalTheory.CompanionTheory.TorusCh
