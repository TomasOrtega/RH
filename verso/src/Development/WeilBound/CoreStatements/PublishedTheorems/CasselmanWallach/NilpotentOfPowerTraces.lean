import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
import GroundTheory.GlobalFields.Artin.LogCharpoly

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CharpolyPowerTraces

open Polynomial

/- English proof (translation)
Establish `hps : (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0`. Use extensionality with `k`. Simplify using `[h]`. Establish `hd : derivative N.charpolyRev = 0`. Establish `hc` using `GroundTheory.Global.coe_derivative_charpolyRev N`.

Rewrite `hc` using `[hps, mul_zero]`. Conclude with `Polynomial.coe_eq_zero_iff.mp hc`. Establish `hm` using `congrArg (fun p => Polynomial.coeff p m) hd`. Simplify using `only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hm`. Rewrite using `[mul_comm]`.

Conclude with `hm`.
-/
theorem coeff_succ {R : Type} [CommRing R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (h : ∀ k, (N ^ (k + 1)).trace = 0) (m : ℕ) :
    ((m : R) + 1) * N.charpolyRev.coeff (m + 1) = 0 := by
  have hps : (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0 := by
    ext k
    simp [h]
  have hd : derivative N.charpolyRev = 0 := by
    have hc := GroundTheory.Global.coe_derivative_charpolyRev N
    rw [hps, mul_zero] at hc
    exact Polynomial.coe_eq_zero_iff.mp hc
  have hm := congrArg (fun p => Polynomial.coeff p m) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hm
  rw [mul_comm]
  exact hm

/- English proof (translation)
Establish `hu : IsUnit ((m : R) + 1)`. Establish `: ((m : R) + 1) = algebraMap ℚ R ((m : ℚ) + 1)` using `by simp`. Rewrite using `[this]; exact (IsUnit.mk0 _ (by positivity)).map _`. Conclude with `hu.mul_right_eq_zero.mp (coeff_succ N h m)`.
-/
theorem coeff_succ_zero {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (h : ∀ k, (N ^ (k + 1)).trace = 0) (m : ℕ) : N.charpolyRev.coeff (m + 1) = 0 := by
  have hu : IsUnit ((m : R) + 1) := by
    have : ((m : R) + 1) = algebraMap ℚ R ((m : ℚ) + 1) := by simp
    rw [this]; exact (IsUnit.mk0 _ (by positivity)).map _
  exact hu.mul_right_eq_zero.mp (coeff_succ N h m)

/- English proof (translation)
Establish `hRev : ∀ i, 1 ≤ i → N.charpolyRev.coeff i = 0`. Introduce `i hi`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le' hi`. Conclude with `coeff_succ_zero N h m`. Establish `hdeg : N.charpoly.natDegree = n`.

Rewrite using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Use extensionality with `j`. Rewrite using `[Polynomial.coeff_X_pow]`. Break down `lt_trichotomy j n with hj | hj | hj` into its components or cases. Rewrite using `[if_neg hj.ne]`.

Establish `hz` using `hRev (n - j) (by omega)`. Rewrite `hz` using `[← Matrix.reverse_charpoly, Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le (by omega)]`. Rewrite `hz` using `[show n - (n - j) = j by omega]`. Then use the resulting hypothesis. Rewrite using `[if_pos hj]`. Establish `hl` using `(Matrix.charpoly_monic N).leadingCoeff`.

Rewrite `hl` using `[Polynomial.leadingCoeff, hdeg]`. Rewrite using `[hj]`. Conclude with `hl`. Rewrite using `[if_neg hj.ne']`. Conclude with `Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)`.
-/
theorem charpoly_eq {R : Type} [CommRing R] [Algebra ℚ R] [Nontrivial R] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) R) (h : ∀ k, (N ^ (k + 1)).trace = 0) : N.charpoly = X ^ n := by
  have hRev : ∀ i, 1 ≤ i → N.charpolyRev.coeff i = 0 := by
    intro i hi
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hi
    exact coeff_succ_zero N h m
  have hdeg : N.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  ext j
  rw [Polynomial.coeff_X_pow]
  rcases lt_trichotomy j n with hj | hj | hj
  · rw [if_neg hj.ne]
    have hz := hRev (n - j) (by omega)
    rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, hdeg,
      Polynomial.revAt_le (by omega)] at hz
    rwa [show n - (n - j) = j by omega] at hz
  · rw [if_pos hj]
    have hl := (Matrix.charpoly_monic N).leadingCoeff
    rw [Polynomial.leadingCoeff, hdeg] at hl
    rw [hj]
    exact hl
  · rw [if_neg hj.ne']
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end CharpolyPowerTraces

/- English proof (translation)
Unfold `A4`. Introduce `R _ _ n N h`. Break down `subsingleton_or_nontrivial R with hR | hR` into its components or cases. Conclude with `Subsingleton.elim _ _`. Establish `hc` using `Matrix.aeval_self_charpoly N`.

Rewrite `hc` using `[CharpolyPowerTraces.charpoly_eq N h, Polynomial.aeval_X_pow]`. Conclude with `hc`.
-/
theorem nilpotent_of_power_traces : A4 := by
  unfold A4
  intro R _ _ n N h
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hc := Matrix.aeval_self_charpoly N
  rw [CharpolyPowerTraces.charpoly_eq N h, Polynomial.aeval_X_pow] at hc
  exact hc

end PositivityTheory.CW

end
