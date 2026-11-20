import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsGenLeadMinorNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

/- English proof (translation)
Unfold `leadMinor pivotMinor`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem leadMinor_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) :
    f (leadMinor M a) = leadMinor (f.mapMatrix M) a := by
  unfold leadMinor pivotMinor
  rw [RingHom.map_det]
  rfl

/- English proof (translation)
Unfold `leadMinor pivotMinor`. Establish `h : (1 : Matrix (Fin n) (Fin n) R).submatrix (Fin.castLE (n` using `(a : ℕ) + 1) (m := n) (by have := a.2; omega)) (pivotCols a (Fin.castLE (Nat.sub_le n 1) a)) = (1 : Matrix (Fin ((a : ℕ) + 1)) (Fin ((a : ℕ) + 1)) R) := by`. Use extensionality with `i j`. Establish `hj : pivotCols a (Fin.castLE (Nat.sub_le n 1) a) j = Fin.castLE (n` using `(a : ℕ) + 1) (m := n) (by have := a.2; omega) j := by`. Unfold `pivotCols`.

Use `split_ifs with hlt`. Both sides reduce to the same expression. Use `ext`. Simplify using `only [Fin.val_castLE]`. Use `j.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Matrix.submatrix_apply, hj, Matrix.one_apply, Matrix.one_apply]`. Simplify using `[Fin.castLE_inj]`. Rewrite using `[h, Matrix.det_one]`.
-/
theorem leadMinor_one {R : Type} [CommRing R] {n : ℕ} (a : Fin (n - 1)) :
    leadMinor (1 : Matrix (Fin n) (Fin n) R) a = 1 := by
  unfold leadMinor pivotMinor
  have h : (1 : Matrix (Fin n) (Fin n) R).submatrix (Fin.castLE (n := (a : ℕ) + 1) (m := n) (by have := a.2; omega))
      (pivotCols a (Fin.castLE (Nat.sub_le n 1) a)) = (1 : Matrix (Fin ((a : ℕ) + 1)) (Fin ((a : ℕ) + 1)) R) := by
    ext i j
    have hj : pivotCols a (Fin.castLE (Nat.sub_le n 1) a) j = Fin.castLE (n := (a : ℕ) + 1) (m := n) (by have := a.2; omega) j := by
      unfold pivotCols
      split_ifs with hlt
      · rfl
      · ext
        simp only [Fin.val_castLE]
        have := j.2
        omega
    rw [Matrix.submatrix_apply, hj, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castLE_inj]
  rw [h, Matrix.det_one]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[genMatFr]`.
-/
theorem genMatFr_eq_map (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) :
    genMatFr F Ψ n τ = (algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)).mapMatrix
      (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (Ψ × Fin n × Fin n) F)) := by
  ext i j
  simp [genMatFr]

/- English proof (translation)
Introduce `F _ Ψ n τ a`. Rewrite using `[genMatFr_eq_map, ← leadMinor_map]`. Use `(map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))).2 ?_` and prove the remaining obligations. Introduce `h0`. Establish `h1` using `congrArg (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)) h0`.

Rewrite `h1` using `[leadMinor_map, map_zero]`. Establish `hP : (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)).mapMatrix (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (Ψ × Fin n × Fin n) F)) = 1`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply]`. Rewrite `h1` using `[hP, leadMinor_one]`.

Conclude with `one_ne_zero h1`.
-/
theorem GenLeadMinorNeZero.full : GenLeadMinorNeZero.Statement := by
  intro F _ Ψ n τ a
  rw [genMatFr_eq_map, ← leadMinor_map]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))).2 ?_
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)) h0
  rw [leadMinor_map, map_zero] at h1
  have hP : (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)).mapMatrix
      (Matrix.of fun i j => (X (τ, i, j) : MvPolynomial (Ψ × Fin n × Fin n) F)) = 1 := by
    ext i j
    simp [Matrix.one_apply]
  rw [hP, leadMinor_one] at h1
  exact one_ne_zero h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
