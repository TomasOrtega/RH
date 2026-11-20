import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulEqMulDiagonal

open Matrix

namespace GlobalTheory.SplitHecke

/- English proof (translation)
Take `⟨-, h2, u, hu⟩` from `h`. Take `⟨B, hB⟩` from `intM_iff.1 h2`. Establish `inj : Function.Injective (algebraMap O K)` using `IsFractionRing.injective O K`. Establish `hAB : A * B = p • (1 : Matrix (Fin n) (Fin n) O)`. Apply `Matrix.map_injective inj` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `(A * B).map (algebraMap O K) = (p • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O K)`. Rewrite using `[Matrix.map_mul, hA, hB, Matrix.mul_smul, Units.mul_inv]`. Use extensionality with `i k`. Apply the tactic sequence `by_cases e : i = k <;> simp [e]`. Establish `hdet : Associated A.det (p ^ j)`.

Establish `: A.det = p ^ j * u`. Apply `inj` to reduce the goal to its premises. Rewrite using `[← hu, ← hA, RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[this]`.

Conclude with `(associated_mul_unit_left _ _ u.isUnit)`. Take `⟨P, Q, hP, hQ, hPQ⟩` from `GlobalTheory.SmithBetween.smith_between O p hp n j hj A B hAB hdet`. Use `set r := IsLocalRing.residue O with hr`. Establish `hP' : IsUnit (P.map r).det`. Use `hP.map r` as an intermediate fact.

Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Establish `hQ' : IsUnit (Q.map r).det`. Use `hQ.map r` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Establish `hp0 : r p = 0` using `(IsLocalRing.residue_eq_zero_iff p).2 hp.not_isUnit`.

Establish `h3 : A.map r * Q.map r = P.map r * Matrix.diagonal (fun i : Fin n => if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0)`. Rewrite using `[← Matrix.map_mul, hPQ, Matrix.map_mul, Matrix.diagonal_map (map_zero r)]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `split_ifs <;> simp [hp0]`.

Establish `h4` using `congrArg Matrix.rank h3`. Rewrite `h4` using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP', Matrix.rank_diagonal]`. Establish `h5 : Fintype.card {i : Fin n // (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0} = n - j`. Rewrite using `[Fintype.card_subtype]`. Establish `: (Finset.univ.filter fun i : Fin n => (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0) = Finset.univ.filter fun i : Fin n => i.1 < n - j`.

Use extensionality with `i`. Apply the tactic sequence `by_cases e : i.1 < n - j <;> simp only [Finset.mem_filter, Finset.mem_univ, e, if_true, if_false, true_and, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]`. Rewrite using `[this, Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers. Establish `h6 : (A.map r).rank = n - j`.

Rewrite using `[h4]`. Use `h5` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `(A.map r).rank + j = n`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_range_reduction (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (p : O) (hp : Irreducible p) (n j : ℕ) (a : GL (Fin n) K)
    (A : Matrix (Fin n) (Fin n) O) (hj : j ≤ n) (h : Hk O p j a) (hA : A.map (algebraMap O K) = a.1) :
    Module.finrank (IsLocalRing.ResidueField O)
      (LinearMap.range (A.map (IsLocalRing.residue O)).mulVecLin) + j = n := by
  classical
  obtain ⟨-, h2, u, hu⟩ := h
  obtain ⟨B, hB⟩ := intM_iff.1 h2
  have inj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hAB : A * B = p • (1 : Matrix (Fin n) (Fin n) O) := by
    apply Matrix.map_injective inj
    change (A * B).map (algebraMap O K) = (p • (1 : Matrix (Fin n) (Fin n) O)).map (algebraMap O K)
    rw [Matrix.map_mul, hA, hB, Matrix.mul_smul, Units.mul_inv]
    ext i k
    by_cases e : i = k <;> simp [e]
  have hdet : Associated A.det (p ^ j) := by
    have : A.det = p ^ j * u := by
      apply inj
      rw [← hu, ← hA, RingHom.map_det]
      rfl
    rw [this]
    exact (associated_mul_unit_left _ _ u.isUnit)
  obtain ⟨P, Q, hP, hQ, hPQ⟩ := GlobalTheory.SmithBetween.smith_between O p hp n j hj A B hAB hdet
  set r := IsLocalRing.residue O with hr
  have hP' : IsUnit (P.map r).det := by
    have := hP.map r
    rwa [RingHom.map_det] at this
  have hQ' : IsUnit (Q.map r).det := by
    have := hQ.map r
    rwa [RingHom.map_det] at this
  have hp0 : r p = 0 := (IsLocalRing.residue_eq_zero_iff p).2 hp.not_isUnit
  have h3 : A.map r * Q.map r = P.map r *
      Matrix.diagonal (fun i : Fin n => if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_mul, Matrix.diagonal_map (map_zero r)]
    congr 2
    funext i
    split_ifs <;> simp [hp0]
  have h4 := congrArg Matrix.rank h3
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP',
    Matrix.rank_diagonal] at h4
  have h5 : Fintype.card {i : Fin n // (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0}
      = n - j := by
    rw [Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin n =>
        (if i.1 < n - j then (1 : IsLocalRing.ResidueField O) else 0) ≠ 0)
        = Finset.univ.filter fun i : Fin n => i.1 < n - j := by
      ext i
      by_cases e : i.1 < n - j <;> simp only [Finset.mem_filter, Finset.mem_univ, e, if_true, if_false, true_and, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]
    rw [this, Fin.card_filter_val_lt]
    omega
  have h6 : (A.map r).rank = n - j := by
    rw [h4]
    convert h5
  change (A.map r).rank + j = n
  omega

end GlobalTheory.SplitHecke
