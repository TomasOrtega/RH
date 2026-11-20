import Formalism.GaloisIrreducibility.Statement

namespace Formalism.GaloisIrreducibility
open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => Fin.succ_ne_zero k h.symm, fun h => h.elim⟩`.
-/
@[simp] lemma zero_ne_succ' {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := ⟨fun h => Fin.succ_ne_zero k h.symm, fun h => h.elim⟩

def bord {m : ℕ} (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m+1)) (Fin (m+1)) R :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (M i)))

/- English proof (translation)
Simplify using `[bord]`.
-/
@[simp] lemma bord_zero_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) R) : bord M 0 0 = 1 := by
  simp [bord]
/- English proof (translation)
Simplify using `[bord]`.
-/
@[simp] lemma bord_zero_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (j : Fin m) :
    bord M 0 j.succ = 0 := by
  simp [bord]
/- English proof (translation)
Simplify using `[bord]`.
-/
@[simp] lemma bord_succ_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i : Fin m) :
    bord M i.succ 0 = 0 := by
  simp [bord]
/- English proof (translation)
Simplify using `[bord]`.
-/
@[simp] lemma bord_succ_succ {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    bord M i.succ j.succ = M i j := by
  simp [bord]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
lemma bord_mul {m : ℕ} (M N : Matrix (Fin m) (Fin m) R) : bord M * bord N = bord (M * N) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>`. Simplify using `[Matrix.one_apply]`.
-/
lemma bord_one {m : ℕ} : bord (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply]

/- English proof (translation)
Take `⟨u, rfl⟩` from `h`. Use `⟨⟨bord (u : Matrix (Fin m) (Fin m) R), bord (↑u⁻¹ : Matrix (Fin m) (Fin m) R), ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use `first`. Consider the case `rw [bord_mul, Units.mul_inv, bord_one]`. Consider the case `simp [bord_mul, bord_one]`.

Use `first`. Consider the case `rw [bord_mul, Units.inv_mul, bord_one]`. Consider the case `simp [bord_mul, bord_one]`.
-/
lemma bord_isUnit {m : ℕ} {M : Matrix (Fin m) (Fin m) R} (h : IsUnit M) : IsUnit (bord M) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨⟨bord (u : Matrix (Fin m) (Fin m) R), bord (↑u⁻¹ : Matrix (Fin m) (Fin m) R), ?_, ?_⟩, rfl⟩
  · first
    | rw [bord_mul, Units.mul_inv, bord_one]
    | simp [bord_mul, bord_one]
  · first
    | rw [bord_mul, Units.inv_mul, bord_one]
    | simp [bord_mul, bord_one]

/- English proof (translation)
Establish `h0 : (0 : ℕ) ≠ n + 1` using `by omega`. Establish `h0' : n + 1 ≠ 0` using `by omega`. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>`. Simplify using `[Matrix.diagonal_apply, h0, h0']`.
-/
lemma bord_diag {n : ℕ} (d : R) :
    bord (diagonal fun i : Fin (n+1) => if (i : ℕ) = n then d else 1) =
      diagonal fun i : Fin (n+2) => if (i : ℕ) = n + 1 then d else 1 := by
  have h0 : (0 : ℕ) ≠ n + 1 := by omega
  have h0' : n + 1 ≠ 0 := by omega
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.diagonal_apply, h0, h0']

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>`. Simplify using `[Matrix.map_apply]`.
-/
lemma bord_map {S : Type} [CommRing S] (φ : R →+* S) {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    (bord M).map φ = bord (M.map φ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.map_apply]

/- English proof (translation)
Unfold `Matrix.rank`. Rewrite using `[Matrix.mulVecLin_add]`. Conclude with `(Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)`.
-/
lemma rank_add_le' {K : Type} [Field K] {m : ℕ} (A B : Matrix (Fin m) (Fin m) K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/- English proof (translation)
Set `S : Matrix (Fin (m+1)) (Fin m) K` to `Matrix.of fun i k => if i = k.succ then 1 else 0`. Set `T : Matrix (Fin m) (Fin (m+1)) K` to `Matrix.of fun k j => if j = k.succ then 1 else 0`. Set `S' : Matrix (Fin (m+1)) (Fin 1) K` to `Matrix.of fun i _ => if i = 0 then 1 else 0`. Set `T' : Matrix (Fin 1) (Fin (m+1)) K` to `Matrix.of fun _ j => if j = 0 then 1 else 0`. Establish `hsplit : bord M = S' * T' + S * M * T`.

Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>`. Simplify using `[S, T, S', T', Matrix.mul_apply, Fin.sum_univ_succ]`. Rewrite using `[hsplit]`. Use `(rank_add_le' _ _).trans ?_` and prove the remaining obligations.

Establish `h1 : (S' * T').rank ≤ 1` using `(Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width S')`. Establish `h2 : (S * M * T).rank ≤ M.rank` using `(Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)`. Use linear arithmetic over natural numbers and integers.
-/
lemma rank_bord_le {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K) :
    (bord M).rank ≤ M.rank + 1 := by
  classical
  let S : Matrix (Fin (m+1)) (Fin m) K := Matrix.of fun i k => if i = k.succ then 1 else 0
  let T : Matrix (Fin m) (Fin (m+1)) K := Matrix.of fun k j => if j = k.succ then 1 else 0
  let S' : Matrix (Fin (m+1)) (Fin 1) K := Matrix.of fun i _ => if i = 0 then 1 else 0
  let T' : Matrix (Fin 1) (Fin (m+1)) K := Matrix.of fun _ j => if j = 0 then 1 else 0
  have hsplit : bord M = S' * T' + S * M * T := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [S, T, S', T', Matrix.mul_apply, Fin.sum_univ_succ]
  rw [hsplit]
  refine (rank_add_le' _ _).trans ?_
  have h1 : (S' * T').rank ≤ 1 :=
    (Matrix.rank_mul_le_left _ _).trans (by simpa using Matrix.rank_le_card_width S')
  have h2 : (S * M * T).rank ≤ M.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  omega

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R]

def Equi {s : ℕ} (A B : Matrix (Fin s) (Fin s) R) : Prop :=
  ∃ P Q : Matrix (Fin s) (Fin s) R, IsUnit P ∧ IsUnit Q ∧ P * A * Q = B

/- English proof (translation)
Unfold `Equi at h1 h2 ⊢`. Take `⟨P1, Q1, hP1, hQ1, rfl⟩` from `h1`. Take `⟨P2, Q2, hP2, hQ2, rfl⟩` from `h2`. Conclude with `⟨P2 * P1, Q1 * Q2, hP2.mul hP1, hQ1.mul hQ2, by simp only [Matrix.mul_assoc]⟩`.
-/
lemma Equi.trans {s : ℕ} {A B C : Matrix (Fin s) (Fin s) R} (h1 : Equi A B) (h2 : Equi B C) :
    Equi A C := by
  unfold Equi at h1 h2 ⊢
  obtain ⟨P1, Q1, hP1, hQ1, rfl⟩ := h1
  obtain ⟨P2, Q2, hP2, hQ2, rfl⟩ := h2
  exact ⟨P2 * P1, Q1 * Q2, hP2.mul hP1, hQ1.mul hQ2, by simp only [Matrix.mul_assoc]⟩

/- English proof (translation)
Unfold `Equi at h`. Take `⟨P, Q, hP, hQ, rfl⟩` from `h`. Establish `hP' : IsUnit (P.map φ).det`. Rewrite using `[← Matrix.isUnit_iff_isUnit_det]`. Simplify using `using hP.map φ.mapMatrix`.

Establish `hQ' : IsUnit (Q.map φ).det`. Rewrite using `[← Matrix.isUnit_iff_isUnit_det]`. Simplify using `using hQ.map φ.mapMatrix`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP']`.
-/
lemma Equi.rank_map {K : Type} [Field K] (φ : R →+* K) {s : ℕ}
    {A B : Matrix (Fin s) (Fin s) R} (h : Equi A B) : (B.map φ).rank = (A.map φ).rank := by
  unfold Equi at h
  obtain ⟨P, Q, hP, hQ, rfl⟩ := h
  have hP' : IsUnit (P.map φ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; simpa using hP.map φ.mapMatrix
  have hQ' : IsUnit (Q.map φ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det]; simpa using hQ.map φ.mapMatrix
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP']

/- English proof (translation)
Use `⟨⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Use `first`. Consider the case `rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]`. Consider the case `simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]`. Use `first`.

Consider the case `rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]`. Consider the case `simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]`.
-/
lemma perm_isUnit {s : ℕ} (σ : Equiv.Perm (Fin s)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin s) (Fin s) R) := by
  refine ⟨⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, ?_, ?_⟩, rfl⟩
  · first
    | rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
    | simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]
  · first
    | rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self,
        Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
    | simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

/- English proof (translation)
Unfold `Equi`. Use `⟨σ.toPEquiv.toMatrix, τ.symm.toPEquiv.toMatrix, perm_isUnit σ, perm_isUnit τ.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
lemma equi_submatrix {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (σ τ : Equiv.Perm (Fin s)) :
    Equi A (A.submatrix σ τ) := by
  unfold Equi
  refine ⟨σ.toPEquiv.toMatrix, τ.symm.toPEquiv.toMatrix, perm_isUnit σ, perm_isUnit τ.symm, ?_⟩
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp

/- English proof (translation)
Take `⟨b, hb⟩ : ∃ b : R, A 0 0 * b = 1` from `⟨_, hu.mul_val_inv⟩`. Establish `hb' : b * A 0 0 = 1` using `by rw [mul_comm]; exact hb`. Use `set P : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons (-(A i.succ 0 * b)) (fun j => if i = j then 1 else 0))) with hP`. Use `set Pinv : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons (A i.succ 0 * b) (fun j => if i = j then 1 else 0))) with hPinv`. Use `set Q : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons b (fun j => -(b * A 0 j.succ))) (fun i => Fin.cons 0 (fun j => if i = j then 1 else 0))) with hQ`.

Use `set Qinv : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons (A 0 0) (fun j => A 0 j.succ)) (fun i => Fin.cons 0 (fun j => if i = j then 1 else 0))) with hQinv`. Use `set A' : Matrix (Fin m) (Fin m) R := Matrix.of fun i j => A i.succ j.succ - A i.succ 0 * b * A 0 j.succ with hA'`. Establish `hPP : P * Pinv = 1`. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>`.

Simplify using `[hP, hPinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]`. Establish `hQQ : Q * Qinv = 1`. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>`. Simplify using `[hQ, hQinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hb']`.

Establish `hPu : IsUnit P`. Establish `h : P.det * Pinv.det = 1` using `by rw [← Matrix.det_mul, hPP, Matrix.det_one]`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Use `first`. Consider the case `exact isUnit_iff_exists_inv.mpr ⟨_, h⟩`.

Consider the case `exact IsUnit.of_mul_eq_one _ h`. Establish `hQu : IsUnit Q`. Establish `h : Q.det * Qinv.det = 1` using `by rw [← Matrix.det_mul, hQQ, Matrix.det_one]`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Use `first`.

Consider the case `exact isUnit_iff_exists_inv.mpr ⟨_, h⟩`. Consider the case `exact IsUnit.of_mul_eq_one _ h`. Establish `key : P * A * Q = bord A'`. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`.

Apply the tactic sequence `simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;> first | linear_combination hb | linear_combination (-1 : R) * hb`. Apply the tactic sequence `simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;> first | linear_combination (-(A 0 j.succ)) * hb | linear_combination (A 0 j.succ) * hb`. Apply the tactic sequence `simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;> first | linear_combination (-(A i.succ 0 * b)) * hb' | linear_combination (A i.succ 0 * b) * hb'`. Apply the tactic sequence `simp [hP, hQ, hA', Matrix.mul_apply, Fin.sum_univ_succ] <;> first`. Consider the case `linear_combination (A i.succ 0 * b * A 0 j.succ) * hb'`.

Consider the case `linear_combination (-(A i.succ 0 * b * A 0 j.succ)) * hb'`. Use `⟨A', ?_⟩` and prove the remaining obligations. Unfold `Equi`. Conclude with `⟨P, Q, hPu, hQu, key⟩`.
-/
lemma clear {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (hu : IsUnit (A 0 0)) :
    ∃ A' : Matrix (Fin m) (Fin m) R, Equi A (bord A') := by
  obtain ⟨b, hb⟩ : ∃ b : R, A 0 0 * b = 1 := ⟨_, hu.mul_val_inv⟩
  have hb' : b * A 0 0 = 1 := by rw [mul_comm]; exact hb
  set P : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons 1 0)
    (fun i => Fin.cons (-(A i.succ 0 * b)) (fun j => if i = j then 1 else 0))) with hP
  set Pinv : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons 1 0)
    (fun i => Fin.cons (A i.succ 0 * b) (fun j => if i = j then 1 else 0))) with hPinv
  set Q : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons b (fun j => -(b * A 0 j.succ)))
    (fun i => Fin.cons 0 (fun j => if i = j then 1 else 0))) with hQ
  set Qinv : Matrix (Fin (m+1)) (Fin (m+1)) R := Matrix.of (Fin.cons (Fin.cons (A 0 0) (fun j => A 0 j.succ))
    (fun i => Fin.cons 0 (fun j => if i = j then 1 else 0))) with hQinv
  set A' : Matrix (Fin m) (Fin m) R := Matrix.of fun i j => A i.succ j.succ - A i.succ 0 * b * A 0 j.succ
    with hA'
  have hPP : P * Pinv = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [hP, hPinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  have hQQ : Q * Qinv = 1 := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [hQ, hQinv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, hb']
  have hPu : IsUnit P := by
    have h : P.det * Pinv.det = 1 := by rw [← Matrix.det_mul, hPP, Matrix.det_one]
    rw [Matrix.isUnit_iff_isUnit_det]
    first
    | exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
    | exact IsUnit.of_mul_eq_one _ h
  have hQu : IsUnit Q := by
    have h : Q.det * Qinv.det = 1 := by rw [← Matrix.det_mul, hQQ, Matrix.det_one]
    rw [Matrix.isUnit_iff_isUnit_det]
    first
    | exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
    | exact IsUnit.of_mul_eq_one _ h
  have key : P * A * Q = bord A' := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination hb | linear_combination (-1 : R) * hb
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination (-(A 0 j.succ)) * hb | linear_combination (A 0 j.succ) * hb
    · simp [hP, hQ, Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first | linear_combination (-(A i.succ 0 * b)) * hb' | linear_combination (A i.succ 0 * b) * hb'
    · simp [hP, hQ, hA', Matrix.mul_apply, Fin.sum_univ_succ] <;>
        first
        | linear_combination (A i.succ 0 * b * A 0 j.succ) * hb'
        | linear_combination (-(A i.succ 0 * b * A 0 j.succ)) * hb'
  refine ⟨A', ?_⟩
  unfold Equi
  exact ⟨P, Q, hPu, hQu, key⟩

end BorderedIndexCases

open Matrix

namespace BorderedIndexCases

variable {R : Type} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `A _`. Use `⟨A 0 0, ?_⟩` and prove the remaining obligations. Unfold `Equi`.

Use `⟨1, 1, isUnit_one, isUnit_one, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `A hA`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, IsUnit (A i j) := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Establish `h0 : A.map (IsLocalRing.residue R) = 0`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.zero_apply]`. Conclude with `(IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (hne i j))`. Rewrite `hA` using `[h0, Matrix.rank_zero]`.

Use linear arithmetic over natural numbers and integers. Establish `hu : IsUnit ((A.submatrix (Equiv.swap 0 i) (Equiv.swap 0 j)) 0 0)`. Simplify using `using hij`. Take `⟨A', e2⟩` from `clear _ hu`. Establish `e12 : Equi A (bord A')` using `(equi_submatrix A _ _).trans e2`.

Establish `hr : n ≤ (A'.map (IsLocalRing.residue R)).rank`. Establish `h1` using `e12.rank_map (IsLocalRing.residue R)`. Establish `h2` using `rank_bord_le (A'.map (IsLocalRing.residue R))`. Rewrite `h2` using `[← bord_map, h1]`. Use linear arithmetic over natural numbers and integers.

Take `⟨d, hd⟩` from `ih A' hr`. Unfold `Equi at hd`. Take `⟨P, Q, hP, hQ, hPQ⟩` from `hd`. Use `⟨d, e12.trans ?_⟩` and prove the remaining obligations. Unfold `Equi`.

Use `⟨bord P, bord Q, bord_isUnit hP, bord_isUnit hQ, ?_⟩` and prove the remaining obligations. Rewrite using `[bord_mul, bord_mul, hPQ, bord_diag]`.
-/
lemma main (n : ℕ) : ∀ (A : Matrix (Fin (n+1)) (Fin (n+1)) R),
    n ≤ (A.map (IsLocalRing.residue R)).rank →
    ∃ d : R, Equi A (diagonal fun i : Fin (n+1) => if (i : ℕ) = n then d else 1) := by
  induction n with
  | zero =>
    intro A _
    refine ⟨A 0 0, ?_⟩
    unfold Equi
    refine ⟨1, 1, isUnit_one, isUnit_one, ?_⟩
    ext i j
    fin_cases i; fin_cases j
    simp
  | succ n ih =>
    intro A hA
    obtain ⟨i, j, hij⟩ : ∃ i j, IsUnit (A i j) := by
      by_contra hne
      push_neg at hne
      have h0 : A.map (IsLocalRing.residue R) = 0 := by
        ext i j
        simp only [Matrix.map_apply, Matrix.zero_apply]
        exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr (hne i j))
      rw [h0, Matrix.rank_zero] at hA
      omega
    have hu : IsUnit ((A.submatrix (Equiv.swap 0 i) (Equiv.swap 0 j)) 0 0) := by
      simpa using hij
    obtain ⟨A', e2⟩ := clear _ hu
    have e12 : Equi A (bord A') := (equi_submatrix A _ _).trans e2
    have hr : n ≤ (A'.map (IsLocalRing.residue R)).rank := by
      have h1 := e12.rank_map (IsLocalRing.residue R)
      have h2 := rank_bord_le (A'.map (IsLocalRing.residue R))
      rw [← bord_map, h1] at h2
      omega
    obtain ⟨d, hd⟩ := ih A' hr
    unfold Equi at hd
    obtain ⟨P, Q, hP, hQ, hPQ⟩ := hd
    refine ⟨d, e12.trans ?_⟩
    unfold Equi
    refine ⟨bord P, bord Q, bord_isUnit hP, bord_isUnit hQ, ?_⟩
    rw [bord_mul, bord_mul, hPQ, bord_diag]

end BorderedIndexCases

end Formalism.GaloisIrreducibility
