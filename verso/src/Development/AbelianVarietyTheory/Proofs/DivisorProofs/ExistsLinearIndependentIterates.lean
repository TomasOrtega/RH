import Mathlib
import Formalism.PadicSubsetSums.StableGradedCounts.ExistsNeZeroAevalEqZero
open Polynomial Matrix

namespace GlobalTheory.ConjLocal

variable {R : Type} [CommRing R] {n : ℕ}

def iterMat (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (Y ^ (j : ℕ) *ᵥ v) i

def compMat (Q : R[X]) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if (j : ℕ) + 1 < n then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else -Q.coeff i

/- English proof (translation)
Take `⟨e, -, he⟩` from `Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (toLin' M) (by rw [charpoly_toLin']; exact hs) (toLin' M).charpoly dvd_rfl`. Use `⟨e, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Set `q : K[X]` to `∑ j : Fin n, monomial (j : ℕ) (c j)`.

Establish `ha : ∀ p : K[X], aeval (toLin' M) p = toLin' (aeval M p)` using `fun p => aeval_algHom_apply (toLinAlgEquiv' (R := K) (n := Fin n)) M p`. Establish `hq0 : aeval (toLin' M) q e = 0`. Rewrite using `[ha, toLin'_apply]`. Establish `haq : aeval M q = ∑ j : Fin n, c j • M ^ (j : ℕ)`. Simplify using `[q, map_sum, aeval_monomial, Algebra.smul_def]`.

Rewrite using `[haq, Matrix.sum_mulVec]`. Simplify `hc` using `[Matrix.smul_mulVec]`. Establish `hdvd` using `he q hq0`. Rewrite `hdvd` using `[charpoly_toLin']`. Establish `hdeg : q.degree < M.charpoly.degree`.

Rewrite using `[degree_eq_natDegree M.charpoly_monic.ne_zero, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Use `lt_of_le_of_lt (degree_sum_le _ _) ?_` and prove the remaining obligations. Use `(Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => ?_` and prove the remaining obligations. Conclude with `lt_of_le_of_lt (degree_monomial_le _ _) (by exact_mod_cast j.2)`. Establish `hq : q = 0` using `eq_zero_of_dvd_of_degree_lt hdvd hdeg`.

Introduce `j`. Use `congrArg (fun p : K[X] => p.coeff j) hq` as an intermediate fact. Simplify `this` using `[q, finset_sum_coeff, coeff_monomial, Fin.val_inj]`.
-/
theorem exists_linearIndependent_iterates {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (hs : M.charpoly.Separable) :
    ∃ v : Fin n → K, LinearIndependent K (fun j : Fin n => (M ^ (j : ℕ)) *ᵥ v) := by
  obtain ⟨e, -, he⟩ := Formalism.IrreducibleCountingLemmas.Z.exists_annihilator_eq (toLin' M) (by rw [charpoly_toLin']; exact hs)
    (toLin' M).charpoly dvd_rfl
  refine ⟨e, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let q : K[X] := ∑ j : Fin n, monomial (j : ℕ) (c j)
  have ha : ∀ p : K[X], aeval (toLin' M) p = toLin' (aeval M p) := fun p =>
    aeval_algHom_apply (toLinAlgEquiv' (R := K) (n := Fin n)) M p
  have hq0 : aeval (toLin' M) q e = 0 := by
    rw [ha, toLin'_apply]
    have haq : aeval M q = ∑ j : Fin n, c j • M ^ (j : ℕ) := by
      simp [q, map_sum, aeval_monomial, Algebra.smul_def]
    rw [haq, Matrix.sum_mulVec]
    simpa [Matrix.smul_mulVec] using hc
  have hdvd := he q hq0
  rw [charpoly_toLin'] at hdvd
  have hdeg : q.degree < M.charpoly.degree := by
    rw [degree_eq_natDegree M.charpoly_monic.ne_zero, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => ?_
    exact lt_of_le_of_lt (degree_monomial_le _ _) (by exact_mod_cast j.2)
  have hq : q = 0 := eq_zero_of_dvd_of_degree_lt hdvd hdeg
  intro j
  have := congrArg (fun p : K[X] => p.coeff j) hq
  simpa [q, finset_sum_coeff, coeff_monomial, Fin.val_inj] using this

end GlobalTheory.ConjLocal

namespace GlobalTheory.ConjLocal

variable {R : Type} [CommRing R] {n : ℕ}

/- English proof (translation)
Establish `h0` using `Matrix.aeval_self_charpoly Y`. Establish `hm` using `Y.charpoly_monic.as_sum`. Rewrite `hm` using `[charpoly_natDegree_eq_dim, Fintype.card_fin]`. Rewrite `h0` using `[hm]`. Simplify using `only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0`.

Use `congrArg (fun M => (M *ᵥ v) i) h0` as an intermediate fact. Simplify using `only [add_mulVec, sum_mulVec, Pi.add_apply, Finset.sum_apply, zero_mulVec, Pi.zero_apply] at this`. Rewrite using `[eq_neg_iff_add_eq_zero, ← this, ← Fin.sum_univ_eq_sum_range]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[← mulVec_mulVec, algebraMap_eq_diagonal, mulVec_diagonal]`. Both sides reduce to the same expression.
-/
theorem pow_dim_mulVec [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (i : Fin n) :
    (Y ^ n *ᵥ v) i = -∑ k : Fin n, Y.charpoly.coeff k * (Y ^ (k : ℕ) *ᵥ v) i := by
  have h0 := Matrix.aeval_self_charpoly Y
  have hm := Y.charpoly_monic.as_sum
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at hm
  rw [hm] at h0
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C] at h0
  have := congrArg (fun M => (M *ᵥ v) i) h0
  simp only [add_mulVec, sum_mulVec, Pi.add_apply, Finset.sum_apply, zero_mulVec, Pi.zero_apply] at this
  rw [eq_neg_iff_add_eq_zero, ← this, ← Fin.sum_univ_eq_sum_range]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mulVec_mulVec, algebraMap_eq_diagonal, mulVec_diagonal]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Establish `hl : (Y * iterMat Y v) i j = (Y ^ ((j : ℕ) + 1) *ᵥ v) i`. Rewrite using `[pow_succ', ← mulVec_mulVec]`. Both sides reduce to the same expression. Rewrite using `[hl, Matrix.mul_apply]`.

Simplify using `only [iterMat, compMat, Matrix.of_apply]`. Use `split_ifs with hj`. Rewrite using `[Finset.sum_eq_single ⟨(j : ℕ) + 1, hj⟩]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Rewrite using `[if_neg (fun h => hb (Fin.ext h)), mul_zero]`. Simplify using the standard rewrite rules. Establish `: (j : ℕ) + 1 = n` using `by omega`. Rewrite using `[this, pow_dim_mulVec, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_iterMat [Nontrivial R] (Y : Matrix (Fin n) (Fin n) R) (v : Fin n → R) :
    Y * iterMat Y v = iterMat Y v * compMat Y.charpoly := by
  ext i j
  have hl : (Y * iterMat Y v) i j = (Y ^ ((j : ℕ) + 1) *ᵥ v) i := by
    rw [pow_succ', ← mulVec_mulVec]; rfl
  rw [hl, Matrix.mul_apply]
  simp only [iterMat, compMat, Matrix.of_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨(j : ℕ) + 1, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg (fun h => hb (Fin.ext h)), mul_zero]
    · simp
  · have : (j : ℕ) + 1 = n := by omega
    rw [this, pow_dim_mulVec, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/- English proof (translation)
Set `f` to `IsLocalRing.residue R`. Establish `hs' : (Y.map f).charpoly.Separable` using `by rw [Matrix.charpoly_map]; exact hs.map`. Take `⟨w, hw⟩` from `exists_linearIndependent_iterates (Y.map f) hs'`. Use `choose v hv using fun i => IsLocalRing.residue_surjective (w i)`. Use `⟨v, ?_⟩` and prove the remaining obligations.

Establish `hmap : (iterMat Y v).map f = iterMat (Y.map f) w`. Use extensionality with `i j`. Simplify using `only [iterMat, Matrix.map_apply, Matrix.of_apply, ← Matrix.map_pow, RingHom.map_mulVec]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Conclude with `hv k`. Establish `hunit : IsUnit (iterMat (Y.map f) w)`. Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`. Use `hw using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`.

Use extensionality with `i`. Both sides reduce to the same expression. Apply `isUnit_of_map_unit f` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hmap]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 hunit`.
-/
theorem exists_isUnit_det_iterMat [IsLocalRing R] (Y : Matrix (Fin n) (Fin n) R) (hs : Y.charpoly.Separable) :
    ∃ v : Fin n → R, IsUnit (iterMat Y v).det := by
  let f := IsLocalRing.residue R
  have hs' : (Y.map f).charpoly.Separable := by rw [Matrix.charpoly_map]; exact hs.map
  obtain ⟨w, hw⟩ := exists_linearIndependent_iterates (Y.map f) hs'
  choose v hv using fun i => IsLocalRing.residue_surjective (w i)
  refine ⟨v, ?_⟩
  have hmap : (iterMat Y v).map f = iterMat (Y.map f) w := by
    ext i j
    simp only [iterMat, Matrix.map_apply, Matrix.of_apply, ← Matrix.map_pow, RingHom.map_mulVec]
    congr 1
    funext k
    exact hv k
  have hunit : IsUnit (iterMat (Y.map f) w) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    convert hw using 1
    funext j
    ext i
    rfl
  apply isUnit_of_map_unit f
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
  exact (Matrix.isUnit_iff_isUnit_det _).1 hunit

end GlobalTheory.ConjLocal
