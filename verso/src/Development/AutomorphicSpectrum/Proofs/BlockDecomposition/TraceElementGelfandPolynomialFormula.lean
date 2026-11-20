import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetAddOnesField
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GelfRec

open Polynomial Matrix

noncomputable def entrySum {n : ℕ} (E : Matrix (Fin n) (Fin n) ℂ[X]) (A : Matrix (Fin n) (Fin n) ℂ)
    (k : ℕ) : ℂ[X] :=
  ∑ a, ∑ b, (E * (A ^ k).map C) a b

/- English proof (translation)
Rewrite using `[adjugate_fin_succ_eq_det_submatrix]`. Establish `hs : ((X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + B.map C).submatrix b.succAbove a.succAbove = (X : ℂ[X]) • ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix b.succAbove a.succAbove).map C + (B.submatrix b.succAbove a.succAbove).map C`. Both sides reduce to the same expression. Rewrite using `[hs]`. Establish `h1` using `natDegree_det_X_add_C_le ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix b.succAbove a.succAbove) (B.submatrix b.succAbove a.succAbove)`.

Rewrite `h1` using `[Fintype.card_fin]`. Use `natDegree_mul_le.trans ?_` and prove the remaining obligations. Establish `h2 : ((-1 : ℂ[X]) ^ ((b : ℕ) + (a : ℕ))).natDegree = 0`. Apply the tactic sequence `rcases neg_one_pow_eq_or ℂ[X] ((b : ℕ) + (a : ℕ)) with h | h <;> simp [h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem natDegree_adjugate_le (m : ℕ) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (a b : Fin (m + 1)) :
    (adjugate ((X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + B.map C) a b).natDegree
      ≤ m := by
  rw [adjugate_fin_succ_eq_det_submatrix]
  have hs : ((X : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).map C + B.map C).submatrix
        b.succAbove a.succAbove =
      (X : ℂ[X]) • ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix b.succAbove a.succAbove).map C
        + (B.submatrix b.succAbove a.succAbove).map C := by
    rfl
  rw [hs]
  have h1 := natDegree_det_X_add_C_le
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).submatrix b.succAbove a.succAbove)
    (B.submatrix b.succAbove a.succAbove)
  rw [Fintype.card_fin] at h1
  refine natDegree_mul_le.trans ?_
  have h2 : ((-1 : ℂ[X]) ^ ((b : ℕ) + (a : ℕ))).natDegree = 0 := by
    rcases neg_one_pow_eq_or ℂ[X] ((b : ℕ) + (a : ℕ)) with h | h <;> simp [h]
  omega

/- English proof (translation)
Use `set M := x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C with hM`. Use `set E := adjugate M with hEdef`. Establish `hE : E * M = M.det • (1 : Matrix (Fin n) (Fin n) ℂ[X])` using `adjugate_mul M`. Establish `hp : (A ^ (k + 1)).map C = A.map C * (A ^ k).map C`. Rewrite using `[pow_succ']`.

Conclude with `Matrix.map_mul`. Establish `key : x • (E * (A ^ k).map C) + E * (A ^ (k + 1)).map C = M.det • (A ^ k).map C`. Establish `h3 : (E * M) * (A ^ k).map C = M.det • (A ^ k).map C`. Rewrite using `[hE, Matrix.smul_mul, Matrix.one_mul]`. Rewrite using `[← h3, hp, hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]`.

Establish `h4` using `congrArg (fun B : Matrix (Fin n) (Fin n) ℂ[X] => ∑ a, ∑ b, B a b) key`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, Matrix.map_apply] at h4`. Simplify using `only [entrySum, map_sum]`. Conclude with `h4`.
-/
theorem entrySum_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ[X]) (k : ℕ) :
    x * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A k
        + entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A (k + 1)
      = det (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C) * C (∑ a, ∑ b, (A ^ k) a b) := by
  set M := x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C with hM
  set E := adjugate M with hEdef
  have hE : E * M = M.det • (1 : Matrix (Fin n) (Fin n) ℂ[X]) := adjugate_mul M
  have hp : (A ^ (k + 1)).map C = A.map C * (A ^ k).map C := by
    rw [pow_succ']
    exact Matrix.map_mul
  have key : x • (E * (A ^ k).map C) + E * (A ^ (k + 1)).map C = M.det • (A ^ k).map C := by
    have h3 : (E * M) * (A ^ k).map C = M.det • (A ^ k).map C := by
      rw [hE, Matrix.smul_mul, Matrix.one_mul]
    rw [← h3, hp, hM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_assoc]
  have h4 := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ[X] => ∑ a, ∑ b, B a b) key
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Matrix.map_apply] at h4
  simp only [entrySum, map_sum]
  exact h4

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Establish `hs : ∑ k ∈ Finset.range (N + 1), C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N + 1 - k) = x * ∑ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k) + C ((-1 : ℂ) ^ N * ∑ a, ∑ b, (A ^ N) a b) * x`. Establish `h1 : ∀ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N + 1 - k) = x * (C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k))`.

Introduce `k hk`. Establish `hk' : k ≤ N` using `(Finset.mem_range.1 hk).le`. Rewrite using `[Nat.succ_sub hk', pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_range_succ, Finset.sum_congr rfl h1, ← Finset.mul_sum]`.

Simplify using the standard rewrite rules. Establish `hstep` using `entrySum_step A x N`. Rewrite using `[hs]`. Simplify using `only [map_mul, map_pow, map_neg, map_one] at ih hstep ⊢`. Take the linear combination `x * ih + (-1) ^ N * x * hstep`.
-/
theorem newton_closed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ[X]) (N : ℕ) :
    x ^ (N + 1) * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A 0
        - det (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)
          * ∑ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)
      = (-1) ^ N * x * entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C)) A N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : ∑ k ∈ Finset.range (N + 1), C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N + 1 - k)
        = x * ∑ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)
          + C ((-1 : ℂ) ^ N * ∑ a, ∑ b, (A ^ N) a b) * x := by
      have h1 : ∀ k ∈ Finset.range N, C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N + 1 - k)
          = x * (C ((-1 : ℂ) ^ k * ∑ a, ∑ b, (A ^ k) a b) * x ^ (N - k)) := by
        intro k hk
        have hk' : k ≤ N := (Finset.mem_range.1 hk).le
        rw [Nat.succ_sub hk', pow_succ]
        ring
      rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, ← Finset.mul_sum]
      simp
    have hstep := entrySum_step A x N
    rw [hs]
    simp only [map_mul, map_pow, map_neg, map_one] at ih hstep ⊢
    linear_combination x * ih + (-1) ^ N * x * hstep

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[Matrix.one_apply_ne h]`.
-/
theorem shift_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    (X - C c : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + A.map C
      = (X : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ).map C + (A - c • (1 : Matrix (Fin n) (Fin n) ℂ)).map C := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h
    simp
    ring
  · simp [Matrix.one_apply_ne h]

/- English proof (translation)
Rewrite using `[shift_eq]`. Use `natDegree_sum_le_of_forall_le _ _ fun a _ => ?_` and prove the remaining obligations. Use `natDegree_sum_le_of_forall_le _ _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `natDegree_sum_le_of_forall_le _ _ fun d _ => ?_` and prove the remaining obligations.

Conclude with `(natDegree_mul_C_le _ _).trans (natDegree_adjugate_le m _ a d)`.
-/
theorem natDegree_entrySum_le (m : ℕ) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c : ℂ) (k : ℕ) :
    (entrySum (adjugate ((X - C c : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X]) + A.map C))
      A k).natDegree ≤ m := by
  rw [shift_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  rw [Matrix.mul_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun d _ => ?_
  exact (natDegree_mul_C_le _ _).trans (natDegree_adjugate_le m _ a d)

/- English proof (translation)
Establish `hM : x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C = (compRingHom x).mapMatrix ((X : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C)`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Matrix.one_apply_ne h]`. Establish `h0` using `congrArg (compRingHom x) (GlobalTheory.CompanionTheory.AdjSum.adj_sum n l)`. Simplify using `only [map_sum, map_sub, map_prod, map_add, map_one, coe_compRingHom_apply, X_comp, C_comp] at h0`. Rewrite using `[← h0, hM, ← RingHom.map_adjugate]`. Simplify using `[entrySum]`.
-/
theorem entrySum_zero {n : ℕ} (l : Fin n → ℂ) (x : ℂ[X]) :
    entrySum (adjugate (x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C))
        (Formalism.REAL.Amat l) 0
      = ∏ s, (x + C (l s) + 1) - ∏ s, (x + C (l s)) := by
  have hM : x • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C
      = (compRingHom x).mapMatrix
        ((X : ℂ[X]) • (1 : Matrix (Fin n) (Fin n) ℂ[X]) + (Formalism.REAL.Amat l).map C) := by
    refine Matrix.ext fun i j => ?_
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have h0 := congrArg (compRingHom x) (GlobalTheory.CompanionTheory.AdjSum.adj_sum n l)
  simp only [map_sum, map_sub, map_prod, map_add, map_one, coe_compRingHom_apply, X_comp, C_comp] at h0
  rw [← h0, hM, ← RingHom.map_adjugate]
  simp [entrySum]

/- English proof (translation)
Rewrite using `[det_of_isUpperTriangular]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `hc : C (χ s - (m : ℂ) / 2) = C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) - C (m : ℂ)`. Rewrite using `[← C_sub]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.map_apply, Formalism.REAL.Amat, Matrix.of_apply, if_true, smul_eq_mul, mul_one]`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Establish `hne : i ≠ j` using `ne_of_gt hij'`. Simplify using `[Formalism.REAL.Amat, Matrix.one_apply_ne hne, hne, not_lt.2 hij'.le]`.
-/
theorem det_shift (m : ℕ) (χ : Fin (m + 1) → ℂ) :
    det ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
        + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C)
      = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := by
  rw [det_of_isUpperTriangular]
  · refine Finset.prod_congr rfl fun s _ => ?_
    have hc : C (χ s - (m : ℂ) / 2) = C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) - C (m : ℂ) := by
      rw [← C_sub]
      congr 1
      push_cast
      ring
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.map_apply,
      Formalism.REAL.Amat, Matrix.of_apply, if_true, smul_eq_mul, mul_one]
    rw [hc]
    ring
  · intro i j hij
    have hij' : j < i := hij
    have hne : i ≠ j := ne_of_gt hij'
    simp [Formalism.REAL.Amat, Matrix.one_apply_ne hne, hne, not_lt.2 hij'.le]

/- English proof (translation)
Establish `hm : (∏ s, (X + C (c s))).Monic` using `monic_prod_of_monic _ _ fun s _ => monic_X_add_C _`. Establish `hd : (∏ s, (X + C (c s))).natDegree = m + 1`. Rewrite using `[natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]`. Simplify using the standard rewrite rules. Establish `h1` using `hm.coeff_natDegree`.

Rewrite `h1` using `[hd]`. Then use the resulting hypothesis.
-/
theorem prod_monic (m : ℕ) (c : Fin (m + 1) → ℂ) :
    (∏ s, (X + C (c s))).coeff (m + 1) = 1 := by
  have hm : (∏ s, (X + C (c s))).Monic := monic_prod_of_monic _ _ fun s _ => monic_X_add_C _
  have hd : (∏ s, (X + C (c s))).natDegree = m + 1 := by
    rw [natDegree_prod_of_monic _ _ fun s _ => monic_X_add_C _]
    simp
  have h1 := hm.coeff_natDegree
  rwa [hd] at h1

/- English proof (translation)
Introduce `m χ N`. Establish `hdet` using `det_shift m χ`. Establish `hz` using `entrySum_zero (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) (X - C (m : ℂ))`. Establish `hc` using `newton_closed (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (X - C (m : ℂ)) N`. Establish `hs` using `entrySum_step (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (X - C (m : ℂ)) N`.

Establish `hdeg` using `natDegree_entrySum_le m (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (m : ℂ) (N + 1)`. Establish `hterm : ∀ s : Fin (m + 1), (X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) = X + C (χ s - (m : ℂ) / 2)`. Introduce `s`. Establish `hc : C (χ s - (m : ℂ) / 2) = C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) - C (m : ℂ)`. Rewrite using `[← C_sub]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hQ : (∏ s, (X + C (χ s - (m : ℂ) / 2))).comp (X + 1) = ∏ s, ((X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) + 1)`. Rewrite using `[prod_comp]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[hterm s]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish `hP : ∏ s, ((X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2)) = ∏ s, (X + C (χ s - (m : ℂ) / 2))` using `Finset.prod_congr rfl fun s _ => hterm s`. Rewrite `hz` using `[hP, ← hQ]`. Rewrite `hc` using `[hz, hdet]`. Rewrite `hs` using `[hdet]`.

Establish `hsq : (-1 : ℂ[X]) ^ N * (-1) ^ N = 1`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `_ = ∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) ^ N) a b`. Establish `hgoal : (-1 : ℂ[X]) ^ N * ((X - C (m : ℂ)) ^ (N + 1) * ((∏ s, (X + C (χ s - (m : ℂ) / 2))).comp (X + 1) - (∏ s, (X + C (χ s - (m : ℂ) / 2)))) - (∏ s, (X + C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (X - C (m : ℂ)) ^ (N - k)) = C …`.

Establish `hc'` using `hc`. Simplify using `only [GlobalTheory.Dec.gelfVal] at *`. Take the linear combination `(-1 : ℂ[X]) ^ N * hc' + hs + (X - C (m : ℂ)) * entrySum (adjugate ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X]) + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C)) (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) …`. Rewrite using `[hgoal, coeff_sub, coeff_C_mul, prod_monic m (fun s => χ s - (m : ℂ) / 2), coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hdeg)]`. Simplify using the standard rewrite rules.
-/
theorem gelfVal_newton : ∀ (m : ℕ) (χ : Fin (m + 1) → ℂ) (N : ℕ), ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))).comp (Polynomial.X + 1) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2)))) - (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) = GlobalTheory.Dec.gelfVal χ N := by
  intro m χ N
  have hdet := det_shift m χ
  have hz := entrySum_zero (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) (X - C (m : ℂ))
  have hc := newton_closed (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (X - C (m : ℂ)) N
  have hs := entrySum_step (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (X - C (m : ℂ)) N
  have hdeg := natDegree_entrySum_le m (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (m : ℂ) (N + 1)
  have hterm : ∀ s : Fin (m + 1), (X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2)
      = X + C (χ s - (m : ℂ) / 2) := by
    intro s
    have hc : C (χ s - (m : ℂ) / 2) = C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) - C (m : ℂ) := by
      rw [← C_sub]
      congr 1
      push_cast
      ring
    rw [hc]
    ring
  have hQ : (∏ s, (X + C (χ s - (m : ℂ) / 2))).comp (X + 1)
      = ∏ s, ((X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2) + 1) := by
    rw [prod_comp]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hterm s]
    simp
    ring
  have hP : ∏ s, ((X - C (m : ℂ) : ℂ[X]) + C (χ s + (((m + 1 : ℕ) : ℂ) - 1) / 2))
      = ∏ s, (X + C (χ s - (m : ℂ) / 2)) := Finset.prod_congr rfl fun s _ => hterm s
  rw [hP, ← hQ] at hz
  rw [hz, hdet] at hc
  rw [hdet] at hs
  have hsq : (-1 : ℂ[X]) ^ N * (-1) ^ N = 1 := by
    rw [← mul_pow]
    simp
  change _ = ∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) ^ N) a b
  have hgoal : (-1 : ℂ[X]) ^ N * ((X - C (m : ℂ)) ^ (N + 1) * ((∏ s, (X + C (χ s - (m : ℂ) / 2))).comp (X + 1) - (∏ s, (X + C (χ s - (m : ℂ) / 2)))) - (∏ s, (X + C (χ s - (m : ℂ) / 2))) * ∑ k ∈ Finset.range N, C ((-1) ^ k * GlobalTheory.Dec.gelfVal χ k) * (X - C (m : ℂ)) ^ (N - k))
      = C (∑ a, ∑ b, (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2) ^ N) a b) * (∏ s, (X + C (χ s - (m : ℂ) / 2)))
        - entrySum (adjugate ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
            + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C))
          (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) (N + 1) := by
    have hc' := hc
    simp only [GlobalTheory.Dec.gelfVal] at *
    linear_combination (-1 : ℂ[X]) ^ N * hc' + hs + (X - C (m : ℂ)) * entrySum (adjugate ((X - C (m : ℂ) : ℂ[X]) • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X])
            + (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)).map C))
          (Formalism.REAL.Amat (fun c => χ c + (((m + 1 : ℕ) : ℂ) - 1) / 2)) N * hsq
  rw [hgoal, coeff_sub, coeff_C_mul, prod_monic m (fun s => χ s - (m : ℂ) / 2),
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le hdeg)]
  simp

end GlobalTheory.CompanionTheory.GelfRec
