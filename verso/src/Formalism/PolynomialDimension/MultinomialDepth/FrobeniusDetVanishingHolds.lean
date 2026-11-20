import Formalism.PolynomialDimension.FrameSum

noncomputable section

open scoped BigOperators
open Finset Matrix

namespace Formalism.CountingSumsFrames

/- English proof (translation)
Introduce `R _ r T s a`. Establish `h : (T.adjugate *ᵥ (T *ᵥ s)) a = (T.det • s) a`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.one_apply]`. Rewrite `h` using `[Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[← h]`. Generalize the expression as in `T *ᵥ s = v`. Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl fun l _ => mul_comm _ _`.
-/
theorem detMulEqSumAdjugate_holds : DetMulEqSumAdjugate := by
  intro R _ r T s a
  have h : (T.adjugate *ᵥ (T *ᵥ s)) a = (T.det • s) a := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [Pi.smul_apply, smul_eq_mul] at h
  rw [← h]
  generalize T *ᵥ s = v
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/- English proof (translation)
Apply the tactic sequence `cases i using Fin.cases <;> simp [borderedMatrix]`.
-/
lemma borderedMatrix_castSucc {R : Type} [CommRing R] (r : ℕ) (ts : Fin r → R) (u : R)
    (T : Matrix (Fin r) (Fin r) R) (b : Fin r → R) (i : Fin (r + 1)) (j : Fin r) :
    borderedMatrix r ts u T b i (Fin.castSucc j) = borderedMatrix r ts 0 T 0 i (Fin.castSucc j) := by
  cases i using Fin.cases <;> simp [borderedMatrix]

/- English proof (translation)
Introduce `R _ r ts T`. Use `⟨fun l => (-1) ^ ((l.succ : ℕ) + r) * ((borderedMatrix r ts 0 T 0).submatrix (Fin.succ l).succAbove Fin.castSucc).det, fun u b => ?_⟩` and prove the remaining obligations. Establish `hsub : ∀ i : Fin (r + 1), (borderedMatrix r ts u T b).submatrix i.succAbove (Fin.last r).succAbove = (borderedMatrix r ts 0 T 0).submatrix i.succAbove Fin.castSucc`. Introduce `i`. Use extensionality with `x y`.

Simplify using `only [Matrix.submatrix_apply, Fin.succAbove_last]`. Conclude with `borderedMatrix_castSucc r ts u T b _ y`. Establish `h0 : (borderedMatrix r ts 0 T 0).submatrix (Fin.succAbove 0) Fin.castSucc = T`. Use extensionality with `x y`. Simplify using `[borderedMatrix]`.

Establish `hl0 : borderedMatrix r ts u T b 0 (Fin.last r) = u` using `by simp [borderedMatrix]`. Establish `hls : ∀ l : Fin r, borderedMatrix r ts u T b l.succ (Fin.last r) = b l`. Introduce `l`. Simplify using `[borderedMatrix]`. Rewrite using `[Matrix.det_succ_column _ (Fin.last r), Fin.sum_univ_succ]`.

Simplify using `only [hsub, h0, hl0, hls, Fin.val_zero, Fin.val_last, zero_add]`. Use `congr 1`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem borderedDetLinear_holds : BorderedDetLinear := by
  intro R _ r ts T
  refine ⟨fun l => (-1) ^ ((l.succ : ℕ) + r) *
    ((borderedMatrix r ts 0 T 0).submatrix (Fin.succ l).succAbove Fin.castSucc).det, fun u b => ?_⟩
  have hsub : ∀ i : Fin (r + 1), (borderedMatrix r ts u T b).submatrix i.succAbove (Fin.last r).succAbove =
      (borderedMatrix r ts 0 T 0).submatrix i.succAbove Fin.castSucc := by
    intro i
    ext x y
    simp only [Matrix.submatrix_apply, Fin.succAbove_last]
    exact borderedMatrix_castSucc r ts u T b _ y
  have h0 : (borderedMatrix r ts 0 T 0).submatrix (Fin.succAbove 0) Fin.castSucc = T := by
    ext x y
    simp [borderedMatrix]
  have hl0 : borderedMatrix r ts u T b 0 (Fin.last r) = u := by simp [borderedMatrix]
  have hls : ∀ l : Fin r, borderedMatrix r ts u T b l.succ (Fin.last r) = b l := by
    intro l
    simp [borderedMatrix]
  rw [Matrix.det_succ_column _ (Fin.last r), Fin.sum_univ_succ]
  simp only [hsub, h0, hl0, hls, Fin.val_zero, Fin.val_last, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Use `haveI : ExpChar F p := ExpChar.prime (Fact.out)`. Simplify using `only [Matrix.vecMul, dotProduct, Matrix.map_apply]`. Rewrite using `[sum_pow_char_pow]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_of_le ha]`.
-/
lemma frob_row {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p] {k : ℕ}
    (h : Matrix (Fin k) (Fin k) F) (a s : ℕ) (ha : a ≤ s) (t : Fin k → F) (c : Fin k) :
    ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) =
      ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) c := by
  haveI : ExpChar F p := ExpChar.prime (Fact.out)
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply]
  rw [sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_add, Nat.add_sub_of_le ha]

/- English proof (translation)
Introduce `p _ F _ _ r k h hdet s`. Establish `hp : 0 < p` using `(Fact.out : p.Prime).pos`. Use `⟨fun A t cols hA ht => ?_, fun a t v ha ht hv => ?_⟩` and prove the remaining obligations. Establish `hM : (Matrix.of fun l c => ((t l ᵥ* h.map (fun x => x ^ p ^ A l)) (cols c)) ^ p ^ (s - A l)) = (Matrix.of fun (l : Fin (r + 1)) (i : {i : Fin k // i.val < r}) => t l i.1 ^ p ^ (s - A l)) * (Matrix.of fun (i : {i : Fin k // i.val < r}) (c : Fin (r + 1)) => (h.map (fun x => x ^ p ^ …`. Use extensionality with `l c`.

Rewrite using `[Matrix.of_apply, frob_row h (A l) s (hA l) (t l) (cols c), Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply, Matrix.vecMul, dotProduct]`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i.val < r)]`. Establish `hz : ∑ i : {i : Fin k // ¬ i.val < r}, t l i.1 ^ p ^ (s - A l) * (h.map (fun x => x ^ p ^ s)) i.1 (cols c) = 0`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[ht l i.1 (not_lt.mp i.2), zero_pow (pow_ne_zero _ hp.ne'), zero_mul]`. Rewrite using `[hz, add_zero]`. Rewrite using `[hM]`. Assume the negation of the conclusion as `hne`. Establish `hu` using `Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))`.

Establish `hcard : Fintype.card {i : Fin k // i.val < r} ≤ r`. Use `Fintype.card_le_of_injective (fun i : {i : Fin k // i.val < r} => (⟨i.1.val, i.2⟩ : Fin r)) (fun x y hxy => by` as an intermediate fact. Simplify using `only [Fin.mk.injEq] at hxy`. Conclude with `Subtype.ext (Fin.ext hxy))`. Simplify using `using this`.

Establish `h2` using `(Matrix.rank_mul_le_left (Matrix.of fun (l : Fin (r + 1)) (i : {i : Fin k // i.val < r}) => t l i.1 ^ p ^ (s - A l)) (Matrix.of fun (i : {i : Fin k // i.val < r}) (c : Fin (r + 1)) => (h.map (fun x => x ^ p ^ s)) i.1 (cols c))).trans ((Matrix.rank_le_card_width _).trans hcard)`. Rewrite `h2` using `[hu, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `hH : IsUnit (h.map (fun x => x ^ p ^ s)).det` using `by haveI : ExpChar F p := ExpChar.prime (Fact.out)`. Establish `e : h.map (fun x => x ^ p ^ s) = (iterateFrobenius F p s).mapMatrix h`.

Use extensionality with `i j`. Simplify using `[iterateFrobenius_def]`. Rewrite using `[e, ← RingHom.map_det]`. Conclude with `hdet.map _`. Establish `e1 : ∀ c, ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) = ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) c` using `fun c => frob_row h a s ha t c`.

Simplify using `only [e1]`. Express the relevant statement in the definitionally equal form `((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) ⬝ᵥ (v ᵥ* (h.map (fun x => x ^ p ^ s))⁻¹ᵀ) = 0`. Rewrite using `[Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `show t i ^ p ^ (s - a) * v i = 0`.

Distinguish the cases in `hi : i.val < r`. Rewrite using `[hv i hi, mul_zero]`. Rewrite using `[ht i (not_lt.mp hi), zero_pow (pow_ne_zero _ hp.ne'), zero_mul]`.
-/
theorem frobeniusDetVanishing_holds : KeyVanish := by
  intro p _ F _ _ r k h hdet s
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine ⟨fun A t cols hA ht => ?_, fun a t v ha ht hv => ?_⟩
  · have hM : (Matrix.of fun l c =>
        ((t l ᵥ* h.map (fun x => x ^ p ^ A l)) (cols c)) ^ p ^ (s - A l)) =
        (Matrix.of fun (l : Fin (r + 1)) (i : {i : Fin k // i.val < r}) =>
          t l i.1 ^ p ^ (s - A l)) *
        (Matrix.of fun (i : {i : Fin k // i.val < r}) (c : Fin (r + 1)) =>
          (h.map (fun x => x ^ p ^ s)) i.1 (cols c)) := by
      ext l c
      rw [Matrix.of_apply, frob_row h (A l) s (hA l) (t l) (cols c), Matrix.mul_apply]
      simp only [Matrix.of_apply, Matrix.vecMul, dotProduct]
      rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i.val < r)]
      have hz : ∑ i : {i : Fin k // ¬ i.val < r},
          t l i.1 ^ p ^ (s - A l) * (h.map (fun x => x ^ p ^ s)) i.1 (cols c) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [ht l i.1 (not_lt.mp i.2), zero_pow (pow_ne_zero _ hp.ne'), zero_mul]
      rw [hz, add_zero]
    rw [hM]
    by_contra hne
    have hu := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne))
    have hcard : Fintype.card {i : Fin k // i.val < r} ≤ r := by
      have := Fintype.card_le_of_injective (fun i : {i : Fin k // i.val < r} => (⟨i.1.val, i.2⟩ : Fin r))
        (fun x y hxy => by
          simp only [Fin.mk.injEq] at hxy
          exact Subtype.ext (Fin.ext hxy))
      simpa using this
    have h2 := (Matrix.rank_mul_le_left
      (Matrix.of fun (l : Fin (r + 1)) (i : {i : Fin k // i.val < r}) => t l i.1 ^ p ^ (s - A l))
      (Matrix.of fun (i : {i : Fin k // i.val < r}) (c : Fin (r + 1)) =>
        (h.map (fun x => x ^ p ^ s)) i.1 (cols c))).trans ((Matrix.rank_le_card_width _).trans hcard)
    rw [hu, Fintype.card_fin] at h2
    omega
  · have hH : IsUnit (h.map (fun x => x ^ p ^ s)).det := by
      haveI : ExpChar F p := ExpChar.prime (Fact.out)
      have e : h.map (fun x => x ^ p ^ s) = (iterateFrobenius F p s).mapMatrix h := by
        ext i j
        simp [iterateFrobenius_def]
      rw [e, ← RingHom.map_det]
      exact hdet.map _
    have e1 : ∀ c, ((t ᵥ* h.map (fun x => x ^ p ^ a)) c) ^ p ^ (s - a) =
        ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) c :=
      fun c => frob_row h a s ha t c
    simp only [e1]
    change ((fun i => t i ^ p ^ (s - a)) ᵥ* h.map (fun x => x ^ p ^ s)) ⬝ᵥ
      (v ᵥ* (h.map (fun x => x ^ p ^ s))⁻¹ᵀ) = 0
    rw [Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec]
    refine Finset.sum_eq_zero fun i _ => ?_
    show t i ^ p ^ (s - a) * v i = 0
    by_cases hi : i.val < r
    · rw [hv i hi, mul_zero]
    · rw [ht i (not_lt.mp hi), zero_pow (pow_ne_zero _ hp.ne'), zero_mul]

end Formalism.CountingSumsFrames
