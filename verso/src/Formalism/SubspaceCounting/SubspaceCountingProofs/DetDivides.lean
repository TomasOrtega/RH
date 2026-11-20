import Formalism.SubspaceCounting.StatementW

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {L : Type} [Field L] {r : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
lemma lastIdx_iff (hr : 0 < r) (a : Fin r) : a.val + 1 = r ↔ a = ⟨r - 1, by omega⟩ := by
  constructor
  · intro h; ext; simp; omega
  · intro h; subst h; simp; omega

/- English proof (translation)
Establish `: (fun a : Fin r => if a.val + 1 = r then u else 1) = fun a => if (⟨r - 1, by omega⟩ : Fin r) = a then u else 1`. Use function extensionality and compare the values at `a`. Simplify using `only [lastIdx_iff hr, eq_comm]`. Rewrite using `[this, Finset.prod_ite_eq]`. Simplify using the standard rewrite rules.
-/
lemma prod_lastX (hr : 0 < r) {R : Type} [CommRing R] (u : R) :
    (∏ a : Fin r, if a.val + 1 = r then u else 1) = u := by
  have : (fun a : Fin r => if a.val + 1 = r then u else 1) =
      fun a => if (⟨r - 1, by omega⟩ : Fin r) = a then u else 1 := by
    funext a; simp only [lastIdx_iff hr, eq_comm]
  rw [this, Finset.prod_ite_eq]; simp

/- English proof (translation)
Unfold `msMat`. Rewrite using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_lastX hr]`. Establish `h1 : (g.1.map C).det * (((g⁻¹ : GL (Fin r) L)).1.map C).det = 1`. Rewrite using `[← Matrix.det_mul, ← Matrix.map_mul]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma det_msMat (hr : 0 < r) (g : GL (Fin r) L) : (msMat g).det = X := by
  unfold msMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_lastX hr]
  have h1 : (g.1.map C).det * (((g⁻¹ : GL (Fin r) L)).1.map C).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul]
    simp
  calc (g.1.map C).det * X * (((g⁻¹ : GL (Fin r) L)).1.map C).det
      = ((g.1.map C).det * (((g⁻¹ : GL (Fin r) L)).1.map C).det) * X := by ring
    _ = X := by rw [h1, one_mul]

def nMat (g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L[X] :=
  (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C)

/- English proof (translation)
Unfold `msMat nMat`. Establish `hgi : ((g⁻¹ : GL (Fin r) L).1.map C) * (g.1.map C) = 1`. Rewrite using `[← Matrix.map_mul]`. Simplify using the standard rewrite rules. Establish `hgg : (g.1.map C) * ((g⁻¹ : GL (Fin r) L).1.map C) = 1`.

Rewrite using `[← Matrix.map_mul]`. Simplify using the standard rewrite rules. Establish `hdd : Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X])`. Rewrite using `[Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]`. Apply the tactic sequence `congr 1; funext a; split_ifs <;> simp`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hgi, Matrix.mul_one, Matrix.mul_assoc (g.1.map C), hdd]`. Use `_ = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by`. Rewrite using `[Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hgg]`.
-/
lemma msMat_mul_nMat (g : GL (Fin r) L) : msMat g * nMat g = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
  unfold msMat nMat
  have hgi : ((g⁻¹ : GL (Fin r) L).1.map C) * (g.1.map C) = 1 := by
    rw [← Matrix.map_mul]; simp
  have hgg : (g.1.map C) * ((g⁻¹ : GL (Fin r) L).1.map C) = 1 := by
    rw [← Matrix.map_mul]; simp
  have hdd : Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1; funext a; split_ifs <;> simp
  calc (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
        ((g⁻¹ : GL (Fin r) L).1.map C) * ((g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C))
      = (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
        (((g⁻¹ : GL (Fin r) L).1.map C) * (g.1.map C)) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C) := by simp only [Matrix.mul_assoc]
    _ = (g.1.map C) * ((X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X])) * ((g⁻¹ : GL (Fin r) L).1.map C) := by
        rw [hgi, Matrix.mul_one, Matrix.mul_assoc (g.1.map C), hdd]
    _ = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hgg]

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma msDualMat_eq (g : GL (Fin r) L) : msDualMat g = (nMat g).transpose := rfl

/- English proof (translation)
Rewrite using `[msDualMat_eq, ← Matrix.transpose_mul, msMat_mul_nMat]`. Simplify using the standard rewrite rules.
-/
lemma msDualMat_mul_msMat_transpose (g : GL (Fin r) L) :
    msDualMat g * (msMat g).transpose = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
  rw [msDualMat_eq, ← Matrix.transpose_mul, msMat_mul_nMat]; simp

/- English proof (translation)
Unfold `msMat`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.diagonal_map (by simp)]`. Use `congr 2`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Apply the tactic sequence `congr 1; funext a; split_ifs <;> simp`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
lemma msMat_eval0 (g : GL (Fin r) L) :
    (msMat g).map (Polynomial.evalRingHom 0) =
      g.1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) * (g⁻¹ : GL (Fin r) L).1 := by
  unfold msMat
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.diagonal_map (by simp)]
  congr 2
  · ext i j; simp
  · congr 1; funext a; split_ifs <;> simp
  · ext i j; simp

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

open Classical in

def ptA {L : Type} [Field L] (A : Fin r → ι) (g : GL (Fin r) L) (x : ι × Fin r → L) : ι × Fin r → L[X] :=
  fun p => if p.1 ∈ Set.range A then ∑ b, msMat g p.2 b * C (x (p.1, b)) else C (x p)

def Red (A : Fin r → ι) (G : MvPolynomial (ι × Fin r) K) (n : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [Algebra K L] (g : GL (Fin r) L) (x : ι × Fin r → L),
    MvPolynomial.aeval x (detLetters (K := K) A) ≠ 0 →
      (X : L[X]) ^ n ∣ MvPolynomial.aeval (ptA A g x) G

/- English proof (translation)
Unfold `detLetters`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `l a`. Simplify using the standard rewrite rules.
-/
lemma aeval_detLetters {B : Type} [CommRing B] [Algebra K B] (A : Fin r → ι) (y : ι × Fin r → B) :
    MvPolynomial.aeval y (detLetters (K := K) A) = (Matrix.of fun l a => y (A l, a)).det := by
  unfold detLetters
  rw [AlgHom.map_det]; congr 1; ext l a; simp

/- English proof (translation)
Rewrite using `[aeval_detLetters, aeval_detLetters]`. Establish `: (Matrix.of fun l a => ptA A g x (A l, a)) = ((Matrix.of fun l b => x (A l, b)).map C) * (msMat g).transpose`. Use extensionality with `l a`. Simplify using `[ptA, Matrix.mul_apply, mul_comm]`. Rewrite using `[this, Matrix.det_mul, Matrix.det_transpose, det_msMat hr, RingHom.map_det]`.

Both sides reduce to the same expression.
-/
lemma aeval_ptA_det (hr : 0 < r) {L : Type} [Field L] [Algebra K L] (A : Fin r → ι) (g : GL (Fin r) L)
    (x : ι × Fin r → L) :
    MvPolynomial.aeval (ptA A g x) (detLetters (K := K) A) =
      C (MvPolynomial.aeval x (detLetters (K := K) A)) * X := by
  rw [aeval_detLetters, aeval_detLetters]
  have : (Matrix.of fun l a => ptA A g x (A l, a)) =
      ((Matrix.of fun l b => x (A l, b)).map C) * (msMat g).transpose := by
    ext l a
    simp [ptA, Matrix.mul_apply, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_transpose, det_msMat hr, RingHom.map_det]
  rfl

/- English proof (translation)
Introduce `L _ _ g x hx`. Establish `h1` using `h L g x hx`. Rewrite `h1` using `[map_mul, aeval_ptA_det hr, pow_succ, mul_comm (C _) X, mul_assoc, mul_comm (X ^ n) X]`. Establish `h2` using `(mul_dvd_mul_iff_left (X_ne_zero : (X : L[X]) ≠ 0)).mp h1`. Conclude with `(IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hx))).mp h2`.
-/
lemma red_of_mul (hr : 0 < r) (A : Fin r → ι) (G' : MvPolynomial (ι × Fin r) K) (n : ℕ)
    (h : Red A (detLetters (K := K) A * G') (n + 1)) : Red A G' n := by
  intro L _ _ g x hx
  have h1 := h L g x hx
  rw [map_mul, aeval_ptA_det hr, pow_succ, mul_comm (C _) X, mul_assoc, mul_comm (X ^ n) X] at h1
  have h2 := (mul_dvd_mul_iff_left (X_ne_zero : (X : L[X]) ≠ 0)).mp h1
  exact (IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hx))).mp h2

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

/- English proof (translation)
Use `conv_lhs => rw [φ.as_sum]`. Use `conv_rhs => rw [φ.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]`.

Establish `hw : Finsupp.weight w m = n` using `hφ (MvPolynomial.mem_support_iff.mp hm)`. Establish `: (m.prod fun p k => (t ^ w p * z p) ^ k) = t ^ n * m.prod fun p k => z p ^ k`. Simplify using `only [mul_pow, Finsupp.prod_mul]`. Use `congr 1`. Rewrite using `[← hw, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]`.

Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, smul_eq_mul, mul_comm]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma aeval_weighted_scale {σ : Type} {B : Type} [CommSemiring B] [Algebra K B] (w : σ → ℕ)
    {φ : MvPolynomial σ K} {n : ℕ} (hφ : MvPolynomial.IsWeightedHomogeneous w φ n) (t : B) (z : σ → B) :
    MvPolynomial.aeval (fun p => t ^ (w p) * z p) φ = t ^ n * MvPolynomial.aeval z φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  have hw : Finsupp.weight w m = n := hφ (MvPolynomial.mem_support_iff.mp hm)
  have : (m.prod fun p k => (t ^ w p * z p) ^ k) = t ^ n * m.prod fun p k => z p ^ k := by
    simp only [mul_pow, Finsupp.prod_mul]
    congr 1
    rw [← hw, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, smul_eq_mul, mul_comm]
  rw [this]; ring

/- English proof (translation)
Rewrite using `[← aeval_weighted_scale _ (hG i) t z]`. Establish `: (fun p : ι × Fin r => if p.1 = i then t * z p else z p) = fun p => t ^ (if p.1 = i then 1 else 0) * z p`. Apply the tactic sequence `funext p; split_ifs <;> simp`. Rewrite using `[this]`.
-/
lemma aeval_letter_scale {B : Type} [CommSemiring B] [Algebra K B] {G : MvPolynomial (ι × Fin r) K}
    {d : ι → ℕ} (hG : MultiHom G d) (i : ι) (t : B) (z : ι × Fin r → B) :
    MvPolynomial.aeval (fun p => if p.1 = i then t * z p else z p) G = t ^ d i * MvPolynomial.aeval z G := by
  rw [← aeval_weighted_scale _ (hG i) t z]
  have : (fun p : ι × Fin r => if p.1 = i then t * z p else z p) =
      fun p => t ^ (if p.1 = i then 1 else 0) * z p := by
    funext p; split_ifs <;> simp
  rw [this]

/- English proof (translation)
Proceed by induction on `U using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i U hi ih`. Establish `: (fun p : ι × Fin r => if p.1 ∈ insert i U then t * z p else z p) = fun p => if p.1 = i then t * (if p.1 ∈ U then t * z p else z p) else (if p.1 ∈ U then t * z p else z p)`. Use function extensionality and compare the values at `p`.

Distinguish the cases in `h1 : p.1 = i`. Simplify using `[h1, hi]`. Simplify using `[h1, Finset.mem_insert]`. Rewrite using `[this, aeval_letter_scale hG, ih, Finset.sum_insert hi, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma aeval_set_scale {B : Type} [CommSemiring B] [Algebra K B] {G : MvPolynomial (ι × Fin r) K}
    {d : ι → ℕ} (hG : MultiHom G d) (U : Finset ι) (t : B) (z : ι × Fin r → B) :
    MvPolynomial.aeval (fun p => if p.1 ∈ U then t * z p else z p) G =
      t ^ (∑ i ∈ U, d i) * MvPolynomial.aeval z G := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert i U hi ih =>
    have : (fun p : ι × Fin r => if p.1 ∈ insert i U then t * z p else z p) =
        fun p => if p.1 = i then t * (if p.1 ∈ U then t * z p else z p)
          else (if p.1 ∈ U then t * z p else z p) := by
      funext p
      by_cases h1 : p.1 = i
      · simp [h1, hi]
      · simp [h1, Finset.mem_insert]
    rw [this, aeval_letter_scale hG, ih, Finset.sum_insert hi, pow_add]; ring

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
lemma sum_sum_mat {R : Type} [CommSemiring R] (M N : Matrix (Fin r) (Fin r) R) (v : Fin r → R) (a : Fin r) :
    (∑ b, M a b * ∑ c, N b c * v c) = ∑ c, (M * N) a c * v c := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `[Matrix.smul_apply, Matrix.one_apply]`.
-/
lemma sum_smul_one {R : Type} [CommSemiring R] (t : R) (v : Fin r → R) (a : Fin r) :
    (∑ c, ((t • (1 : Matrix (Fin r) (Fin r) R)) a c) * v c) = t * v a := by
  simp [Matrix.smul_apply, Matrix.one_apply]

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_add_sum_filter_not (S.filter (fun i => i ∉ Set.range A)) (fun i => vec i = true)]`. Use `congr 1`. Apply `Finset.sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `i`. Simplify using `[Finset.mem_filter]`.

The claim follows by propositional logic. Apply `Finset.sum_congr _ (fun _ _ => rfl)` to reduce the goal to its premises. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Bool.not_eq_true]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨h1, _⟩, h3⟩`. Conclude with `⟨h1, h3⟩`. Introduce and unpack `⟨h1, h3⟩`. Use `⟨⟨h1, ?_⟩, h3⟩` and prove the remaining obligations. Introduce and unpack `⟨l, rfl⟩`.

Use `(hAS l).2` as an intermediate fact. Simplify the hypotheses and the goal together.
-/
lemma sum_split (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ)
    (hAS : ∀ l, A l ∈ S ∧ vec (A l) = true) :
    (∑ i ∈ S.filter (fun i => i ∉ Set.range A), d i) =
      (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) +
        ∑ i ∈ S.filter (fun i => vec i = false), d i := by
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter (fun i => i ∉ Set.range A)) (fun i => vec i = true)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i; simp [Finset.mem_filter]; tauto
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Bool.not_eq_true]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rintro ⟨l, rfl⟩
      have := (hAS l).2; simp_all

/- English proof (translation)
Introduce `L _ _ g x hx`. Establish `hv` using `hV L g`. Set `y : ι × Fin r → L[X]` to `fun p => if p.1 ∈ S then (if vec p.1 then (if p.1 ∈ Set.range A then C (x p) else ∑ c, nMat g p.2 c * C (x (p.1, c))) else ∑ c, (msMat g).transpose p.2 c * C (x (p.1, c))) else C (x p)`. Set `ev : MvPolynomial (ι × Fin r) L[X] →ₐ[K] L[X]` to `(MvPolynomial.aeval y).restrictScalars K`. Establish `h1` using `map_dvd ev hv`.

Establish `hC : ev (MvPolynomial.C (X ^ (th + ∑ i ∈ S.filter (fun i => vec i = false), d i))) = X ^ (th + ∑ i ∈ S.filter (fun i => vec i = false), d i)`. Simplify using `[ev]`. Establish `hsub : ev (substS (K` using `K) vec S g G) = MvPolynomial.aeval (fun p => if p.1 ∈ S.filter (fun i => i ∉ Set.range A) then X * ptA A g x p else ptA A g x p) G := by`. Unfold `substS`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`.

Use `congrArg (fun f => MvPolynomial.aeval f G) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Take `⟨i, a⟩` from `p`. Establish `hev : ∀ (M : Matrix (Fin r) (Fin r) L[X]), ev (∑ b, MvPolynomial.C (M a b) * MvPolynomial.X (i, b)) = ∑ b, M a b * y (i, b)`. Introduce `M`.

Simplify using `only [ev, map_sum, map_mul, AlgHom.restrictScalars_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]`. Distinguish the cases in `hS : i ∈ S`. Distinguish the cases in `hvi : vec i = true`. Simplify using `only [if_pos hS, if_pos hvi]`. Rewrite using `[hev]`.

Distinguish the cases in `hA : i ∈ Set.range A`. Establish `hy : ∀ b, y (i, b) = C (x (i, b))` using `fun b => by`. Simplify using `only [y, if_pos hS, if_pos hvi, if_pos hA]`. Establish `hU : i ∉ S.filter (fun i => i ∉ Set.range A)`. Simplify using `only [Finset.mem_filter, hA, not_true_eq_false, and_false, not_false_eq_true]`.

Simplify using `only [hy, if_neg hU, ptA, if_pos hA]`. Establish `hy : ∀ b, y (i, b) = ∑ c, nMat g b c * C (x (i, c))` using `fun b => by`. Simplify using `only [y, if_pos hS, if_pos hvi, if_neg hA]`. Establish `hU : i ∈ S.filter (fun i => i ∉ Set.range A)`. Simplify using `only [Finset.mem_filter, hA, hS, not_false_eq_true, and_self]`.

Simplify using `only [hy, if_pos hU, ptA, if_neg hA]`. Rewrite using `[sum_sum_mat, msMat_mul_nMat, sum_smul_one]`. Establish `hA : i ∉ Set.range A`. Introduce and unpack `⟨l, rfl⟩`. Conclude with `hvi (hAS l).2`.

Simplify using `only [if_pos hS, if_neg hvi]`. Rewrite using `[hev]`. Establish `hy : ∀ b, y (i, b) = ∑ c, (msMat g).transpose b c * C (x (i, c))` using `fun b => by`. Simplify using `only [y, if_pos hS, if_neg hvi]`. Establish `hU : i ∈ S.filter (fun i => i ∉ Set.range A)`.

Simplify using `only [Finset.mem_filter, hA, hS, not_false_eq_true, and_self]`. Simplify using `only [hy, if_pos hU, ptA, if_neg hA]`. Rewrite using `[sum_sum_mat, msDualMat_mul_msMat_transpose, sum_smul_one]`. Establish `hA : i ∉ Set.range A`. Introduce and unpack `⟨l, rfl⟩`.

Conclude with `hS (hAS l).1`. Establish `hU : i ∉ S.filter (fun i => i ∉ Set.range A)`. Simplify using `only [Finset.mem_filter, hS, false_and, not_false_eq_true]`. Simplify using `only [if_neg hS, if_neg hU, ptA, if_neg hA, ev, AlgHom.restrictScalars_apply, MvPolynomial.aeval_X, y]`. Rewrite `h1` using `[hC, hsub, aeval_set_scale hG, sum_split vec S A d hAS]`.

Establish `he : th + ∑ i ∈ S.filter (fun i => vec i = false), d i = ((∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) + ∑ i ∈ S.filter (fun i => vec i = false), d i) + (th - ∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i)` using `by omega`. Rewrite `h1` using `[he, pow_add]`. Conclude with `(mul_dvd_mul_iff_left (pow_ne_zero _ X_ne_zero)).mp h1`.
-/
theorem red_of_valGE (_hr : 0 < r) (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ)
    (G : MvPolynomial (ι × Fin r) K) (th : ℕ)
    (hAS : ∀ l, A l ∈ S ∧ vec (A l) = true) (hG : MultiHom G d) (hV : ValGE vec S d G th)
    (hB : (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) < th) :
    Red A G (th - ∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) := by
  classical
  intro L _ _ g x hx
  have hv := hV L g
  let y : ι × Fin r → L[X] := fun p =>
    if p.1 ∈ S then
      (if vec p.1 then
        (if p.1 ∈ Set.range A then C (x p) else ∑ c, nMat g p.2 c * C (x (p.1, c)))
       else ∑ c, (msMat g).transpose p.2 c * C (x (p.1, c)))
    else C (x p)
  let ev : MvPolynomial (ι × Fin r) L[X] →ₐ[K] L[X] := (MvPolynomial.aeval y).restrictScalars K
  have h1 := map_dvd ev hv
  have hC : ev (MvPolynomial.C (X ^ (th + ∑ i ∈ S.filter (fun i => vec i = false), d i))) =
      X ^ (th + ∑ i ∈ S.filter (fun i => vec i = false), d i) := by
    simp [ev]
  have hsub : ev (substS (K := K) vec S g G) = MvPolynomial.aeval
      (fun p => if p.1 ∈ S.filter (fun i => i ∉ Set.range A) then X * ptA A g x p else ptA A g x p) G := by
    unfold substS
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    refine congrArg (fun f => MvPolynomial.aeval f G) ?_
    funext p
    obtain ⟨i, a⟩ := p
    have hev : ∀ (M : Matrix (Fin r) (Fin r) L[X]),
        ev (∑ b, MvPolynomial.C (M a b) * MvPolynomial.X (i, b)) = ∑ b, M a b * y (i, b) := by
      intro M
      simp only [ev, map_sum, map_mul, AlgHom.restrictScalars_apply, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
    by_cases hS : i ∈ S
    · by_cases hvi : vec i = true
      · simp only [if_pos hS, if_pos hvi]
        rw [hev]
        by_cases hA : i ∈ Set.range A
        · have hy : ∀ b, y (i, b) = C (x (i, b)) := fun b => by
            simp only [y, if_pos hS, if_pos hvi, if_pos hA]
          have hU : i ∉ S.filter (fun i => i ∉ Set.range A) := by
            simp only [Finset.mem_filter, hA, not_true_eq_false, and_false, not_false_eq_true]
          simp only [hy, if_neg hU, ptA, if_pos hA]
        · have hy : ∀ b, y (i, b) = ∑ c, nMat g b c * C (x (i, c)) := fun b => by
            simp only [y, if_pos hS, if_pos hvi, if_neg hA]
          have hU : i ∈ S.filter (fun i => i ∉ Set.range A) := by
            simp only [Finset.mem_filter, hA, hS, not_false_eq_true, and_self]
          simp only [hy, if_pos hU, ptA, if_neg hA]
          rw [sum_sum_mat, msMat_mul_nMat, sum_smul_one]
      · have hA : i ∉ Set.range A := by
          rintro ⟨l, rfl⟩; exact hvi (hAS l).2
        simp only [if_pos hS, if_neg hvi]
        rw [hev]
        have hy : ∀ b, y (i, b) = ∑ c, (msMat g).transpose b c * C (x (i, c)) := fun b => by
          simp only [y, if_pos hS, if_neg hvi]
        have hU : i ∈ S.filter (fun i => i ∉ Set.range A) := by
          simp only [Finset.mem_filter, hA, hS, not_false_eq_true, and_self]
        simp only [hy, if_pos hU, ptA, if_neg hA]
        rw [sum_sum_mat, msDualMat_mul_msMat_transpose, sum_smul_one]
    · have hA : i ∉ Set.range A := by
        rintro ⟨l, rfl⟩; exact hS (hAS l).1
      have hU : i ∉ S.filter (fun i => i ∉ Set.range A) := by
        simp only [Finset.mem_filter, hS, false_and, not_false_eq_true]
      simp only [if_neg hS, if_neg hU, ptA, if_neg hA, ev, AlgHom.restrictScalars_apply,
        MvPolynomial.aeval_X, y]
  rw [hC, hsub, aeval_set_scale hG, sum_split vec S A d hAS] at h1
  have he : th + ∑ i ∈ S.filter (fun i => vec i = false), d i =
      ((∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) +
        ∑ i ∈ S.filter (fun i => vec i = false), d i) +
      (th - ∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) := by omega
  rw [he, pow_add] at h1
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ X_ne_zero)).mp h1

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

/- English proof (translation)
Introduce `hx`. Rewrite `hx` using `[mem_vars_iff_mem_support]`. Take `⟨d, hd, hxd⟩` from `hx`. Establish `h1` using `Finset.le_sup (f := fun m : σ →₀ ℕ => m x) hd`. Rewrite `h1` using `[← degreeOf_eq_sup, h]`.

Rewrite `hxd` using `[Finsupp.mem_support_iff]`. Conclude with `hxd (by simpa using h1)`.
-/
lemma not_mem_vars_of_degreeOf {σ : Type} {p : MvPolynomial σ K} {x : σ} (h : degreeOf x p = 0) :
    x ∉ p.vars := by
  intro hx
  rw [mem_vars_iff_mem_support] at hx
  obtain ⟨d, hd, hxd⟩ := hx
  have h1 := Finset.le_sup (f := fun m : σ →₀ ℕ => m x) hd
  rw [← degreeOf_eq_sup, h] at h1
  rw [Finsupp.mem_support_iff] at hxd
  exact hxd (by simpa using h1)

/- English proof (translation)
Take `⟨q, rfl⟩` from `hpf`. Establish `hp : p ≠ 0` using `left_ne_zero_of_mul hf`. Establish `hq : q ≠ 0` using `right_ne_zero_of_mul hf`. Rewrite `h` using `[degreeOf_mul_eq hp hq]`. Use linear arithmetic over natural numbers and integers.
-/
lemma degreeOf_eq_zero_of_dvd {σ : Type} {p f : MvPolynomial σ K} (x : σ) (hpf : p ∣ f) (hf : f ≠ 0)
    (h : degreeOf x f = 0) : degreeOf x p = 0 := by
  obtain ⟨q, rfl⟩ := hpf
  have hp : p ≠ 0 := left_ne_zero_of_mul hf
  have hq : q ≠ 0 := right_ne_zero_of_mul hf
  rw [degreeOf_mul_eq hp hq] at h
  omega

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Apply `Nat.eq_zero_of_le_zero` to reduce the goal to its premises. Use `(degreeOf_sum_le _ _ _).trans (Finset.sup_le fun σ' _ => ?_)` and prove the remaining obligations. Rewrite using `[Units.smul_def, zsmul_eq_mul, ← map_intCast (C : K →+* MvPolynomial σ K)]`. Use `(degreeOf_C_mul_le _ _ _).trans ?_` and prove the remaining obligations.

Use `(degreeOf_prod_le _ _ _).trans ?_` and prove the remaining obligations. Simplify using `[h]`.
-/
lemma degreeOf_det_eq_zero {σ : Type} (M : Matrix (Fin r) (Fin r) (MvPolynomial σ K)) (x : σ)
    (h : ∀ i j, degreeOf x (M i j) = 0) : degreeOf x M.det = 0 := by
  rw [Matrix.det_apply]
  apply Nat.eq_zero_of_le_zero
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun σ' _ => ?_)
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : K →+* MvPolynomial σ K)]
  refine (degreeOf_C_mul_le _ _ _).trans ?_
  refine (degreeOf_prod_le _ _ _).trans ?_
  simp [h]

/- English proof (translation)
Establish `hv : p.vars = ∅`. Use extensionality with `x`. Simplify using `only [Finset.notMem_empty, iff_false]`. Conclude with `not_mem_vars_of_degreeOf (h x)`. Rewrite `hv` using `[vars_eq_empty_iff_eq_C]`.

Rewrite `hp`, the goal using `[hv]`. Establish `: coeff 0 p ≠ 0` using `fun h0 => hp (by rw [h0, map_zero])`. Conclude with `(isUnit_iff_ne_zero.mpr this).map C`.
-/
lemma isUnit_of_degreeOf_eq_zero {σ : Type} {p : MvPolynomial σ K} (hp : p ≠ 0)
    (h : ∀ x, degreeOf x p = 0) : IsUnit p := by
  have hv : p.vars = ∅ := by
    ext x; simp only [Finset.notMem_empty, iff_false]; exact not_mem_vars_of_degreeOf (h x)
  rw [vars_eq_empty_iff_eq_C] at hv
  rw [hv] at hp ⊢
  have : coeff 0 p ≠ 0 := fun h0 => hp (by rw [h0, map_zero])
  exact (isUnit_iff_ne_zero.mpr this).map C

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

def Tm (K : Type) [Field K] (A : Fin r → ι) : Matrix (Fin r) (Fin r) (MvPolynomial ((ι × Fin r) ⊕ ι) K) :=
  Matrix.of fun l b => X (Sum.inl (A l, b))

def Wv (K : Type) [Field K] (A : Fin r → ι) : Fin r → MvPolynomial ((ι × Fin r) ⊕ ι) K :=
  fun l => X (Sum.inr (A l))

open Classical in

def evPerm (A : Fin r → ι) (τ : Equiv.Perm (Fin r)) : MvPolynomial ((ι × Fin r) ⊕ ι) K →ₐ[K] K :=
  aeval (Sum.elim (fun q => if h : ∃ l, A l = q.1 then (if q.2 = τ (Classical.choose h) then 1 else 0) else 0)
    (fun _ => 0))

/- English proof (translation)
Use extensionality with `l b`. Establish `h : ∃ l', A l' = A l` using `⟨l, rfl⟩`. Establish `hc : Classical.choose h = l` using `hA (Classical.choose_spec h)`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Tm, Matrix.of_apply, evPerm, aeval_X, Sum.elim_inl, dif_pos h, hc]`. Simplify using `[Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]`.
-/
lemma evPerm_Tm (A : Fin r → ι) (hA : Function.Injective A) (τ : Equiv.Perm (Fin r)) :
    (evPerm (K := K) A τ).mapMatrix (Tm K A) = τ.permMatrix K := by
  ext l b
  have h : ∃ l', A l' = A l := ⟨l, rfl⟩
  have hc : Classical.choose h = l := hA (Classical.choose_spec h)
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Tm, Matrix.of_apply, evPerm, aeval_X,
    Sum.elim_inl, dif_pos h, hc]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

/- English proof (translation)
Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]`.
-/
lemma sign_cast_ne_zero (τ : Equiv.Perm (Fin r)) : ((Equiv.Perm.sign τ : ℤ) : K) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

/- English proof (translation)
Introduce `h`. Use `congrArg (evPerm (K := K) A 1) h` as an intermediate fact. Rewrite `this` using `[AlgHom.map_det, evPerm_Tm A hA, Matrix.det_permutation, map_zero]`. Conclude with `sign_cast_ne_zero (K := K) 1 this`.
-/
lemma det_Tm_ne_zero (A : Fin r → ι) (hA : Function.Injective A) : (Tm K A).det ≠ 0 := by
  intro h
  have := congrArg (evPerm (K := K) A 1) h
  rw [AlgHom.map_det, evPerm_Tm A hA, Matrix.det_permutation, map_zero] at this
  exact sign_cast_ne_zero (K := K) 1 this

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[Matrix.adjugate_apply]`. Use `congrArg (evPerm (K := K) A (Equiv.swap l lst)) h` as an intermediate fact. Establish `hm : (evPerm (K` using `K) A (Equiv.swap l lst)).mapMatrix ((Tm K A).updateRow l (Pi.single lst 1)) = (Equiv.swap l lst).permMatrix K := by`. Use extensionality with `i j`.

Establish `hT` using `congrFun (congrFun (evPerm_Tm (K := K) A hA (Equiv.swap l lst)) i) j`. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply] at hT`. Distinguish the cases in `hi : i = l`. Substitute `hi` using the available equality. Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_self]`.

Simplify using `only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.swap_apply_left, Option.mem_def, Option.some.injEq]`. Distinguish the cases in `hj : j = lst`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj, Ne.symm hj]`.

Simplify using `only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne hi]`. Conclude with `hT`. Rewrite `this` using `[AlgHom.map_det, hm, Matrix.det_permutation, map_zero]`. Conclude with `sign_cast_ne_zero (K := K) _ this`.
-/
lemma adj_Tm_ne_zero (A : Fin r → ι) (hA : Function.Injective A) (lst l : Fin r) :
    (Tm K A).adjugate lst l ≠ 0 := by
  classical
  intro h
  rw [Matrix.adjugate_apply] at h
  have := congrArg (evPerm (K := K) A (Equiv.swap l lst)) h
  have hm : (evPerm (K := K) A (Equiv.swap l lst)).mapMatrix ((Tm K A).updateRow l (Pi.single lst 1)) =
      (Equiv.swap l lst).permMatrix K := by
    ext i j
    have hT := congrFun (congrFun (evPerm_Tm (K := K) A hA (Equiv.swap l lst)) i) j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply] at hT
    by_cases hi : i = l
    · subst hi
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_self]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.swap_apply_left,
        Option.mem_def, Option.some.injEq]
      by_cases hj : j = lst
      · subst hj; simp
      · simp [hj, Ne.symm hj]
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne hi]
      exact hT
  rw [AlgHom.map_det, hm, Matrix.det_permutation, map_zero] at this
  exact sign_cast_ne_zero (K := K) _ this

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

def rho (K : Type) [Field K] (A : Fin r → ι) (l : Fin r) :
    MvPolynomial ((ι × Fin r) ⊕ ι) K →ₐ[K] MvPolynomial ((ι × Fin r) ⊕ ι) K :=
  aeval (Sum.elim (fun q => X (Sum.inl q)) (fun i => if i = A l then 1 else 0))

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[rho, Tm]`.
-/
lemma rho_Tm (A : Fin r → ι) (l : Fin r) : (rho K A l).mapMatrix (Tm K A) = Tm K A := by
  ext i j; simp [rho, Tm]

/- English proof (translation)
Use `RingHom.map_adjugate (rho K A l).toRingHom (Tm K A)` as an intermediate fact. Establish `h2 : (rho K A l).toRingHom.mapMatrix (Tm K A) = Tm K A` using `rho_Tm A l`. Rewrite `this` using `[h2]`. Conclude with `congrFun (congrFun this i) j`.
-/
lemma rho_adj (A : Fin r → ι) (l i j : Fin r) : rho K A l ((Tm K A).adjugate i j) = (Tm K A).adjugate i j := by
  have := RingHom.map_adjugate (rho K A l).toRingHom (Tm K A)
  have h2 : (rho K A l).toRingHom.mapMatrix (Tm K A) = Tm K A := rho_Tm A l
  rw [h2] at this
  exact congrFun (congrFun this i) j

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, rho_adj]`. Establish `: ∀ j, rho K A l (Wv K A j) = if j = l then 1 else 0`. Introduce `j`. Simplify using `[rho, Wv, hA.eq_iff]`. Simplify using `only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
lemma rho_cc (A : Fin r → ι) (hA : Function.Injective A) (lst l : Fin r) :
    rho K A l (((Tm K A).adjugate.mulVec (Wv K A)) lst) = (Tm K A).adjugate lst l := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, rho_adj]
  have : ∀ j, rho K A l (Wv K A j) = if j = l then 1 else 0 := by
    intro j; simp [rho, Wv, hA.eq_iff]
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Establish `hsub : (p.vars : Set ((ι × Fin r) ⊕ ι)) ⊆ Set.range Sum.inl`. Introduce `x hx`. Consider the cases of `x with`. Consider the case `inl q => exact ⟨q, rfl⟩`. Consider the case `inr i => exact absurd hx (not_mem_vars_of_degreeOf (hp i))`.

Take `⟨q, rfl⟩` from `exists_rename_eq_of_vars_subset_range p Sum.inl Sum.inl_injective hsub`. Rewrite using `[rho, aeval_rename]`. Establish `: ((Sum.elim (fun q => (X (Sum.inl q) : MvPolynomial ((ι × Fin r) ⊕ ι) K)) (fun i => if i = A l then 1 else 0)) ∘ Sum.inl) = fun q => X (Sum.inl q)`. Use function extensionality and compare the values at `q`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Use `clear hp hsub this`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp' hq' => rw [map_add, map_add, hp', hq']`.

Consider the case `mul_X p n hp' => rw [map_mul, map_mul, hp', aeval_X, rename_X]`.
-/
lemma rho_fix (A : Fin r → ι) (l : Fin r) {p : MvPolynomial ((ι × Fin r) ⊕ ι) K}
    (hp : ∀ i, degreeOf (Sum.inr i) p = 0) : rho K A l p = p := by
  have hsub : (p.vars : Set ((ι × Fin r) ⊕ ι)) ⊆ Set.range Sum.inl := by
    intro x hx
    cases x with
    | inl q => exact ⟨q, rfl⟩
    | inr i => exact absurd hx (not_mem_vars_of_degreeOf (hp i))
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range p Sum.inl Sum.inl_injective hsub
  rw [rho, aeval_rename]
  have : ((Sum.elim (fun q => (X (Sum.inl q) : MvPolynomial ((ι × Fin r) ⊕ ι) K))
      (fun i => if i = A l then 1 else 0)) ∘ Sum.inl) = fun q => X (Sum.inl q) := by
    funext q; simp
  rw [this]
  clear hp hsub this
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp' hq' => rw [map_add, map_add, hp', hq']
  | mul_X p n hp' => rw [map_mul, map_mul, hp', aeval_X, rename_X]

/- English proof (translation)
Introduce `p hpD hpc`. Establish `hD` using `det_Tm_ne_zero (K := K) A hA`. Establish `hp0 : p ≠ 0` using `by rintro rfl; exact hD (zero_dvd_iff.mp hpD)`. Establish `hinr : ∀ i, degreeOf (Sum.inr i) p = 0` using `fun i => degreeOf_eq_zero_of_dvd _ hpD hD (degreeOf_det_eq_zero _ _ fun a b => by`. Simplify using `[Tm, degreeOf_X_of_ne])`.

Establish `hrow : ∀ l b, degreeOf (Sum.inl (A l, b)) p = 0`. Introduce `l b`. Establish `h1 : p ∣ (Tm K A).adjugate lst l`. Use `map_dvd (rho K A l) hpc` as an intermediate fact. Rewrite `this` using `[rho_fix A l hinr, rho_cc A hA]`. Then use the resulting hypothesis.

Use `degreeOf_eq_zero_of_dvd _ h1 (adj_Tm_ne_zero A hA lst l) ?_` and prove the remaining obligations. Rewrite using `[Matrix.adjugate_apply]`. Use `degreeOf_det_eq_zero _ _ fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = l`. Substitute `hi` using the available equality.

Rewrite using `[Matrix.updateRow_self, Pi.single_apply]`. Use `split_ifs`. Conclude with `degreeOf_one _`. Conclude with `degreeOf_zero _`. Rewrite using `[Matrix.updateRow_ne hi]`.

Simplify using `only [Tm, Matrix.of_apply]`. Apply `degreeOf_X_of_ne` to reduce the goal to its premises. Introduce `h`. Simplify using `only [Sum.inl.injEq, Prod.mk.injEq] at h`. Conclude with `hi (hA h.1).symm`.

Apply `isUnit_of_degreeOf_eq_zero hp0` to reduce the goal to its premises. Introduce `x`. Break down `x with ⟨i, b⟩ | i` into its components or cases. Distinguish the cases in `hi : i ∈ Set.range A`. Take `⟨l, rfl⟩` from `hi`.

Conclude with `hrow l b`. Use `degreeOf_eq_zero_of_dvd _ hpD hD (degreeOf_det_eq_zero _ _ fun a c => ?_)` and prove the remaining obligations. Simplify using `only [Tm, Matrix.of_apply]`. Apply `degreeOf_X_of_ne` to reduce the goal to its premises. Introduce `h`.

Simplify using `only [Sum.inl.injEq, Prod.mk.injEq] at h`. Conclude with `hi ⟨a, h.1.symm⟩`. Conclude with `hinr i`.
-/
lemma coprime_det_cc (A : Fin r → ι) (hA : Function.Injective A) (lst : Fin r) :
    IsRelPrime (Tm K A).det (((Tm K A).adjugate.mulVec (Wv K A)) lst) := by
  intro p hpD hpc
  have hD := det_Tm_ne_zero (K := K) A hA
  have hp0 : p ≠ 0 := by rintro rfl; exact hD (zero_dvd_iff.mp hpD)
  have hinr : ∀ i, degreeOf (Sum.inr i) p = 0 := fun i =>
    degreeOf_eq_zero_of_dvd _ hpD hD (degreeOf_det_eq_zero _ _ fun a b => by
      simp [Tm, degreeOf_X_of_ne])
  have hrow : ∀ l b, degreeOf (Sum.inl (A l, b)) p = 0 := by
    intro l b
    have h1 : p ∣ (Tm K A).adjugate lst l := by
      have := map_dvd (rho K A l) hpc
      rwa [rho_fix A l hinr, rho_cc A hA] at this
    refine degreeOf_eq_zero_of_dvd _ h1 (adj_Tm_ne_zero A hA lst l) ?_
    rw [Matrix.adjugate_apply]
    refine degreeOf_det_eq_zero _ _ fun i j => ?_
    by_cases hi : i = l
    · subst hi
      rw [Matrix.updateRow_self, Pi.single_apply]
      split_ifs
      · exact degreeOf_one _
      · exact degreeOf_zero _
    · rw [Matrix.updateRow_ne hi]
      simp only [Tm, Matrix.of_apply]
      apply degreeOf_X_of_ne
      intro h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      exact hi (hA h.1).symm
  apply isUnit_of_degreeOf_eq_zero hp0
  intro x
  rcases x with ⟨i, b⟩ | i
  · by_cases hi : i ∈ Set.range A
    · obtain ⟨l, rfl⟩ := hi; exact hrow l b
    · refine degreeOf_eq_zero_of_dvd _ hpD hD (degreeOf_det_eq_zero _ _ fun a c => ?_)
      simp only [Tm, Matrix.of_apply]
      apply degreeOf_X_of_ne
      intro h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      exact hi ⟨a, h.1.symm⟩
  · exact hinr i

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp' hq' => rw [map_add, map_add, hp', hq']`. Consider the case `mul_X p n hp' => rw [map_mul, map_mul, hp', aeval_X, rename_X]`.
-/
lemma aeval_X_comp {σ τ : Type} (f : σ → τ) (p : MvPolynomial σ K) :
    aeval (fun q => (X (f q) : MvPolynomial τ K)) p = rename f p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp' hq' => rw [map_add, map_add, hp', hq']
  | mul_X p n hp' => rw [map_mul, map_mul, hp', aeval_X, rename_X]

def lst (hr : 0 < r) : Fin r := ⟨r - 1, by omega⟩

section matrices
variable {L : Type} [Field L]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.diagonal_apply, lastIdx_iff hr, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, Pi.single_apply, lst]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
lemma diagonal_last_zero_eq (hr : 0 < r) :
    Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) =
      1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) (Pi.single (lst hr) 1) := by
  ext a b
  simp only [Matrix.diagonal_apply, lastIdx_iff hr, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, Pi.single_apply, lst]
  split_ifs <;> simp_all

/- English proof (translation)
Use `set e : Fin r → L := Pi.single i 1 with he`. Use `set E := Matrix.vecMulVec e (φ - e) with hE`. Use `set Q := Matrix.vecMulVec e e with hQ`. Establish `hv : (φ - e) ⬝ᵥ e = 0`. Rewrite using `[he, dotProduct_single]`.

Simplify using `[hφ]`. Establish `hee : e ⬝ᵥ e = 1` using `by rw [he, dotProduct_single]; simp`. Establish `hEQ : E * Q = 0` using `by rw [hE, hQ, Matrix.vecMulVec_mul_vecMulVec, hv]; simp`. Establish `hEE : E * E = 0` using `by rw [hE, Matrix.vecMulVec_mul_vecMulVec, hv]; simp`. Establish `hQE : Q * E = E` using `by rw [hE, hQ, Matrix.vecMulVec_mul_vecMulVec, hee, one_smul]`.

Establish `hsum : Q + E = Matrix.vecMulVec e φ`. Use extensionality with `a b`. Simplify using `[hQ, hE, Matrix.vecMulVec_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : (1 - E) * (1 - Q) = 1 - Q - E`.

Rewrite using `[sub_mul, one_mul, mul_sub, mul_one, hEQ]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1, mul_add, mul_one, sub_mul, sub_mul, one_mul, hQE, hEE, ← hsum]`. Normalize the expressions using the abelian group laws.
-/
lemma rank_one_conj_eq (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) :
    (1 - Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)) *
      (1 - Matrix.vecMulVec (Pi.single i (1 : L)) (Pi.single i 1)) *
      (1 + Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1))
      = 1 - Matrix.vecMulVec (Pi.single i (1 : L)) φ := by
  set e : Fin r → L := Pi.single i 1 with he
  set E := Matrix.vecMulVec e (φ - e) with hE
  set Q := Matrix.vecMulVec e e with hQ
  have hv : (φ - e) ⬝ᵥ e = 0 := by
    rw [he, dotProduct_single]; simp [hφ]
  have hee : e ⬝ᵥ e = 1 := by rw [he, dotProduct_single]; simp
  have hEQ : E * Q = 0 := by rw [hE, hQ, Matrix.vecMulVec_mul_vecMulVec, hv]; simp
  have hEE : E * E = 0 := by rw [hE, Matrix.vecMulVec_mul_vecMulVec, hv]; simp
  have hQE : Q * E = E := by rw [hE, hQ, Matrix.vecMulVec_mul_vecMulVec, hee, one_smul]
  have hsum : Q + E = Matrix.vecMulVec e φ := by
    ext a b; simp [hQ, hE, Matrix.vecMulVec_apply]; ring
  have h1 : (1 - E) * (1 - Q) = 1 - Q - E := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hEQ]; abel
  rw [h1, mul_add, mul_one, sub_mul, sub_mul, one_mul, hQE, hEE, ← hsum]
  abel

/- English proof (translation)
Rewrite using `[Matrix.vecMulVec_mul_vecMulVec, dotProduct_single]`. Simplify using `[hφ]`.
-/
lemma E_sq (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) :
    Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1) *
      Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1) = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_single]; simp [hφ]

def gU (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) : GL (Fin r) L where
  val := 1 - Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)
  inv := 1 + Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)
  val_inv := by
    rw [mul_add, mul_one, sub_mul, one_mul, E_sq i φ hφ]; abel
  inv_val := by
    rw [add_mul, one_mul, mul_sub, mul_one, E_sq i φ hφ]; abel

/- English proof (translation)
Rewrite using `[diagonal_last_zero_eq hr]`. Conclude with `rank_one_conj_eq (lst hr) φ hφ`.
-/
lemma conj_diagonal_last_zero (hr : 0 < r) (φ : Fin r → L) (hφ : φ (lst hr) = 1) :
    (gU (lst hr) φ hφ).1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) *
      (gU (lst hr) φ hφ)⁻¹.1 = 1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ := by
  rw [diagonal_last_zero_eq hr]
  exact rank_one_conj_eq (lst hr) φ hφ

end matrices

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

/- English proof (translation)
Unfold `detLetters`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `l a`. Simplify using `[Tm]`.
-/
lemma rename_detLetters (A : Fin r → ι) :
    rename Sum.inl (detLetters (K := K) A) = (Tm K A : Matrix (Fin r) (Fin r) (MvPolynomial ((ι × Fin r) ⊕ ι) K)).det := by
  unfold detLetters; rw [AlgHom.map_det]; congr 1; ext l a; simp [Tm]

/- English proof (translation)
Use `set F' := MvPolynomial ((ι × Fin r) ⊕ ι) K`. Set `L` to `FractionRing F'`. Set `am : F' →+* L` to `algebraMap F' L`. Establish `ham : Function.Injective am` using `IsFractionRing.injective F' L`. Use `set T := Tm K A with hT`.

Use `set Dt := T.det with hDt`. Use `set ψ := T.adjugate.mulVec (Wv K A) with hψ`. Use `set c := ψ (lst hr) with hcdef`. Establish `hDt0 : Dt ≠ 0` using `det_Tm_ne_zero A hA`. Establish `hc0 : c ≠ 0`.

Introduce `h0`. Use `rho_cc (K := K) A hA (lst hr) (lst hr)` as an intermediate fact. Rewrite `this` using `[← hψ, ← hcdef, h0, map_zero]`. Conclude with `adj_Tm_ne_zero A hA (lst hr) (lst hr) this.symm`. Establish `hamc : am c ≠ 0` using `fun h0 => hc0 (ham (by rw [h0, map_zero]))`.

Set `φ : Fin r → L` to `fun b => am (ψ b) / am c`. Establish `hφ : φ (lst hr) = 1` using `div_self hamc`. Set `g` to `gU (lst hr) φ hφ`. Set `Y : ι × Fin r → L` to `fun p => am (X (Sum.inl p))`. Establish `hY : MvPolynomial.aeval Y (detLetters (K` using `K) A) = am Dt := by`.

Rewrite using `[aeval_detLetters, hDt, RingHom.map_det]`. Use `congr 1`. Establish `hdiv` using `h L g Y (by rw [hY]; exact fun h0 => hDt0 (ham (by rw [h0, map_zero])))`. Establish `hM0 : ∀ a b, ((msMat g) a b).eval 0 = (1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ) a b`. Introduce `a b`.

Use `congrFun (congrFun (msMat_eval0 g) a) b` as an intermediate fact. Simplify using `only [Matrix.map_apply, Polynomial.coe_evalRingHom] at this`. Rewrite using `[this, conj_diagonal_last_zero hr φ hφ]`. Establish `h0 : MvPolynomial.aeval (fun p => (ptA A g Y p).eval 0) G = 0`. Take `⟨q, hq⟩` from `hdiv`.

Establish `e1` using `congrArg (fun z => (Polynomial.aeval (0 : L)).restrictScalars K z) hq`. Rewrite `e1` using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Simplify `e1` using `[Polynomial.coe_aeval_eq_eval]`. Establish `hTψ : ∀ l, (∑ b, T l b * ψ b) = Dt * Wv K A l`. Introduce `l`.

Establish `: T.mulVec ψ = Dt • Wv K A`. Rewrite using `[hψ, Matrix.mulVec_mulVec, Matrix.mul_adjugate, ← hDt, Matrix.smul_mulVec, Matrix.one_mulVec]`. Use `congrFun this l` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct]`. Set `f : ι × Fin r → Polynomial F'` to `fun p => Polynomial.C (X (Sum.inl p)) - (if p.2 = lst hr ∧ p.1 ∈ Set.range A then Polynomial.C (X (Sum.inr p.1)) * Polynomial.X else 0)`.

Set `Hp : Polynomial F'` to `MvPolynomial.aeval f G`. Establish `hroot : Polynomial.aeval (am Dt / am c) Hp = 0`. Establish `e1 : Polynomial.aeval (am Dt / am c) Hp = MvPolynomial.aeval (fun p => Polynomial.aeval (am Dt / am c) (f p)) G` using `by show ((Polynomial.aeval (am Dt / am c)).restrictScalars K) (MvPolynomial.aeval f G) = _`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Both sides reduce to the same expression.

Rewrite using `[e1, ← h0]`. Use `congr 2`. Use function extensionality and compare the values at `p`. Take `⟨i, a⟩` from `p`. Distinguish the cases in `hi : i ∈ Set.range A`.

Take `⟨l, rfl⟩` from `hi`. Simplify using `only [ptA, f, Set.mem_range_self, and_true, if_true, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, hM0]`. Establish `hsum : ∑ x, (1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ) a x * Y (A l, x) = Y (A l, a) - ((Pi.single (lst hr) (1 : L) : Fin r → L) a) * ∑ x, φ x * Y (A l, x)`. Simplify using `only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]`. Rewrite using `[Finset.mul_sum]`.

Establish `hφY : ∑ x, φ x * Y (A l, x) = am (Dt * Wv K A l) / am c`. Rewrite using `[← hTψ l, map_sum, Finset.sum_div]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [φ, Y, T, Tm, Matrix.of_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsum, hφY]`. Distinguish the cases in `ha : a = lst hr`. Substitute `ha` using the available equality. Simplify using `only [if_true, map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, Pi.single_eq_same, one_mul, Wv, Y]`. Rewrite using `[mul_div_assoc', mul_comm (am (X (Sum.inr (A l)))) (am Dt)]`.

Simplify using `only [if_neg ha, sub_zero, Polynomial.aeval_C, Pi.single_apply, zero_mul, Y]`. Both sides reduce to the same expression. Establish `hi' : ¬ (a = lst hr ∧ i ∈ Set.range A)` using `fun h => hi h.2`. Simplify using `only [f, ptA, if_neg hi, if_neg hi', sub_zero, Polynomial.eval_C, Polynomial.aeval_C, Y]`. Both sides reduce to the same expression.

Establish `hsc : Polynomial.aeval (am Dt) (Hp.scaleRoots c) = 0` using `Polynomial.scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero ham hroot (mem_nonZeroDivisors_of_ne_zero hc0)`. Establish `hisroot : (Hp.scaleRoots c).IsRoot Dt`. Rewrite `hsc` using `[Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]`. Conclude with `ham (by rw [hsc, map_zero])`. Establish `hdvd` using `Polynomial.dvd_term_of_isRoot_of_dvd_terms 0 hisroot (fun j hj => dvd_mul_of_dvd_right (dvd_pow_self Dt hj) _)`.

Rewrite `hdvd` using `[pow_zero, mul_one, Polynomial.coeff_scaleRoots, Polynomial.coeff_zero_eq_eval_zero]`. Establish `hHp0 : Hp.eval 0 = rename Sum.inl G`. Establish `e2 : Hp.eval 0 = MvPolynomial.aeval (fun p => ((Polynomial.aeval (0 : F')).restrictScalars K) (f p)) G`. Rewrite using `[← MvPolynomial.comp_aeval, AlgHom.comp_apply]`. Simplify using `[Hp, Polynomial.coe_aeval_eq_eval]`.

Rewrite using `[e2, ← aeval_X_comp]`. Use `congr 2`. Use function extensionality and compare the values at `p`. Simplify using `only [f, AlgHom.restrictScalars_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_sub, Polynomial.eval_C]`. Use `split_ifs`.

Rewrite using `[Polynomial.eval_mul, Polynomial.eval_X, mul_zero, sub_zero]`. Rewrite using `[Polynomial.eval_zero, sub_zero]`. Rewrite `hdvd` using `[hHp0]`. Establish `hcop` using `(coprime_det_cc (K := K) A hA (lst hr)).pow_right (n := Hp.natDegree - 0)`. Establish `hD' : Dt ∣ rename Sum.inl G` using `hcop.dvd_of_dvd_mul_right hdvd`.

Set `ret : F' →ₐ[K] MvPolynomial (ι × Fin r) K` to `MvPolynomial.aeval (Sum.elim X 0)`. Establish `hret : ∀ q : MvPolynomial (ι × Fin r) K, ret (rename Sum.inl q) = q`. Introduce `q`. Simplify using `only [ret]`. Rewrite using `[aeval_rename]`.

Establish `: (Sum.elim X 0 : (ι × Fin r) ⊕ ι → MvPolynomial (ι × Fin r) K) ∘ Sum.inl = X`. Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules. Rewrite using `[this, aeval_X_left_apply]`. Use `map_dvd ret hD'` as an intermediate fact.

Rewrite `this` using `[hDt, hT, ← rename_detLetters, hret, hret]`. Then use the resulting hypothesis.
-/
theorem dvd_of_red_one (hr : 0 < r) (A : Fin r → ι) (hA : Function.Injective A)
    (G : MvPolynomial (ι × Fin r) K) (h : Red A G 1) : detLetters (K := K) A ∣ G := by
  classical
  set F' := MvPolynomial ((ι × Fin r) ⊕ ι) K
  let L := FractionRing F'
  let am : F' →+* L := algebraMap F' L
  have ham : Function.Injective am := IsFractionRing.injective F' L
  set T := Tm K A with hT
  set Dt := T.det with hDt
  set ψ := T.adjugate.mulVec (Wv K A) with hψ
  set c := ψ (lst hr) with hcdef
  have hDt0 : Dt ≠ 0 := det_Tm_ne_zero A hA
  have hc0 : c ≠ 0 := by
    intro h0
    have := rho_cc (K := K) A hA (lst hr) (lst hr)
    rw [← hψ, ← hcdef, h0, map_zero] at this
    exact adj_Tm_ne_zero A hA (lst hr) (lst hr) this.symm
  have hamc : am c ≠ 0 := fun h0 => hc0 (ham (by rw [h0, map_zero]))
  let φ : Fin r → L := fun b => am (ψ b) / am c
  have hφ : φ (lst hr) = 1 := div_self hamc
  let g := gU (lst hr) φ hφ
  let Y : ι × Fin r → L := fun p => am (X (Sum.inl p))
  have hY : MvPolynomial.aeval Y (detLetters (K := K) A) = am Dt := by
    rw [aeval_detLetters, hDt, RingHom.map_det]; congr 1
  have hdiv := h L g Y (by rw [hY]; exact fun h0 => hDt0 (ham (by rw [h0, map_zero])))
  have hM0 : ∀ a b, ((msMat g) a b).eval 0 = (1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ) a b := by
    intro a b
    have := congrFun (congrFun (msMat_eval0 g) a) b
    simp only [Matrix.map_apply, Polynomial.coe_evalRingHom] at this
    rw [this, conj_diagonal_last_zero hr φ hφ]
  have h0 : MvPolynomial.aeval (fun p => (ptA A g Y p).eval 0) G = 0 := by
    obtain ⟨q, hq⟩ := hdiv
    have e1 := congrArg (fun z => (Polynomial.aeval (0 : L)).restrictScalars K z) hq
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at e1
    simpa [Polynomial.coe_aeval_eq_eval] using e1
  have hTψ : ∀ l, (∑ b, T l b * ψ b) = Dt * Wv K A l := by
    intro l
    have : T.mulVec ψ = Dt • Wv K A := by
      rw [hψ, Matrix.mulVec_mulVec, Matrix.mul_adjugate, ← hDt, Matrix.smul_mulVec, Matrix.one_mulVec]
    have := congrFun this l
    simpa [Matrix.mulVec, dotProduct] using this
  let f : ι × Fin r → Polynomial F' := fun p => Polynomial.C (X (Sum.inl p)) -
    (if p.2 = lst hr ∧ p.1 ∈ Set.range A then Polynomial.C (X (Sum.inr p.1)) * Polynomial.X else 0)
  let Hp : Polynomial F' := MvPolynomial.aeval f G
  have hroot : Polynomial.aeval (am Dt / am c) Hp = 0 := by
    have e1 : Polynomial.aeval (am Dt / am c) Hp =
        MvPolynomial.aeval (fun p => Polynomial.aeval (am Dt / am c) (f p)) G := by
      show ((Polynomial.aeval (am Dt / am c)).restrictScalars K) (MvPolynomial.aeval f G) = _
      rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]; rfl
    rw [e1, ← h0]
    congr 2
    funext p
    obtain ⟨i, a⟩ := p
    by_cases hi : i ∈ Set.range A
    · obtain ⟨l, rfl⟩ := hi
      simp only [ptA, f, Set.mem_range_self, and_true, if_true, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C, hM0]
      have hsum : ∑ x, (1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ) a x * Y (A l, x) =
          Y (A l, a) - ((Pi.single (lst hr) (1 : L) : Fin r → L) a) * ∑ x, φ x * Y (A l, x) := by
        simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, sub_mul,
          Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
          if_true, mul_assoc]
        rw [Finset.mul_sum]
      have hφY : ∑ x, φ x * Y (A l, x) = am (Dt * Wv K A l) / am c := by
        rw [← hTψ l, map_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [φ, Y, T, Tm, Matrix.of_apply, map_mul]
        ring
      rw [hsum, hφY]
      by_cases ha : a = lst hr
      · subst ha
        simp only [if_true, map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, Pi.single_eq_same,
          one_mul, Wv, Y]
        rw [mul_div_assoc', mul_comm (am (X (Sum.inr (A l)))) (am Dt)]
      · simp only [if_neg ha, sub_zero, Polynomial.aeval_C, Pi.single_apply, zero_mul, Y]
        rfl
    · have hi' : ¬ (a = lst hr ∧ i ∈ Set.range A) := fun h => hi h.2
      simp only [f, ptA, if_neg hi, if_neg hi', sub_zero, Polynomial.eval_C, Polynomial.aeval_C, Y]
      rfl
  have hsc : Polynomial.aeval (am Dt) (Hp.scaleRoots c) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero ham hroot (mem_nonZeroDivisors_of_ne_zero hc0)
  have hisroot : (Hp.scaleRoots c).IsRoot Dt := by
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval] at hsc
    exact ham (by rw [hsc, map_zero])
  have hdvd := Polynomial.dvd_term_of_isRoot_of_dvd_terms 0 hisroot
    (fun j hj => dvd_mul_of_dvd_right (dvd_pow_self Dt hj) _)
  rw [pow_zero, mul_one, Polynomial.coeff_scaleRoots, Polynomial.coeff_zero_eq_eval_zero] at hdvd
  have hHp0 : Hp.eval 0 = rename Sum.inl G := by
    have e2 : Hp.eval 0 = MvPolynomial.aeval (fun p => ((Polynomial.aeval (0 : F')).restrictScalars K) (f p)) G := by
      rw [← MvPolynomial.comp_aeval, AlgHom.comp_apply]
      simp [Hp, Polynomial.coe_aeval_eq_eval]
    rw [e2, ← aeval_X_comp]
    congr 2
    funext p
    simp only [f, AlgHom.restrictScalars_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_sub,
      Polynomial.eval_C]
    split_ifs
    · rw [Polynomial.eval_mul, Polynomial.eval_X, mul_zero, sub_zero]
    · rw [Polynomial.eval_zero, sub_zero]
  rw [hHp0] at hdvd
  have hcop := (coprime_det_cc (K := K) A hA (lst hr)).pow_right (n := Hp.natDegree - 0)
  have hD' : Dt ∣ rename Sum.inl G := hcop.dvd_of_dvd_mul_right hdvd
  let ret : F' →ₐ[K] MvPolynomial (ι × Fin r) K := MvPolynomial.aeval (Sum.elim X 0)
  have hret : ∀ q : MvPolynomial (ι × Fin r) K, ret (rename Sum.inl q) = q := by
    intro q
    simp only [ret]
    rw [aeval_rename]
    have : (Sum.elim X 0 : (ι × Fin r) ⊕ ι → MvPolynomial (ι × Fin r) K) ∘ Sum.inl = X := by
      funext p; simp
    rw [this, aeval_X_left_apply]
  have := map_dvd ret hD'
  rwa [hDt, hT, ← rename_detLetters, hret, hret] at this

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro G _`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `G h`. Establish `h1 : Red A G 1` using `fun L _ _ g x hx => (pow_dvd_pow Polynomial.X (by omega)).trans (h L g x hx)`. Take `⟨G', rfl⟩` from `dvd_of_red_one hr A hA G h1`. Establish `h2` using `red_of_mul hr A G' n h`. Rewrite using `[pow_succ']`.

Conclude with `mul_dvd_mul_left _ (ih G' h2)`.
-/
theorem dvd_pow_of_red (hr : 0 < r) (A : Fin r → ι) (hA : Function.Injective A) :
    ∀ (n : ℕ) (G : MvPolynomial (ι × Fin r) K), Red A G n → detLetters (K := K) A ^ n ∣ G := by
  intro n
  induction n with
  | zero => intro G _; simp
  | succ n ih =>
    intro G h
    have h1 : Red A G 1 := fun L _ _ g x hx =>
      (pow_dvd_pow Polynomial.X (by omega)).trans (h L g x hx)
    obtain ⟨G', rfl⟩ := dvd_of_red_one hr A hA G h1
    have h2 := red_of_mul hr A G' n h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih G' h2)

end Formalism.G0.DetDividesP

namespace Formalism.G0

/- English proof (translation)
Introduce `K ι _ _ _ r vec S A d G th hA hAS hG hV hB`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality. Establish `h1 : detLetters (K` using `K) A = 1 := by`. Unfold `detLetters`.

Conclude with `Matrix.det_isEmpty`. Rewrite using `[h1, one_pow]`. Conclude with `one_dvd _`. Conclude with `DetDividesP.dvd_pow_of_red hr A hA _ G (DetDividesP.red_of_valGE hr vec S A d G th hAS hG hV hB)`.
-/
theorem det_divides : DetDivides := by
  intro K ι _ _ _ r vec S A d G th hA hAS hG hV hB
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have h1 : detLetters (K := K) A = 1 := by
      unfold detLetters; exact Matrix.det_isEmpty
    rw [h1, one_pow]; exact one_dvd _
  · exact DetDividesP.dvd_pow_of_red hr A hA _ G
      (DetDividesP.red_of_valGE hr vec S A d G th hAS hG hV hB)

end Formalism.G0

end
