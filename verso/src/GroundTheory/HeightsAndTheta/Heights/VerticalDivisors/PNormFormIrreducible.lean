import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial TensorProduct Matrix

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace NormFormIrreducible

section Basis

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

def polyTensorAlgEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₐ[R] MvPolynomial (Fin n) A :=
  (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R) A).trans
    ((algebraTensorAlgEquiv R A).restrictScalars R)

/- English proof (translation)
Simplify using `[polyTensorAlgEquiv]`.
-/
theorem polyTensorAlgEquiv_tmul (p : MvPolynomial (Fin n) R) (a : A) :
    polyTensorAlgEquiv R A n (p ⊗ₜ a) = a • MvPolynomial.map (algebraMap R A) p := by
  simp [polyTensorAlgEquiv]

def polyTensorEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₗ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A where
  toFun := polyTensorAlgEquiv R A n
  invFun := (polyTensorAlgEquiv R A n).symm
  map_add' := map_add _
  left_inv := (polyTensorAlgEquiv R A n).symm_apply_apply
  right_inv := (polyTensorAlgEquiv R A n).apply_symm_apply
  map_smul' q t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p a =>
      rw [smul_tmul', smul_eq_mul, polyTensorAlgEquiv_tmul, polyTensorAlgEquiv_tmul, RingHom.id_apply,
        Algebra.smul_def q, MvPolynomial.algebraMap_def, map_mul, mul_smul_comm]
    | add s t hs ht =>
      rw [smul_add, map_add, map_add, hs, ht, smul_add]

def polyBasis {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) :
    Module.Basis ι (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
  (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map (polyTensorEquiv R A n)

/- English proof (translation)
Simplify using `[polyBasis, polyTensorEquiv, Algebra.TensorProduct.basis_apply, polyTensorAlgEquiv_tmul, smul_eq_C_mul]`.
-/
theorem polyBasis_apply {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) (i : ι) :
    polyBasis b n i = C (b i) := by
  simp [polyBasis, polyTensorEquiv, Algebra.TensorProduct.basis_apply, polyTensorAlgEquiv_tmul,
    smul_eq_C_mul]

end Basis

/- English proof (translation)
Set `bP` to `polyBasis b n`. Set `M : Fin n → Matrix ι ι R` to `fun j => Algebra.leftMulMatrix b (x j)`. Establish `hM : ∀ j k, x j * b k = ∑ i, M j i k • b i` using `fun j k => by`. Simplify using `only [M, Algebra.leftMulMatrix_eq_repr_mul]`. Conclude with `(b.sum_repr (x j * b k)).symm`.

Establish `key : ∀ (q : MvPolynomial (Fin n) R) (a : A), q • (C a : MvPolynomial (Fin n) A) = MvPolynomial.map (algebraMap R A) q * C a` using `fun q a => by`. Rewrite using `[Algebra.smul_def, MvPolynomial.algebraMap_def]`. Establish `hmat : Algebra.leftMulMatrix bP (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) = ∑ j, (X j : MvPolynomial (Fin n) R) • (M j).map C`. Use `Matrix.ext fun i k => ?_` and prove the remaining obligations. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, polyBasis_apply]`.

Establish `hsum : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k) = ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← C_mul, hM j k, map_sum, Finset.mul_sum]`.

Use `_ = ∑ i', ∑ j, (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := Finset.sum_comm`. Use `_ = ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by`. Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Rewrite using `[polyBasis_apply, key, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_X, map_C, Algebra.smul_def, C_mul, mul_assoc]`. Rewrite using `[hsum, bP.repr_sum_self, Matrix.sum_apply]`. Simplify using `[Matrix.map_apply]`. Rewrite using `[normForm, Algebra.norm_eq_matrix_det bP, hmat]`.
-/
theorem normForm_eq_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (x : Fin n → A) :
    normForm A x = (∑ j, (X j : MvPolynomial (Fin n) R) • (Algebra.leftMulMatrix b (x j)).map C).det := by
  let bP := polyBasis b n
  let M : Fin n → Matrix ι ι R := fun j => Algebra.leftMulMatrix b (x j)
  have hM : ∀ j k, x j * b k = ∑ i, M j i k • b i := fun j k => by
    simp only [M, Algebra.leftMulMatrix_eq_repr_mul]
    exact (b.sum_repr (x j * b k)).symm
  have key : ∀ (q : MvPolynomial (Fin n) R) (a : A),
      q • (C a : MvPolynomial (Fin n) A) = MvPolynomial.map (algebraMap R A) q * C a := fun q a => by
    rw [Algebra.smul_def, MvPolynomial.algebraMap_def]
  have hmat : Algebra.leftMulMatrix bP (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) =
      ∑ j, (X j : MvPolynomial (Fin n) R) • (M j).map C := by
    refine Matrix.ext fun i k => ?_
    rw [Algebra.leftMulMatrix_eq_repr_mul, polyBasis_apply]
    have hsum : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k) =
        ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by
      calc (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k)
          = ∑ j, ∑ i', (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_assoc, ← C_mul, hM j k, map_sum, Finset.mul_sum]
        _ = ∑ i', ∑ j, (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := Finset.sum_comm
        _ = ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [polyBasis_apply, key, map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_mul, map_X, map_C, Algebra.smul_def, C_mul, mul_assoc]
    rw [hsum, bP.repr_sum_self, Matrix.sum_apply]
    simp [Matrix.map_apply]
  rw [normForm, Algebra.norm_eq_matrix_det bP, hmat]

section Embeddings

variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}

def embForm (σ : L →ₐ[E] K) (x : Fin n → L) : MvPolynomial (Fin n) K :=
  ∑ j, X j * C (σ (x j))

/- English proof (translation)
Simplify using `[embForm]`.
-/
theorem eval_embForm (σ : L →ₐ[E] K) (x : Fin n → L) (u : Fin n → K) :
    eval u (embForm σ x) = ∑ j, u j * σ (x j) := by
  simp [embForm]

/- English proof (translation)
Set `pb` to `Field.powerBasisOfFiniteOfSeparable E L`. Set `b` to `pb.basis`. Establish `hcard : Fintype.card (L →ₐ[E] K) = pb.dim` using `by rw [AlgHom.card, pb.finrank]`. Set `e : Fin pb.dim ≃ (L →ₐ[E] K)` to `(Fintype.equivFinOfCardEq hcard).symm`. Set `P` to `Algebra.embeddingsMatrixReindex E K b e`.

Establish `hPij : ∀ i j, P i j = e j (b i)` using `fun i j => by`. Simplify using `[P, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]`. Establish `hP : P.det ≠ 0`. Establish `h` using `(map_ne_zero (algebraMap E K)).mpr (det_traceMatrix_ne_zero' pb)`. Rewrite `h` using `[RingHom.map_det, RingHom.mapMatrix_apply, Algebra.traceMatrix_eq_embeddingsMatrixReindex_mul_trans E K b e, det_mul, det_transpose]`.

Conclude with `left_ne_zero_of_mul h`. Establish `hkey : ∀ (z : L) (k j : Fin pb.dim), ∑ i, algebraMap E K (Algebra.leftMulMatrix b z i k) * P i j = P k j * e j z`. Introduce `z k j`. Establish `h1 : z * b k = ∑ i, Algebra.leftMulMatrix b z i k • b i`. Simplify using `only [Algebra.leftMulMatrix_eq_repr_mul]`.

Conclude with `(b.sum_repr (z * b k)).symm`. Establish `h2` using `congrArg (e j) h1`. Rewrite `h2` using `[map_mul, map_sum]`. Simplify using `only [hPij, Algebra.smul_def, map_mul, AlgHom.commutes] at h2 ⊢`. Rewrite using `[← h2, mul_comm]`.

Rewrite using `[normForm_eq_det b, RingHom.map_det]`. Use `set Λ := (MvPolynomial.map (algebraMap E K)).mapMatrix (∑ j, (X j : MvPolynomial (Fin n) E) • (Algebra.leftMulMatrix b (x j)).map (C : E →+* MvPolynomial (Fin n) E)) with hΛ`. Set `D : Fin pb.dim → MvPolynomial (Fin n) K` to `fun j => embForm (e j) x`. Establish `hconj : Λᵀ * P.map C = P.map C * diagonal D`. Use `Matrix.ext fun k j => ?_` and prove the remaining obligations.

Rewrite using `[mul_diagonal, Matrix.mul_apply]`. Simplify using `only [hΛ, transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_X, map_C, D, embForm]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_mul, map_sum, Finset.mul_sum, map_mul, mul_assoc]`. Conclude with `Finset.sum_comm`.

Use `_ = C (P k j) * ∑ l, X l * C (e j (x l)) := by`. Simplify using `only [hkey, Finset.mul_sum, map_mul]`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`. Establish `hPC : (P.map C : Matrix (Fin pb.dim) (Fin pb.dim) (MvPolynomial (Fin n) K)).det = C P.det`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply]`.

Establish `hdet` using `congrArg det hconj`. Rewrite `hdet` using `[det_mul, det_mul, det_transpose, det_diagonal, hPC]`. Establish `hC : (C P.det : MvPolynomial (Fin n) K) ≠ 0` using `by rwa [Ne, C_eq_zero]`. Establish `h3 : Λ.det = ∏ j, D j` using `mul_right_cancel₀ hC (hdet.trans (mul_comm _ _))`. Rewrite using `[h3]`.

Conclude with `Equiv.prod_comp e (fun σ => embForm σ x)`.
-/
theorem normForm_map_eq_prod [FiniteDimensional E L] [Algebra.IsSeparable E L] [IsAlgClosed K]
    (x : Fin n → L) :
    (normForm (R := E) L x).map (algebraMap E K) = ∏ σ : L →ₐ[E] K, embForm σ x := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable E L
  let b := pb.basis
  have hcard : Fintype.card (L →ₐ[E] K) = pb.dim := by rw [AlgHom.card, pb.finrank]
  let e : Fin pb.dim ≃ (L →ₐ[E] K) := (Fintype.equivFinOfCardEq hcard).symm
  let P := Algebra.embeddingsMatrixReindex E K b e
  have hPij : ∀ i j, P i j = e j (b i) := fun i j => by
    simp [P, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  have hP : P.det ≠ 0 := by
    have h := (map_ne_zero (algebraMap E K)).mpr (det_traceMatrix_ne_zero' pb)
    rw [RingHom.map_det, RingHom.mapMatrix_apply,
      Algebra.traceMatrix_eq_embeddingsMatrixReindex_mul_trans E K b e, det_mul, det_transpose] at h
    exact left_ne_zero_of_mul h
  have hkey : ∀ (z : L) (k j : Fin pb.dim),
      ∑ i, algebraMap E K (Algebra.leftMulMatrix b z i k) * P i j = P k j * e j z := by
    intro z k j
    have h1 : z * b k = ∑ i, Algebra.leftMulMatrix b z i k • b i := by
      simp only [Algebra.leftMulMatrix_eq_repr_mul]
      exact (b.sum_repr (z * b k)).symm
    have h2 := congrArg (e j) h1
    rw [map_mul, map_sum] at h2
    simp only [hPij, Algebra.smul_def, map_mul, AlgHom.commutes] at h2 ⊢
    rw [← h2, mul_comm]
  rw [normForm_eq_det b, RingHom.map_det]
  set Λ := (MvPolynomial.map (algebraMap E K)).mapMatrix
    (∑ j, (X j : MvPolynomial (Fin n) E) •
      (Algebra.leftMulMatrix b (x j)).map (C : E →+* MvPolynomial (Fin n) E)) with hΛ
  let D : Fin pb.dim → MvPolynomial (Fin n) K := fun j => embForm (e j) x
  have hconj : Λᵀ * P.map C = P.map C * diagonal D := by
    refine Matrix.ext fun k j => ?_
    rw [mul_diagonal, Matrix.mul_apply]
    simp only [hΛ, transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, map_X, map_C, D, embForm]
    calc ∑ i, (∑ l, X l * C (algebraMap E K (Algebra.leftMulMatrix b (x l) i k))) * C (P i j)
        = ∑ l, X l * C (∑ i, algebraMap E K (Algebra.leftMulMatrix b (x l) i k) * P i j) := by
          simp only [Finset.sum_mul, map_sum, Finset.mul_sum, map_mul, mul_assoc]
          exact Finset.sum_comm
      _ = C (P k j) * ∑ l, X l * C (e j (x l)) := by
          simp only [hkey, Finset.mul_sum, map_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
  have hPC : (P.map C : Matrix (Fin pb.dim) (Fin pb.dim) (MvPolynomial (Fin n) K)).det = C P.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hdet := congrArg det hconj
  rw [det_mul, det_mul, det_transpose, det_diagonal, hPC] at hdet
  have hC : (C P.det : MvPolynomial (Fin n) K) ≠ 0 := by rwa [Ne, C_eq_zero]
  have h3 : Λ.det = ∏ j, D j := mul_right_cancel₀ hC (hdet.trans (mul_comm _ _))
  rw [h3]
  exact Equiv.prod_comp e (fun σ => embForm σ x)

end Embeddings

section Degree

variable {K : Type*} [Field K] {n : ℕ}

/- English proof (translation)
Rewrite `hd` using `[totalDegree_eq_zero_iff_eq_C]`. Rewrite `hp`, the goal using `[hd]`. Conclude with `(Ne.isUnit fun h => hp (by rw [h, C_0])).map C`.
-/
theorem isUnit_of_totalDegree_eq_zero {p : MvPolynomial (Fin n) K} (hp : p ≠ 0)
    (hd : p.totalDegree = 0) : IsUnit p := by
  rw [totalDegree_eq_zero_iff_eq_C] at hd
  rw [hd] at hp ⊢
  exact (Ne.isUnit fun h => hp (by rw [h, C_0])).map C

/- English proof (translation)
Establish `hne : ℓ ≠ 0` using `by simpa using hc 0`. Use `irreducible_iff.mpr ⟨fun hu => ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Take `⟨r, -, hr⟩` from `isUnit_iff_eq_C_of_isReduced.mp hu`. Conclude with `hc r hr`. Assume the negation of the conclusion as `hnot`.

Rewrite `hnot` using `[not_or]`. Establish `ha : a ≠ 0` using `by rintro rfl; exact hne (by rw [hab, zero_mul])`. Establish `hb : b ≠ 0` using `by rintro rfl; exact hne (by rw [hab, mul_zero])`. Establish `hda : a.totalDegree ≠ 0` using `fun h => hnot.1 (isUnit_of_totalDegree_eq_zero ha h)`. Establish `hdb : b.totalDegree ≠ 0` using `fun h => hnot.2 (isUnit_of_totalDegree_eq_zero hb h)`.

Use `totalDegree_mul_of_isDomain ha hb` as an intermediate fact. Rewrite `this` using `[← hab]`. Use linear arithmetic over natural numbers and integers.
-/
theorem irreducible_of_totalDegree_le_one {ℓ : MvPolynomial (Fin n) K} (h1 : ℓ.totalDegree ≤ 1)
    (hc : ∀ r, ℓ ≠ C r) : Irreducible ℓ := by
  have hne : ℓ ≠ 0 := by simpa using hc 0
  refine irreducible_iff.mpr ⟨fun hu => ?_, fun a b hab => ?_⟩
  · obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
    exact hc r hr
  · by_contra hnot
    rw [not_or] at hnot
    have ha : a ≠ 0 := by rintro rfl; exact hne (by rw [hab, zero_mul])
    have hb : b ≠ 0 := by rintro rfl; exact hne (by rw [hab, mul_zero])
    have hda : a.totalDegree ≠ 0 := fun h => hnot.1 (isUnit_of_totalDegree_eq_zero ha h)
    have hdb : b.totalDegree ≠ 0 := fun h => hnot.2 (isUnit_of_totalDegree_eq_zero hb h)
    have := totalDegree_mul_of_isDomain ha hb
    rw [← hab] at this
    omega

end Degree

section Forms

variable {E L K : Type*} [Field E] [Field L] [Field K] [Algebra E L] [Algebra E K] {n : ℕ}
  {x : Fin n → L} {t : Fin n → E}

/- English proof (translation)
Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)` and prove the remaining obligations. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Simplify using `[totalDegree_X, totalDegree_C]`.
-/
theorem totalDegree_embForm_le (σ : L →ₐ[E] K) (x : Fin n → L) : (embForm σ x).totalDegree ≤ 1 := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  simp [totalDegree_X, totalDegree_C]

/- English proof (translation)
Rewrite using `[eval_embForm, ← map_one σ, ← ht, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, AlgHom.commutes]`.
-/
theorem eval_embForm_alt (σ : L →ₐ[E] K) (ht : ∑ j, algebraMap E L (t j) * x j = 1) :
    eval (fun j => algebraMap E K (t j)) (embForm σ x) = 1 := by
  rw [eval_embForm, ← map_one σ, ← ht, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, AlgHom.commutes]

/- English proof (translation)
Introduce `h`. Establish `h1` using `congrArg (eval fun j => algebraMap E K (t j)) h`. Rewrite `h1` using `[eval_embForm_alt σ ht, eval_C]`. Establish `h0 : r = 0`. Establish `h0` using `congrArg (eval 0) h`.

Rewrite `h0` using `[eval_embForm, eval_C]`. Simplify using `using h0.symm`. Conclude with `one_ne_zero (h1.trans h0)`.
-/
theorem embForm_ne_C (σ : L →ₐ[E] K) (ht : ∑ j, algebraMap E L (t j) * x j = 1) (r : K) :
    embForm σ x ≠ C r := by
  intro h
  have h1 := congrArg (eval fun j => algebraMap E K (t j)) h
  rw [eval_embForm_alt σ ht, eval_C] at h1
  have h0 : r = 0 := by
    have h0 := congrArg (eval 0) h
    rw [eval_embForm, eval_C] at h0
    simpa using h0.symm
  exact one_ne_zero (h1.trans h0)

/- English proof (translation)
The claim follows from `irreducible_of_totalDegree_le_one (totalDegree_embForm_le σ x) (embForm_ne_C σ ht)`.
-/
theorem irreducible_embForm (σ : L →ₐ[E] K) (ht : ∑ j, algebraMap E L (t j) * x j = 1) :
    Irreducible (embForm σ x) :=
  irreducible_of_totalDegree_le_one (totalDegree_embForm_le σ x) (embForm_ne_C σ ht)

/- English proof (translation)
Take `⟨q, hq⟩` from `h`. Establish `hu : IsUnit q` using `((irreducible_embForm τ ht).isUnit_or_isUnit hq).resolve_left (irreducible_embForm σ ht).not_isUnit`. Take `⟨r, -, rfl⟩` from `isUnit_iff_eq_C_of_isReduced.mp hu`. Establish `hr : r = 1`. Use `congrArg (eval fun j => algebraMap E K (t j)) hq` as an intermediate fact.

Rewrite `this` using `[eval_mul, eval_embForm_alt σ ht, eval_embForm_alt τ ht, eval_C, one_mul]`. Conclude with `this.symm`. Rewrite `hq` using `[hr, C_1, mul_one]`. Use `AlgHom.ext_of_adjoin_eq_top hgen ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`.

Use `congrArg (eval (Pi.single j 1)) hq` as an intermediate fact. Simplify `this.symm` using `[eval_embForm, Pi.single_apply]`.
-/
theorem eq_of_embForm_dvd (hgen : Algebra.adjoin E (Set.range x) = ⊤)
    (ht : ∑ j, algebraMap E L (t j) * x j = 1) {σ τ : L →ₐ[E] K}
    (h : embForm σ x ∣ embForm τ x) : σ = τ := by
  obtain ⟨q, hq⟩ := h
  have hu : IsUnit q := ((irreducible_embForm τ ht).isUnit_or_isUnit hq).resolve_left
    (irreducible_embForm σ ht).not_isUnit
  obtain ⟨r, -, rfl⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
  have hr : r = 1 := by
    have := congrArg (eval fun j => algebraMap E K (t j)) hq
    rw [eval_mul, eval_embForm_alt σ ht, eval_embForm_alt τ ht, eval_C, one_mul] at this
    exact this.symm
  rw [hr, C_1, mul_one] at hq
  refine AlgHom.ext_of_adjoin_eq_top hgen ?_
  rintro _ ⟨j, rfl⟩
  have := congrArg (eval (Pi.single j 1)) hq
  simpa [eval_embForm, Pi.single_apply] using this.symm

/- English proof (translation)
It suffices to establish `∀ s : Finset (L →ₐ[E] K), ∏ σ ∈ s, embForm σ x ∣ p from this Finset.univ`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `@insert a s has ih`.

Take `⟨q, hq⟩` from `ih`. Rewrite using `[Finset.prod_insert has]`. Establish `hp : Prime (embForm a x)` using `(irreducible_embForm a ht).prime`. Establish `hd : embForm a x ∣ (∏ σ ∈ s, embForm σ x) * q` using `hq ▸ h a`. Break down `hp.dvd_or_dvd hd with h1 | h1` into its components or cases.

Take `⟨σ, hσ, hdσ⟩` from `(hp.dvd_finsetProd_iff _).mp h1`. Conclude with `absurd (eq_of_embForm_dvd hgen ht hdσ ▸ hσ) has`. Take `⟨q', rfl⟩` from `h1`. Conclude with `⟨q', by rw [hq]; ring⟩`.
-/
theorem prod_embForm_dvd [Fintype (L →ₐ[E] K)] (hgen : Algebra.adjoin E (Set.range x) = ⊤)
    (ht : ∑ j, algebraMap E L (t j) * x j = 1) {p : MvPolynomial (Fin n) K}
    (h : ∀ σ : L →ₐ[E] K, embForm σ x ∣ p) : ∏ σ : L →ₐ[E] K, embForm σ x ∣ p := by
  classical
  suffices ∀ s : Finset (L →ₐ[E] K), ∏ σ ∈ s, embForm σ x ∣ p from this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    obtain ⟨q, hq⟩ := ih
    rw [Finset.prod_insert has]
    have hp : Prime (embForm a x) := (irreducible_embForm a ht).prime
    have hd : embForm a x ∣ (∏ σ ∈ s, embForm σ x) * q := hq ▸ h a
    rcases hp.dvd_or_dvd hd with h1 | h1
    · obtain ⟨σ, hσ, hdσ⟩ := (hp.dvd_finsetProd_iff _).mp h1
      exact absurd (eq_of_embForm_dvd hgen ht hdσ ▸ hσ) has
    · obtain ⟨q', rfl⟩ := h1
      exact ⟨q', by rw [hq]; ring⟩

/- English proof (translation)
Simplify using `[embForm]`.
-/
theorem map_embForm (τ : K →ₐ[E] K) (σ : L →ₐ[E] K) :
    (embForm σ x).map (τ : K →+* K) = embForm (τ.comp σ) x := by
  simp [embForm]

/- English proof (translation)
Rewrite using `[MvPolynomial.map_map, AlgHom.comp_algebraMap]`.
-/
theorem map_map_algebraMap (τ : K →ₐ[E] K) (p : MvPolynomial (Fin n) E) :
    (p.map (algebraMap E K)).map (τ : K →+* K) = p.map (algebraMap E K) := by
  rw [MvPolynomial.map_map, AlgHom.comp_algebraMap]

/- English proof (translation)
Set `pb` to `Field.powerBasisOfFiniteOfSeparable E L`. Establish `hy : Polynomial.aeval (σ' pb.gen) (minpoly E (σ pb.gen)) = 0`. Rewrite using `[minpoly.algHom_eq σ σ.injective, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Take `⟨τ, hτ⟩` from `IntermediateField.exists_algHom_of_splits_of_aeval (fun s => ⟨Algebra.IsIntegral.isIntegral (R := E) s, IsAlgClosed.splits _⟩) hy`. Conclude with `⟨τ, pb.algHom_ext (by simpa using hτ)⟩`.
-/
theorem exists_comp_eq [FiniteDimensional E L] [Algebra.IsSeparable E L] [IsAlgClosed K]
    [Algebra.IsAlgebraic E K] (σ σ' : L →ₐ[E] K) : ∃ τ : K →ₐ[E] K, τ.comp σ = σ' := by
  let pb := Field.powerBasisOfFiniteOfSeparable E L
  have hy : Polynomial.aeval (σ' pb.gen) (minpoly E (σ pb.gen)) = 0 := by
    rw [minpoly.algHom_eq σ σ.injective, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨τ, hτ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
    (fun s => ⟨Algebra.IsIntegral.isIntegral (R := E) s, IsAlgClosed.splits _⟩) hy
  exact ⟨τ, pb.algHom_ext (by simpa using hτ)⟩

/- English proof (translation)
Take `⟨r, hr, hpr⟩` from `isUnit_iff_eq_C_of_isReduced.mp h`. Establish `hc : ∀ m, m ≠ 0 → p.coeff m = 0` using `fun m hm => by`. Use `congrArg (coeff m) hpr` as an intermediate fact. Rewrite `this` using `[coeff_map, coeff_C, if_neg (Ne.symm hm)]`. Conclude with `(algebraMap E K).injective (by rw [this, map_zero])`.

Establish `hp : p = C (p.coeff 0)`. Use extensionality with `m`. Rewrite using `[coeff_C]`. Use `split_ifs with h0`. Rewrite using `[h0]`.

Conclude with `hc m (Ne.symm h0)`. Establish `h0 : p.coeff 0 ≠ 0`. Introduce `h0`. Use `congrArg (coeff 0) hpr` as an intermediate fact. Rewrite `this` using `[coeff_map, h0, map_zero, coeff_C, if_pos rfl]`.

Conclude with `hr.ne_zero this.symm`. Rewrite using `[hp]`. Conclude with `(Ne.isUnit h0).map C`.
-/
theorem isUnit_of_map_isUnit {p : MvPolynomial (Fin n) E} (h : IsUnit (p.map (algebraMap E K))) :
    IsUnit p := by
  obtain ⟨r, hr, hpr⟩ := isUnit_iff_eq_C_of_isReduced.mp h
  have hc : ∀ m, m ≠ 0 → p.coeff m = 0 := fun m hm => by
    have := congrArg (coeff m) hpr
    rw [coeff_map, coeff_C, if_neg (Ne.symm hm)] at this
    exact (algebraMap E K).injective (by rw [this, map_zero])
  have hp : p = C (p.coeff 0) := by
    ext m
    rw [coeff_C]
    split_ifs with h0
    · rw [h0]
    · exact hc m (Ne.symm h0)
  have h0 : p.coeff 0 ≠ 0 := by
    intro h0
    have := congrArg (coeff 0) hpr
    rw [coeff_map, h0, map_zero, coeff_C, if_pos rfl] at this
    exact hr.ne_zero this.symm
  rw [hp]
  exact (Ne.isUnit h0).map C

end Forms

end NormFormIrreducible

open NormFormIrreducible in

/- English proof (translation)
Introduce `E L _ _ _ _ _ _ n x t hgen ht`. Set `_ : Field L` to `(isField_of_isIntegral_of_isField' (R := E) (Field.toIsField E)).toField`. Set `K` to `AlgebraicClosure E`. Establish `hprod` using `normForm_map_eq_prod (E := E) (L := L) (K := K) x`. Establish `hirr : ∀ σ : L →ₐ[E] K, Irreducible (embForm σ x)` using `fun σ => irreducible_embForm σ ht`.

Set `σ₀ : L →ₐ[E] K` to `IsAlgClosed.lift`. Use `irreducible_iff.mpr ⟨fun hu => ?_, fun F G hFG => ?_⟩` and prove the remaining obligations. Use `hu.map (MvPolynomial.map (algebraMap E K))` as an intermediate fact. Rewrite `this` using `[hprod]`. Conclude with `(hirr σ₀).not_isUnit (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun σ => embForm σ x) (Finset.mem_univ σ₀)) this)`.

Establish `hbar : ∏ σ : L →ₐ[E] K, embForm σ x = F.map (algebraMap E K) * G.map (algebraMap E K)`. Rewrite using `[← hprod, hFG, map_mul]`. Establish `hN0 : ∏ σ : L →ₐ[E] K, embForm σ x ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun σ _ => (hirr σ).ne_zero`. Establish `hstable : ∀ p : MvPolynomial (Fin n) E, (∃ σ : L →ₐ[E] K, embForm σ x ∣ p.map (algebraMap E K)) → ∀ σ : L →ₐ[E] K, embForm σ x ∣ p.map (algebraMap E K)`. Introduce and unpack `p ⟨σ, hσ⟩ σ'`.

Take `⟨τ, rfl⟩` from `exists_comp_eq σ σ'`. Use `map_dvd (MvPolynomial.map (τ : K →+* K)) hσ` as an intermediate fact. Rewrite `this` using `[map_embForm, map_map_algebraMap]`. Then use the resulting hypothesis. Establish `hunit : ∀ P Q : MvPolynomial (Fin n) E, (∀ σ : L →ₐ[E] K, embForm σ x ∣ P.map (algebraMap E K)) → ∏ σ : L →ₐ[E] K, embForm σ x = P.map (algebraMap E K) * Q.map (algebraMap E K) → IsUnit Q`. Introduce `P Q hP hPQ`.

Establish `hd` using `prod_embForm_dvd hgen ht hP`. Rewrite `hd`, `hN0` using `[hPQ]`. Establish `hP0 : P.map (algebraMap E K) ≠ 0` using `left_ne_zero_of_mul hN0`. Use `conv_rhs at hd => rw [← mul_one (P.map (algebraMap E K))]`. Conclude with `isUnit_of_map_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hP0).mp hd))`.

Distinguish the cases in `hF : ∃ σ : L →ₐ[E] K, embForm σ x ∣ F.map (algebraMap E K)`. Conclude with `Or.inr (hunit F G (hstable F hF) hbar)`. Simplify using `only [not_exists] at hF`. Use `Or.inl (hunit G F (hstable G ⟨σ₀, ?_⟩) (by rw [hbar, mul_comm]))` and prove the remaining obligations. Conclude with `((hirr σ₀).prime.dvd_or_dvd (hbar ▸ Finset.dvd_prod_of_mem (fun σ => embForm σ x) (Finset.mem_univ σ₀))).resolve_left (hF σ₀)`.
-/
theorem NormFormIrreducible.proof : NormFormIrreducible.Statement := by
  intro E L _ _ _ _ _ _ n x t hgen ht
  let _ : Field L := (isField_of_isIntegral_of_isField' (R := E) (Field.toIsField E)).toField
  classical
  let K := AlgebraicClosure E
  have hprod := normForm_map_eq_prod (E := E) (L := L) (K := K) x
  have hirr : ∀ σ : L →ₐ[E] K, Irreducible (embForm σ x) := fun σ => irreducible_embForm σ ht
  let σ₀ : L →ₐ[E] K := IsAlgClosed.lift
  refine irreducible_iff.mpr ⟨fun hu => ?_, fun F G hFG => ?_⟩
  · have := hu.map (MvPolynomial.map (algebraMap E K))
    rw [hprod] at this
    exact (hirr σ₀).not_isUnit
      (isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun σ => embForm σ x) (Finset.mem_univ σ₀)) this)
  · have hbar : ∏ σ : L →ₐ[E] K, embForm σ x =
        F.map (algebraMap E K) * G.map (algebraMap E K) := by
      rw [← hprod, hFG, map_mul]
    have hN0 : ∏ σ : L →ₐ[E] K, embForm σ x ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun σ _ => (hirr σ).ne_zero
    have hstable : ∀ p : MvPolynomial (Fin n) E, (∃ σ : L →ₐ[E] K, embForm σ x ∣ p.map (algebraMap E K)) →
        ∀ σ : L →ₐ[E] K, embForm σ x ∣ p.map (algebraMap E K) := by
      rintro p ⟨σ, hσ⟩ σ'
      obtain ⟨τ, rfl⟩ := exists_comp_eq σ σ'
      have := map_dvd (MvPolynomial.map (τ : K →+* K)) hσ
      rwa [map_embForm, map_map_algebraMap] at this
    have hunit : ∀ P Q : MvPolynomial (Fin n) E, (∀ σ : L →ₐ[E] K, embForm σ x ∣ P.map (algebraMap E K)) →
        ∏ σ : L →ₐ[E] K, embForm σ x = P.map (algebraMap E K) * Q.map (algebraMap E K) →
          IsUnit Q := by
      intro P Q hP hPQ
      have hd := prod_embForm_dvd hgen ht hP
      rw [hPQ] at hd hN0
      have hP0 : P.map (algebraMap E K) ≠ 0 := left_ne_zero_of_mul hN0
      conv_rhs at hd => rw [← mul_one (P.map (algebraMap E K))]
      exact isUnit_of_map_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hP0).mp hd))
    by_cases hF : ∃ σ : L →ₐ[E] K, embForm σ x ∣ F.map (algebraMap E K)
    · exact Or.inr (hunit F G (hstable F hF) hbar)
    · simp only [not_exists] at hF
      refine Or.inl (hunit G F (hstable G ⟨σ₀, ?_⟩) (by rw [hbar, mul_comm]))
      exact ((hirr σ₀).prime.dvd_or_dvd
        (hbar ▸ Finset.dvd_prod_of_mem (fun σ => embForm σ x) (Finset.mem_univ σ₀))).resolve_left (hF σ₀)

end

end GroundTheory.Heights₂.Heights.Vertical
