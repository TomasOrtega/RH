import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan.Frame

variable {n : ℕ}

/- English proof (translation)
Establish `hnd : A.charpoly.roots.Nodup` using `Polynomial.nodup_roots hA`. Establish `hcard : A.charpoly.roots.card = n`. Rewrite using `[IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Establish `hcs : A.charpoly.roots.toFinset.card = n`. Rewrite using `[Multiset.toFinset_card_of_nodup hnd, hcard]`.

Set `e : Fin n ≃ A.charpoly.roots.toFinset` to `(Finset.equivFinOfCardEq hcs).symm`. Set `l : Fin n → ℂ` to `fun i => (e i : ℂ)`. Establish `hl : Function.Injective l` using `fun i j h => e.injective (Subtype.ext h)`. Establish `hroot : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' A) (l i)` using `fun i => by`. Establish `h1 : l i ∈ A.charpoly.roots` using `Multiset.mem_toFinset.1 (e i).2`.

Establish `h2 : A.charpoly.IsRoot (l i)` using `Polynomial.isRoot_of_mem_roots h1`. Apply `Module.End.hasEigenvalue_iff_mem_spectrum.2` to reduce the goal to its premises. Rewrite using `[Matrix.spectrum_toLin']`. Conclude with `Matrix.mem_spectrum_iff_isRoot_charpoly.2 h2`. Establish `hv : ∀ i, ∃ v, Module.End.HasEigenvector (Matrix.toLin' A) (l i) v` using `fun i => (hroot i).exists_hasEigenvector`.

Use `choose v hv using hv`. Establish `hli : LinearIndependent ℂ v` using `Module.End.eigenvectors_linearIndependent' _ l hl v hv`. Establish `hu : IsUnit (Matrix.of v)` using `(Matrix.linearIndependent_rows_iff_isUnit).1 hli`. Establish `hu' : IsUnit (Matrix.of v)ᵀ`. Simplify using `using hu.map (Matrix.transposeRingEquiv (Fin n) ℂ).toRingHom`.

Take `⟨P, hP⟩` from `hu'`. Use `⟨P, l, hl, ?_⟩` and prove the remaining obligations. Rewrite using `[hP]`. Use extensionality with `a i`. Establish `h` using `(hv i).apply_eq_smul`.

Establish `h'` using `congrFun h a`. Rewrite `h'` using `[Matrix.toLin'_apply]`. Rewrite using `[Matrix.mul_diagonal]`. Simplify `h'` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem exists_frame (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.charpoly.Separable) :
    ∃ (P : GL (Fin n) ℂ) (l : Fin n → ℂ), Function.Injective l ∧
      A * P.val = P.val * Matrix.diagonal l := by
  classical
  have hnd : A.charpoly.roots.Nodup := Polynomial.nodup_roots hA
  have hcard : A.charpoly.roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcs : A.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  let e : Fin n ≃ A.charpoly.roots.toFinset := (Finset.equivFinOfCardEq hcs).symm
  let l : Fin n → ℂ := fun i => (e i : ℂ)
  have hl : Function.Injective l := fun i j h => e.injective (Subtype.ext h)
  have hroot : ∀ i, Module.End.HasEigenvalue (Matrix.toLin' A) (l i) := fun i => by
    have h1 : l i ∈ A.charpoly.roots := Multiset.mem_toFinset.1 (e i).2
    have h2 : A.charpoly.IsRoot (l i) := Polynomial.isRoot_of_mem_roots h1
    apply Module.End.hasEigenvalue_iff_mem_spectrum.2
    rw [Matrix.spectrum_toLin']
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.2 h2
  have hv : ∀ i, ∃ v, Module.End.HasEigenvector (Matrix.toLin' A) (l i) v :=
    fun i => (hroot i).exists_hasEigenvector
  choose v hv using hv
  have hli : LinearIndependent ℂ v :=
    Module.End.eigenvectors_linearIndependent' _ l hl v hv
  have hu : IsUnit (Matrix.of v) := (Matrix.linearIndependent_rows_iff_isUnit).1 hli
  have hu' : IsUnit (Matrix.of v)ᵀ := by
    simpa using hu.map (Matrix.transposeRingEquiv (Fin n) ℂ).toRingHom
  obtain ⟨P, hP⟩ := hu'
  refine ⟨P, l, hl, ?_⟩
  rw [hP]
  ext a i
  have h := (hv i).apply_eq_smul
  have h' := congrFun h a
  rw [Matrix.toLin'_apply] at h'
  rw [Matrix.mul_diagonal]
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using h'

/- English proof (translation)
Set `ι : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)` to `(WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm`. Establish `key : ∀ U : Submodule ℂ (Fin n → ℂ), (perp (starRingEnd ℂ) U).map ι.toLinearMap = (U.map ι.toLinearMap)ᗮ`. Introduce `U`. Use extensionality with `y`. Rewrite using `[Submodule.mem_orthogonal]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩ _ ⟨x, hx, rfl⟩`. Use `hz x hx` as an intermediate fact. Rewrite using `[EuclideanSpace.inner_eq_star_dotProduct]`. Simplify `this` using `[ι, dotProduct, mul_comm]`.

Introduce `h`. Use `⟨ι.symm y, fun x hx => ?_, by simp⟩` and prove the remaining obligations. Use `h (ι x) ⟨x, hx, rfl⟩` as an intermediate fact. Rewrite `this` using `[EuclideanSpace.inner_eq_star_dotProduct]`. Simplify `this` using `[ι, dotProduct, mul_comm]`.

Apply `Submodule.map_injective_of_injective (f := ι.toLinearMap) ι.injective` to reduce the goal to its premises. Rewrite using `[key, key, Submodule.orthogonal_orthogonal]`.
-/
theorem perp_perp' (W : Submodule ℂ (Fin n → ℂ)) :
    perp (starRingEnd ℂ) (perp (starRingEnd ℂ) W) = W := by
  let ι : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  have key : ∀ U : Submodule ℂ (Fin n → ℂ),
      (perp (starRingEnd ℂ) U).map ι.toLinearMap = (U.map ι.toLinearMap)ᗮ := by
    intro U
    ext y
    rw [Submodule.mem_orthogonal]
    constructor
    · rintro ⟨z, hz, rfl⟩ _ ⟨x, hx, rfl⟩
      have := hz x hx
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simpa [ι, dotProduct, mul_comm] using this
    · intro h
      refine ⟨ι.symm y, fun x hx => ?_, by simp⟩
      have := h (ι x) ⟨x, hx, rfl⟩
      rw [EuclideanSpace.inner_eq_star_dotProduct] at this
      simpa [ι, dotProduct, mul_comm] using this
  apply Submodule.map_injective_of_injective (f := ι.toLinearMap) ι.injective
  rw [key, key, Submodule.orthogonal_orthogonal]

/- English proof (translation)
Rewrite using `[perpD, perpD, perp_img, perp_perp', img_mul]`.
-/
theorem perpD_perpD (d : GL (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    perpD (starRingEnd ℂ) d (perpD (starRingEnd ℂ) d W) = img (d * thC n d) W := by
  rw [perpD, perpD, perp_img, perp_perp', img_mul]

/- English proof (translation)
Use extensionality with `g : 2`. Rewrite using `[pow_two]`. Express the relevant statement in the definitionally equal form `((thC n) ((thC n) g)).val = g.val`. Rewrite using `[thC_val, ← map_inv, thC_val, inv_inv]`. Simplify using the standard rewrite rules.
-/
theorem thC_sq : (thC n) ^ 2 = 1 := by
  ext g : 2
  rw [pow_two]
  change ((thC n) ((thC n) g)).val = g.val
  rw [thC_val, ← map_inv, thC_val, inv_inv]
  simp

/- English proof (translation)
Simplify using `[twNorm, List.range_succ]`.
-/
theorem twNorm_thC (d : GL (Fin n) ℂ) : twNorm (thC n) 2 d = d * thC n d := by
  simp [twNorm, List.range_succ]

/- English proof (translation)
Use `twCent_commute_twNorm (thC n) thC_sq d ht` as an intermediate fact. Rewrite `this` using `[twNorm_thC]`. Then use the resulting hypothesis.
-/
theorem commute_of_mem (d t : GL (Fin n) ℂ) (ht : t ∈ twCent (thC n) d) :
    t * (d * thC n d) = (d * thC n d) * t := by
  have := twCent_commute_twNorm (thC n) thC_sq d ht
  rwa [twNorm_thC] at this

/- English proof (translation)
Establish `hp : ∀ m : ℕ, (A ^ m) *ᵥ v = c ^ m • v`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`.

Rewrite using `[pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]`. Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp' hq' => simp only [map_add, Matrix.add_mulVec, hp', hq', Polynomial.eval_add, add_smul]`. Consider the case `monomial m a`. Rewrite using `[Polynomial.aeval_monomial, Polynomial.eval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mulVec, hp, smul_smul]`.
-/
theorem aeval_eig (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (c : ℂ) (h : A *ᵥ v = c • v)
    (q : Polynomial ℂ) : (Polynomial.aeval A q) *ᵥ v = q.eval c • v := by
  have hp : ∀ m : ℕ, (A ^ m) *ᵥ v = c ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]
  induction q using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add, Matrix.add_mulVec, hp', hq', Polynomial.eval_add, add_smul]
  | monomial m a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, Matrix.smul_mulVec, hp, smul_smul]

/- English proof (translation)
Establish `hp : ∀ m : ℕ, ∀ x ∈ W, (A ^ m) *ᵥ x ∈ W`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro x hx`. Simplify using `using hx`.

Consider the case `succ m ih`. Introduce `x hx`. Rewrite using `[pow_succ, ← Matrix.mulVec_mulVec]`. Conclude with `ih _ (h x hx)`. Proceed by induction on `q using Polynomial.induction_on' with`.

Consider the case `add p q hp' hq'`. Introduce `x hx`. Rewrite using `[map_add, Matrix.add_mulVec]`. Conclude with `W.add_mem (hp' x hx) (hq' x hx)`. Consider the case `monomial m a`.

Introduce `x hx`. Rewrite using `[Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.smul_mulVec]`. Conclude with `W.smul_mem _ (hp m x hx)`.
-/
theorem aeval_stable (A : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ))
    (h : ∀ x ∈ W, A *ᵥ x ∈ W) (q : Polynomial ℂ) : ∀ x ∈ W, (Polynomial.aeval A q) *ᵥ x ∈ W := by
  have hp : ∀ m : ℕ, ∀ x ∈ W, (A ^ m) *ᵥ x ∈ W := by
    intro m
    induction m with
    | zero => intro x hx; simpa using hx
    | succ m ih =>
      intro x hx
      rw [pow_succ, ← Matrix.mulVec_mulVec]
      exact ih _ (h x hx)
  induction q using Polynomial.induction_on' with
  | add p q hp' hq' =>
    intro x hx
    rw [map_add, Matrix.add_mulVec]
    exact W.add_mem (hp' x hx) (hq' x hx)
  | monomial m a =>
    intro x hx
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec]
    exact W.smul_mem _ (hp m x hx)

/- English proof (translation)
Rewrite using `[← Matrix.mulVecLin_apply, map_sum]`. Simplify using `only [map_smul, Matrix.mulVecLin_apply]`.
-/
theorem mulVec_sum_smul (M : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) (v : Fin n → Fin n → ℂ) :
    M *ᵥ (∑ j, a j • v j) = ∑ j, a j • (M *ᵥ v j) := by
  rw [← Matrix.mulVecLin_apply, map_sum]
  simp only [map_smul, Matrix.mulVecLin_apply]

/- English proof (translation)
Establish `h : ∀ y : Fin n → ℂ, P.val *ᵥ y = ∑ j, y j • (P.val *ᵥ Pi.single j 1)`. Introduce `y`. Use extensionality with `a`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Rewrite using `[← h, Matrix.mulVec_mulVec, ← Units.val_mul]`.

Simplify using the standard rewrite rules.
-/
theorem expand (P : GL (Fin n) ℂ) (x : Fin n → ℂ) :
    x = ∑ j, ((P⁻¹ : GL (Fin n) ℂ).val *ᵥ x) j • (P.val *ᵥ Pi.single j 1) := by
  have h : ∀ y : Fin n → ℂ, P.val *ᵥ y = ∑ j, y j • (P.val *ᵥ Pi.single j 1) := by
    intro y
    ext a
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul]
  simp

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]`. Use `congr 1`. Use extensionality with `a`. Rewrite using `[Matrix.mulVec_diagonal]`. Distinguish the cases in `h : a = j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.
-/
theorem eig_col (A : Matrix (Fin n) (Fin n) ℂ) (P : GL (Fin n) ℂ) (l : Fin n → ℂ)
    (hA : A * P.val = P.val * Matrix.diagonal l) (j : Fin n) :
    A *ᵥ (P.val *ᵥ Pi.single j 1) = l j • (P.val *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
  congr 1
  ext a
  rw [Matrix.mulVec_diagonal]
  by_cases h : a = j
  · subst h; simp
  · simp [Pi.single_apply, h]

/- English proof (translation)
Establish `e1 : (Polynomial.aeval A (Lagrange.basis Finset.univ l i)) *ᵥ x = ((P⁻¹ : GL (Fin n) ℂ).val *ᵥ x) i • (P.val *ᵥ Pi.single i 1)` using `by conv_lhs => rw [expand P x, mulVec_sum_smul]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[aeval_eig A _ _ (eig_col A P l hA i), Lagrange.eval_basis_self hl.injOn (Finset.mem_univ i), one_smul]`. Introduce `j _ hj`. Rewrite using `[aeval_eig A _ _ (eig_col A P l hA j), Lagrange.eval_basis_of_ne hj.symm (Finset.mem_univ j), zero_smul, smul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Establish `h2` using `aeval_stable A W hW (Lagrange.basis Finset.univ l i) x hx`. Rewrite `h2` using `[e1]`. Conclude with `(W.smul_mem_iff hi).1 h2`.
-/
theorem coord_mem (A : Matrix (Fin n) (Fin n) ℂ) (P : GL (Fin n) ℂ) (l : Fin n → ℂ)
    (hl : Function.Injective l) (hA : A * P.val = P.val * Matrix.diagonal l)
    (W : Submodule ℂ (Fin n → ℂ)) (hW : ∀ x ∈ W, A *ᵥ x ∈ W) {x : Fin n → ℂ} (hx : x ∈ W)
    (i : Fin n) (hi : ((P⁻¹ : GL (Fin n) ℂ).val *ᵥ x) i ≠ 0) : P.val *ᵥ Pi.single i 1 ∈ W := by
  classical
  have e1 : (Polynomial.aeval A (Lagrange.basis Finset.univ l i)) *ᵥ x =
      ((P⁻¹ : GL (Fin n) ℂ).val *ᵥ x) i • (P.val *ᵥ Pi.single i 1) := by
    conv_lhs => rw [expand P x, mulVec_sum_smul]
    rw [Finset.sum_eq_single i]
    · rw [aeval_eig A _ _ (eig_col A P l hA i),
        Lagrange.eval_basis_self hl.injOn (Finset.mem_univ i), one_smul]
    · intro j _ hj
      rw [aeval_eig A _ _ (eig_col A P l hA j),
        Lagrange.eval_basis_of_ne hj.symm (Finset.mem_univ j), zero_smul, smul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  have h2 := aeval_stable A W hW (Lagrange.basis Finset.univ l i) x hx
  rw [e1] at h2
  exact (W.smul_mem_iff hi).1 h2

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Use `congrFun (congrFun h i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Rewrite using `[Matrix.diagonal_apply_ne _ hij]`. Establish `h3 : M i j * (l j - l i) = 0` using `by rw [mul_sub, this]; ring`. Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. Conclude with `h4`.

Conclude with `absurd (hl (sub_eq_zero.1 h4)).symm hij`.
-/
theorem diag_of_commute (M : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ) (hl : Function.Injective l)
    (h : M * Matrix.diagonal l = Matrix.diagonal l * M) :
    M = Matrix.diagonal fun i => M i i := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · have := congrFun (congrFun h i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    rw [Matrix.diagonal_apply_ne _ hij]
    have h3 : M i j * (l j - l i) = 0 := by rw [mul_sub, this]; ring
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact h4
    · exact absurd (hl (sub_eq_zero.1 h4)).symm hij

/- English proof (translation)
Rewrite using `[expand P x, mulVec_sum_smul]`. Use `W.sum_mem fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : ((P⁻¹ : GL (Fin n) ℂ).val *ᵥ x) j = 0`. Rewrite using `[hj, zero_smul]`. Conclude with `W.zero_mem`.

Rewrite using `[eig_col B P a hB j]`. Conclude with `W.smul_mem _ (W.smul_mem _ (coord_mem A P l hl hA W hW hx j hj))`.
-/
theorem stable_of_diag (A B : Matrix (Fin n) (Fin n) ℂ) (P : GL (Fin n) ℂ) (l a : Fin n → ℂ)
    (hl : Function.Injective l) (hA : A * P.val = P.val * Matrix.diagonal l)
    (hB : B * P.val = P.val * Matrix.diagonal a)
    (W : Submodule ℂ (Fin n → ℂ)) (hW : ∀ x ∈ W, A *ᵥ x ∈ W) {x : Fin n → ℂ} (hx : x ∈ W) :
    B *ᵥ x ∈ W := by
  rw [expand P x, mulVec_sum_smul]
  refine W.sum_mem fun j _ => ?_
  by_cases hj : ((P⁻¹ : GL (Fin n) ℂ).val *ᵥ x) j = 0
  · rw [hj, zero_smul]; exact W.zero_mem
  · rw [eig_col B P a hB j]
    exact W.smul_mem _ (W.smul_mem _ (coord_mem A P l hl hA W hW hx j hj))

/- English proof (translation)
Assume the negation of the conclusion as `h`. Conclude with `hi (coord_mem A P l hl hA W hW hx i h)`.
-/
theorem coord_zero (A : Matrix (Fin n) (Fin n) ℂ) (P : GL (Fin n) ℂ) (l : Fin n → ℂ)
    (hl : Function.Injective l) (hA : A * P.val = P.val * Matrix.diagonal l)
    (W : Submodule ℂ (Fin n → ℂ)) (hW : ∀ x ∈ W, A *ᵥ x ∈ W) {x : Fin n → ℂ} (hx : x ∈ W)
    (i : Fin n) (hi : P.val *ᵥ Pi.single i 1 ∉ W) : ((P⁻¹ : GL (Fin n) ℂ).val *ᵥ x) i = 0 := by
  by_contra h
  exact hi (coord_mem A P l hl hA W hW hx i h)

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Simplify using the standard rewrite rules.
-/
theorem conj_entry (P : GL (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    ((P⁻¹ : GL (Fin n) ℂ).val * X * P.val) i i =
      ((P⁻¹ : GL (Fin n) ℂ).val *ᵥ (X *ᵥ (P.val *ᵥ Pi.single i 1))) i := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp

/- English proof (translation)
Take `⟨P, l, hl, hA⟩` from `exists_frame _ hs`. Establish `i1 : img (d * thC n d) W₁ = W₁` using `by rw [← perpD_perpD, h1, h2]`. Establish `i2 : img (d * thC n d) W₂ = W₂` using `by rw [← perpD_perpD, h2, h1]`. Establish `stab : ∀ W : Submodule ℂ (Fin n → ℂ), img (d * thC n d) W = W → ∀ x ∈ W, (d * thC n d).val *ᵥ x ∈ W`. Introduce `W hW x hx`.

Establish `: (d * thC n d).val *ᵥ x ∈ img (d * thC n d) W` using `⟨x, hx, by rw [Matrix.toLin'_apply]⟩`. Rewrite `this` using `[hW]`. Then use the resulting hypothesis. Establish `s1` using `stab W₁ i1`. Establish `s2` using `stab W₂ i2`. Establish `hDv : (P⁻¹ * (d * thC n d) * P).val = Matrix.diagonal l`.

Rewrite using `[mul_assoc, Units.val_mul, Units.val_mul (d * thC n d), hA, ← mul_assoc, ← Units.val_mul]`. Simplify using the standard rewrite rules. Establish `hdiag : ∀ t ∈ twCent (thC n) d, (P⁻¹ * t * P).val = Matrix.diagonal fun i => (P⁻¹ * t * P).val i i`. Introduce `t ht`. Apply `diag_of_commute _ l hl` to reduce the goal to its premises.

Rewrite using `[← hDv, ← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Establish `hc` using `commute_of_mem d t ht`. Combine the equalities or inequalities in the displayed calculation. Establish `hB : ∀ t ∈ twCent (thC n) d, t.val * P.val = P.val * Matrix.diagonal fun i => (P⁻¹ * t * P).val i i`.

Introduce `t ht`. Rewrite using `[← hdiag t ht, ← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`. Establish `hle' : ∀ W : Submodule ℂ (Fin n → ℂ), (∀ x ∈ W, (d * thC n d).val *ᵥ x ∈ W) → ∀ t ∈ twCent (thC n) d, img t W ≤ W`.

Introduce and unpack `W hW t ht _ ⟨x, hx, rfl⟩`. Rewrite using `[Matrix.toLin'_apply]`. Conclude with `stable_of_diag _ _ P l _ hl hA (hB t ht) W hW hx`. Establish `heq : ∀ W : Submodule ℂ (Fin n → ℂ), (∀ x ∈ W, (d * thC n d).val *ᵥ x ∈ W) → ∀ t ∈ twCent (thC n) d, img t W = W`. Introduce `W hW t ht`.

Use `le_antisymm (hle' W hW t ht) ?_` and prove the remaining obligations. Establish `h3` using `img_le_img t (hle' W hW t⁻¹ ((twCent (thC n) d).inv_mem ht))`. Rewrite `h3` using `[img_inv_img]`. Then use the resulting hypothesis. Use `⟨P, fun t ht => ⟨_, hdiag t ht⟩, fun X hX i => ?_, fun t ht => ⟨heq W₁ s1 t ht, heq W₂ s2 t ht⟩⟩` and prove the remaining obligations. Rewrite using `[conj_entry]`.

Distinguish the cases in `c2 : P.val *ᵥ Pi.single i 1 ∈ W₂`. Distinguish the cases in `c1 : P.val *ᵥ Pi.single i 1 ∈ W₁`. Rewrite using `[hX.2.2 _ c1, Matrix.mulVec_zero]`. Both sides reduce to the same expression. Conclude with `coord_zero _ P l hl hA W₁ s1 (hX.2.1 _ c2) i c1`.

Conclude with `coord_zero _ P l hl hA W₂ s2 (hX.1 _) i c2`.
-/
theorem eigenframe (n : ℕ) (d : GL (Fin n) ℂ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (hs : (d * thC n d).val.charpoly.Separable) (hle : W₁ ≤ W₂)
    (h1 : perpD (starRingEnd ℂ) d W₁ = W₂) (h2 : perpD (starRingEnd ℂ) d W₂ = W₁) :
    ∃ P : GL (Fin n) ℂ,
      (∀ t ∈ twCent (thC n) d, ∃ a : Fin n → ℂ, (P⁻¹ * t * P).val = Matrix.diagonal a) ∧
      (∀ X ∈ nilrad W₁ W₂, ∀ i, ((P⁻¹ : GL (Fin n) ℂ).val * X * P.val) i i = 0) ∧
      (∀ t ∈ twCent (thC n) d, img t W₁ = W₁ ∧ img t W₂ = W₂) := by
  obtain ⟨P, l, hl, hA⟩ := exists_frame _ hs
  have i1 : img (d * thC n d) W₁ = W₁ := by rw [← perpD_perpD, h1, h2]
  have i2 : img (d * thC n d) W₂ = W₂ := by rw [← perpD_perpD, h2, h1]
  have stab : ∀ W : Submodule ℂ (Fin n → ℂ), img (d * thC n d) W = W →
      ∀ x ∈ W, (d * thC n d).val *ᵥ x ∈ W := by
    intro W hW x hx
    have : (d * thC n d).val *ᵥ x ∈ img (d * thC n d) W :=
      ⟨x, hx, by rw [Matrix.toLin'_apply]⟩
    rwa [hW] at this
  have s1 := stab W₁ i1
  have s2 := stab W₂ i2
  have hDv : (P⁻¹ * (d * thC n d) * P).val = Matrix.diagonal l := by
    rw [mul_assoc, Units.val_mul, Units.val_mul (d * thC n d), hA, ← mul_assoc, ← Units.val_mul]
    simp
  have hdiag : ∀ t ∈ twCent (thC n) d, (P⁻¹ * t * P).val =
      Matrix.diagonal fun i => (P⁻¹ * t * P).val i i := by
    intro t ht
    apply diag_of_commute _ l hl
    rw [← hDv, ← Units.val_mul, ← Units.val_mul]
    congr 1
    have hc := commute_of_mem d t ht
    calc P⁻¹ * t * P * (P⁻¹ * (d * thC n d) * P) = P⁻¹ * (t * (d * thC n d)) * P := by group
      _ = P⁻¹ * ((d * thC n d) * t) * P := by rw [hc]
      _ = P⁻¹ * (d * thC n d) * P * (P⁻¹ * t * P) := by group
  have hB : ∀ t ∈ twCent (thC n) d, t.val * P.val =
      P.val * Matrix.diagonal fun i => (P⁻¹ * t * P).val i i := by
    intro t ht
    rw [← hdiag t ht, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have hle' : ∀ W : Submodule ℂ (Fin n → ℂ), (∀ x ∈ W, (d * thC n d).val *ᵥ x ∈ W) →
      ∀ t ∈ twCent (thC n) d, img t W ≤ W := by
    rintro W hW t ht _ ⟨x, hx, rfl⟩
    rw [Matrix.toLin'_apply]
    exact stable_of_diag _ _ P l _ hl hA (hB t ht) W hW hx
  have heq : ∀ W : Submodule ℂ (Fin n → ℂ), (∀ x ∈ W, (d * thC n d).val *ᵥ x ∈ W) →
      ∀ t ∈ twCent (thC n) d, img t W = W := by
    intro W hW t ht
    refine le_antisymm (hle' W hW t ht) ?_
    have h3 := img_le_img t (hle' W hW t⁻¹ ((twCent (thC n) d).inv_mem ht))
    rwa [img_inv_img] at h3
  refine ⟨P, fun t ht => ⟨_, hdiag t ht⟩, fun X hX i => ?_,
    fun t ht => ⟨heq W₁ s1 t ht, heq W₂ s2 t ht⟩⟩
  rw [conj_entry]
  by_cases c2 : P.val *ᵥ Pi.single i 1 ∈ W₂
  · by_cases c1 : P.val *ᵥ Pi.single i 1 ∈ W₁
    · rw [hX.2.2 _ c1, Matrix.mulVec_zero]; rfl
    · exact coord_zero _ P l hl hA W₁ s1 (hX.2.1 _ c2) i c1
  · exact coord_zero _ P l hl hA W₂ s2 (hX.1 _) i c2

end GlobalTheory.CompanionTheory.LocVan.Frame
end
