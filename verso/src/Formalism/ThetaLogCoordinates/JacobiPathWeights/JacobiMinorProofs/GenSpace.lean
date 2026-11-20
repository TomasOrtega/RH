import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.GenSpaceFacts
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.ExistsSuppOfEvalNe

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

namespace GS

section Slices

variable {k : Type*} [Field k] {σ : Type*}
variable {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k D]

def slcFun (θ : A →ₗ[k] B) (P : MvPolynomial σ A) : MvPolynomial σ B :=
  ∑ e ∈ P.support, monomial e (θ (coeff e P))

/- English proof (translation)
Simplify using `only [slcFun, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]`. Use `split_ifs with h`. Both sides reduce to the same expression. Use `push Not at h`. Simplify using `[h]`.
-/
theorem coeff_slcFun (θ : A →ₗ[k] B) (P : MvPolynomial σ A) (e : σ →₀ ℕ) :
    coeff e (slcFun θ P) = θ (coeff e P) := by
  classical
  simp only [slcFun, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · push Not at h
    simp [h]

def slc (θ : A →ₗ[k] B) : MvPolynomial σ A →ₗ[k] MvPolynomial σ B where
  toFun := slcFun θ
  map_add' P Q := by
    ext e
    simp [coeff_slcFun]
  map_smul' c P := by
    ext e
    simp [coeff_slcFun]

/- English proof (translation)
The claim follows from `coeff_slcFun θ P e`.
-/
@[simp] theorem coeff_slc (θ : A →ₗ[k] B) (P : MvPolynomial σ A) (e : σ →₀ ℕ) :
    coeff e (slc θ P) = θ (coeff e P) := coeff_slcFun θ P e

/- English proof (translation)
Use extensionality with `e`. Simplify using the standard rewrite rules.
-/
theorem slc_comp (θ₁ : B →ₗ[k] D) (θ₂ : A →ₗ[k] B) (P : MvPolynomial σ A) :
    slc θ₁ (slc θ₂ P) = slc (θ₁ ∘ₗ θ₂) P := by
  ext e
  simp

/- English proof (translation)
Use extensionality with `e`. Simplify using `[coeff_map]`.
-/
theorem slc_algHom (θ : A →ₐ[k] B) (P : MvPolynomial σ A) :
    slc θ.toLinearMap P = map (θ : A →+* B) P := by
  ext e
  simp [coeff_map]

/- English proof (translation)
Use extensionality with `e`. Simplify using `only [coeff_slc, coeff_smul, coeff_map, smul_eq_mul]`. Rewrite using `[mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`.
-/
theorem slc_smul_map (ℓ : A →ₗ[k] k) (a : A) (f : MvPolynomial σ k) :
    slc ℓ (a • map (algebraMap k A) f) = ℓ a • f := by
  ext e
  simp only [coeff_slc, coeff_smul, coeff_map, smul_eq_mul]
  rw [mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Use extensionality with `e'`. Simplify using `only [coeff_slc, coeff_monomial]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem slc_monomial (θ : A →ₗ[k] B) (e : σ →₀ ℕ) (a : A) :
    slc θ (monomial e a) = monomial e (θ a) := by
  classical
  ext e'
  simp only [coeff_slc, coeff_monomial]
  split_ifs <;> simp

def slMap (P : MvPolynomial σ A) : (A →ₗ[k] k) →ₗ[k] MvPolynomial σ k where
  toFun ℓ := slc ℓ P
  map_add' ℓ ℓ' := by
    ext e
    simp
  map_smul' c ℓ := by
    ext e
    simp

def slSpace (P : MvPolynomial σ A) : Submodule k (MvPolynomial σ k) := LinearMap.range (slMap (k := k) P)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_slSpace {P : MvPolynomial σ A} {f : MvPolynomial σ k} :
    f ∈ slSpace (k := k) P ↔ ∃ ℓ : A →ₗ[k] k, slc ℓ P = f := Iff.rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨ℓ, rfl⟩`.
-/
theorem slc_mem_slSpace (P : MvPolynomial σ A) (ℓ : A →ₗ[k] k) : slc ℓ P ∈ slSpace (k := k) P := ⟨ℓ, rfl⟩

/- English proof (translation)
Take `⟨r, hr⟩` from `LinearMap.exists_leftInverse_of_injective θ.toLinearMap (LinearMap.ker_eq_bot.mpr hθ)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨ℓ, rfl⟩`. Use `⟨ℓ ∘ₗ θ.toLinearMap, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `slc _ _ = slc _ _`.

Rewrite using `[← slc_algHom, slc_comp]`. Introduce and unpack `_ ⟨ℓ, rfl⟩`. Use `⟨ℓ ∘ₗ r, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `slc _ _ = slc _ _`. Rewrite using `[← slc_algHom, slc_comp, LinearMap.comp_assoc, hr, LinearMap.comp_id]`.
-/
theorem slSpace_map (θ : A →ₐ[k] B) (hθ : Function.Injective θ) (P : MvPolynomial σ A) :
    slSpace (k := k) (map (θ : A →+* B) P) = slSpace (k := k) P := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective θ.toLinearMap (LinearMap.ker_eq_bot.mpr hθ)
  apply le_antisymm
  · rintro _ ⟨ℓ, rfl⟩
    refine ⟨ℓ ∘ₗ θ.toLinearMap, ?_⟩
    change slc _ _ = slc _ _
    rw [← slc_algHom, slc_comp]
  · rintro _ ⟨ℓ, rfl⟩
    refine ⟨ℓ ∘ₗ r, ?_⟩
    change slc _ _ = slc _ _
    rw [← slc_algHom, slc_comp, LinearMap.comp_assoc, hr, LinearMap.comp_id]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hP`. Introduce and unpack `_ ⟨ℓ, rfl⟩`. Express the relevant statement in the definitionally equal form `slc ℓ P ∈ N`. Proceed by induction on `hP using Submodule.span_induction generalizing ℓ with`.

Consider the case `mem x hx`. Take `⟨f, hf, rfl⟩` from `hx`. Use `slc_smul_map ℓ 1 f` as an intermediate fact. Rewrite `this` using `[one_smul]`. Rewrite using `[this]`.

Conclude with `N.smul_mem _ hf`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `N.add_mem (hx ℓ) (hy ℓ)`. Consider the case `smul a x _ hx`.

Establish `: slc ℓ (a • x) = slc (ℓ ∘ₗ LinearMap.mulLeft k a) x`. Use extensionality with `e`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `hx _`.

Introduce `h`. Set `b` to `Module.Basis.ofVectorSpace k A`. Set `I` to `P.support.biUnion fun e => (b.repr (coeff e P)).support`. Establish `key : P = ∑ i ∈ I, (b i) • map (algebraMap k A) (slc (b.coord i) P)`. Use extensionality with `e`.

Rewrite using `[coeff_sum]`. Simplify using `only [coeff_smul, coeff_map, coeff_slc, smul_eq_mul, Module.Basis.coord_apply]`. Establish `hsub : (b.repr (coeff e P)).support ⊆ I`. Distinguish the cases in `he : e ∈ P.support`. Conclude with `Finset.subset_biUnion_of_mem (fun e => (b.repr (coeff e P)).support) he`.

Rewrite using `[notMem_support_iff.mp he]`. Simplify using the standard rewrite rules. Use `conv_lhs => rw [← b.linearCombination_repr (coeff e P), Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ hsub (fun i a => a • b i) (fun i _ => zero_smul _ _)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`.

Rewrite using `[key]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Conclude with `⟨_, h (slc_mem_slSpace P _), rfl⟩`.
-/
theorem mem_span_iff (N : Submodule k (MvPolynomial σ k)) (P : MvPolynomial σ A) :
    P ∈ Submodule.span A ((fun f => map (algebraMap k A) f) '' (N : Set (MvPolynomial σ k))) ↔
      slSpace (k := k) P ≤ N := by
  classical
  constructor
  · intro hP
    rintro _ ⟨ℓ, rfl⟩
    change slc ℓ P ∈ N
    induction hP using Submodule.span_induction generalizing ℓ with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      have := slc_smul_map ℓ 1 f
      rw [one_smul] at this
      rw [this]
      exact N.smul_mem _ hf
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact N.add_mem (hx ℓ) (hy ℓ)
    | smul a x _ hx =>
      have : slc ℓ (a • x) = slc (ℓ ∘ₗ LinearMap.mulLeft k a) x := by
        ext e
        simp
      rw [this]
      exact hx _
  · intro h
    let b := Module.Basis.ofVectorSpace k A
    let I := P.support.biUnion fun e => (b.repr (coeff e P)).support
    have key : P = ∑ i ∈ I, (b i) • map (algebraMap k A) (slc (b.coord i) P) := by
      ext e
      rw [coeff_sum]
      simp only [coeff_smul, coeff_map, coeff_slc, smul_eq_mul, Module.Basis.coord_apply]
      have hsub : (b.repr (coeff e P)).support ⊆ I := by
        by_cases he : e ∈ P.support
        · exact Finset.subset_biUnion_of_mem (fun e => (b.repr (coeff e P)).support) he
        · rw [notMem_support_iff.mp he]
          simp
      conv_lhs => rw [← b.linearCombination_repr (coeff e P), Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ hsub (fun i a => a • b i) (fun i _ => zero_smul _ _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, mul_comm]
    rw [key]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨_, h (slc_mem_slSpace P _), rfl⟩

end Slices

section Sharp

variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
variable {A B : Type*} [CommRing A] [CommRing B]

/- English proof (translation)
Simplify using `[sharpHom]`.
-/
theorem sharp_C (g gi : Matrix (Fin n) (Fin n) A) (c : A) :
    sharpHom (ζ := ζ) isVec S g gi (C c) = C c := by
  simp [sharpHom]

variable {isVec S}

/- English proof (translation)
Simplify using `[sharpHom, h1, h3, Matrix.vecMul, dotProduct]`.
-/
theorem sharp_vec {i : ι} (h1 : i ∈ S) (h3 : isVec i = true) (g gi : Matrix (Fin n) (Fin n) A) (a : Fin n) :
    sharpHom (ζ := ζ) isVec S g gi (X (Sum.inl (i, a))) = ∑ b, X (Sum.inl (i, b)) * C (g b a) := by
  simp [sharpHom, h1, h3, Matrix.vecMul, dotProduct]

/- English proof (translation)
Simplify using `[sharpHom, h1, h3, Matrix.vecMul, dotProduct]`.
-/
theorem sharp_covec {i : ι} (h1 : i ∈ S) (h3 : isVec i = false) (g gi : Matrix (Fin n) (Fin n) A) (a : Fin n) :
    sharpHom (ζ := ζ) isVec S g gi (X (Sum.inl (i, a))) = ∑ b, X (Sum.inl (i, b)) * C (gi a b) := by
  simp [sharpHom, h1, h3, Matrix.vecMul, dotProduct]

/- English proof (translation)
Simplify using `[sharpHom, h1]`.
-/
theorem sharp_out {i : ι} (h1 : i ∉ S) (g gi : Matrix (Fin n) (Fin n) A) (a : Fin n) :
    sharpHom (ζ := ζ) isVec S g gi (X (Sum.inl (i, a))) = X (Sum.inl (i, a)) := by
  simp [sharpHom, h1]

variable (isVec S)

/- English proof (translation)
Simplify using `[sharpHom]`.
-/
theorem sharp_further (g gi : Matrix (Fin n) (Fin n) A) (z : ζ) :
    sharpHom (ι := ι) isVec S g gi (X (Sum.inr z)) = X (Sum.inr z) := by
  simp [sharpHom]

/- English proof (translation)
It suffices to establish `hh : (map θ).comp (sharpHom (ζ` using `ζ) isVec S g gi).toRingHom = (sharpHom (ζ := ζ) isVec S (g.map θ) (gi.map θ)).toRingHom.comp (map θ) from DFunLike.congr_fun hh P`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using the standard rewrite rules. Introduce and unpack `(⟨i, a⟩ | z)`.

Distinguish the cases in `h1 : i ∈ S`. Consider the cases of `h3 : isVec i`. Simplify using `[sharp_covec h1 h3]`. Simplify using `[sharp_vec h1 h3]`. Simplify using `[sharp_out h1]`.

Simplify using `[sharp_further]`.
-/
theorem sharp_nat (θ : A →+* B) (g gi : Matrix (Fin n) (Fin n) A) (P : MvPolynomial (LVar ι ζ n) A) :
    map θ (sharpHom isVec S g gi P) = sharpHom isVec S (g.map θ) (gi.map θ) (map θ P) := by
  suffices hh : (map θ).comp (sharpHom (ζ := ζ) isVec S g gi).toRingHom =
      (sharpHom (ζ := ζ) isVec S (g.map θ) (gi.map θ)).toRingHom.comp (map θ) from
    DFunLike.congr_fun hh P
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · rintro (⟨i, a⟩ | z)
    · by_cases h1 : i ∈ S
      · cases h3 : isVec i
        · simp [sharp_covec h1 h3]
        · simp [sharp_vec h1 h3]
      · simp [sharp_out h1]
    · simp [sharp_further]

/- English proof (translation)
It suffices to establish `hh : (sharpHom (ζ` using `ζ) isVec S x xi).comp (sharpHom isVec S y yi) = sharpHom isVec S (x * y) (yi * xi) from DFunLike.congr_fun hh P`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `(⟨i, a⟩ | z)`. Distinguish the cases in `h1 : i ∈ S`. Consider the cases of `h3 : isVec i`.

Simplify using `only [AlgHom.comp_apply, sharp_covec h1 h3, map_sum, map_mul, sharp_C, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [AlgHom.comp_apply, sharp_vec h1 h3, map_sum, map_mul, sharp_C, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Simplify using `[sharp_out h1]`. Simplify using `[sharp_further]`.
-/
theorem sharp_comp (x xi y yi : Matrix (Fin n) (Fin n) A) (P : MvPolynomial (LVar ι ζ n) A) :
    sharpHom isVec S x xi (sharpHom isVec S y yi P) = sharpHom isVec S (x * y) (yi * xi) P := by
  suffices hh : (sharpHom (ζ := ζ) isVec S x xi).comp (sharpHom isVec S y yi) =
      sharpHom isVec S (x * y) (yi * xi) from DFunLike.congr_fun hh P
  apply MvPolynomial.algHom_ext
  rintro (⟨i, a⟩ | z)
  · by_cases h1 : i ∈ S
    · cases h3 : isVec i
      · simp only [AlgHom.comp_apply, sharp_covec h1 h3, map_sum, map_mul, sharp_C, Matrix.mul_apply,
          Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        ring
      · simp only [AlgHom.comp_apply, sharp_vec h1 h3, map_sum, map_mul, sharp_C, Matrix.mul_apply,
          Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        ring
    · simp [sharp_out h1]
  · simp [sharp_further]

end Sharp

section Universal

/- English proof (translation)
Use `symm`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hm]`. Conclude with `Matrix.map_one f (map_zero f) (map_one f)`.
-/
theorem map_nonsing_inv {A B : Type*} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (m : Matrix (Fin n) (Fin n) A) (hm : IsUnit m.det) : (m⁻¹).map f = (m.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hm]
  exact Matrix.map_one f (map_zero f) (map_one f)

variable (k : Type*) [Field k] (n : ℕ)

def uDet : MvPolynomial (Fin n × Fin n) k := (Matrix.mvPolynomialX (Fin n) (Fin n) k).det

abbrev UR := Localization.Away (uDet k n)

def uMat : Matrix (Fin n) (Fin n) (UR k n) :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) k).map (algebraMap (MvPolynomial (Fin n × Fin n) k) (UR k n))

/- English proof (translation)
Establish `: (uMat k n).det = algebraMap (MvPolynomial (Fin n × Fin n) k) (UR k n) (uDet k n)`. Conclude with `(RingHom.map_det (algebraMap (MvPolynomial (Fin n × Fin n) k) (UR k n)) (Matrix.mvPolynomialX (Fin n) (Fin n) k)).symm`. Rewrite using `[this]`. Conclude with `IsLocalization.Away.algebraMap_isUnit _`.
-/
theorem uMat_det : IsUnit (uMat k n).det := by
  have : (uMat k n).det = algebraMap (MvPolynomial (Fin n × Fin n) k) (UR k n) (uDet k n) := by
    exact (RingHom.map_det (algebraMap (MvPolynomial (Fin n × Fin n) k) (UR k n))
      (Matrix.mvPolynomialX (Fin n) (Fin n) k)).symm
  rw [this]
  exact IsLocalization.Away.algebraMap_isUnit _

variable {k n}
variable {B : Type*} [CommRing B] [Algebra k B]

/- English proof (translation)
Unfold `uDet`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Conclude with `Matrix.mvPolynomialX_mapMatrix_aeval k g₀`.
-/
theorem eval_uDet (g₀ : Matrix (Fin n) (Fin n) B) :
    aeval (fun p : Fin n × Fin n => g₀ p.1 p.2) (uDet k n) = g₀.det := by
  unfold uDet
  rw [AlgHom.map_det]
  congr 1
  exact Matrix.mvPolynomialX_mapMatrix_aeval k g₀

def uAlg (k : Type*) [Field k] {n : ℕ} {B : Type*} [CommRing B] [Algebra k B]
    (g₀ : Matrix (Fin n) (Fin n) B) (h : IsUnit g₀.det) : UR k n →ₐ[k] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (uDet k n))
    (f := aeval (fun p : Fin n × Fin n => g₀ p.1 p.2))
    (by
      rintro ⟨_, m, rfl⟩
      rw [map_pow, eval_uDet]
      exact h.pow m)

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ _`.
-/
theorem uAlg_algebraMap (g₀ : Matrix (Fin n) (Fin n) B) (h : IsUnit g₀.det)
    (x : MvPolynomial (Fin n × Fin n) k) :
    uAlg k g₀ h (algebraMap _ _ x) = aeval (fun p : Fin n × Fin n => g₀ p.1 p.2) x :=
  IsLocalization.lift_eq _ _

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[uMat, uAlg_algebraMap, Matrix.mvPolynomialX]`.
-/
theorem uAlg_uMat (g₀ : Matrix (Fin n) (Fin n) B) (h : IsUnit g₀.det) :
    (uMat k n).map (uAlg k g₀ h : UR k n →+* B) = g₀ := by
  ext a b
  simp [uMat, uAlg_algebraMap, Matrix.mvPolynomialX]

/- English proof (translation)
Rewrite using `[map_nonsing_inv _ _ (uMat_det k n), uAlg_uMat]`.
-/
theorem uAlg_uInv (g₀ : Matrix (Fin n) (Fin n) B) (h : IsUnit g₀.det) :
    ((uMat k n)⁻¹).map (uAlg k g₀ h : UR k n →+* B) = g₀⁻¹ := by
  rw [map_nonsing_inv _ _ (uMat_det k n), uAlg_uMat]

/- English proof (translation)
Establish `: Function.Injective (uAlg k g₀ h : UR k n →+* B)`. Rewrite using `[IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (uDet k n))]`. Introduce `x y`. Simplify using `only [RingHom.coe_coe]`. Rewrite using `[uAlg_algebraMap, uAlg_algebraMap, hinj.eq_iff]`.

Use `(IsLocalization.injective (UR k n) (M := Submonoid.powers (uDet k n)) ?_).eq_iff` and prove the remaining obligations. Conclude with `powers_le_nonZeroDivisors_of_noZeroDivisors (Matrix.det_mvPolynomialX_ne_zero _ k)`. Conclude with `this`.
-/
theorem uAlg_injective (g₀ : Matrix (Fin n) (Fin n) B) (h : IsUnit g₀.det)
    (hinj : Function.Injective (aeval (R := k) (fun p : Fin n × Fin n => g₀ p.1 p.2))) :
    Function.Injective (uAlg k g₀ h) := by
  have : Function.Injective (uAlg k g₀ h : UR k n →+* B) := by
    rw [IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (uDet k n))]
    intro x y
    simp only [RingHom.coe_coe]
    rw [uAlg_algebraMap, uAlg_algebraMap, hinj.eq_iff]
    refine (IsLocalization.injective (UR k n) (M := Submonoid.powers (uDet k n)) ?_).eq_iff
    exact powers_le_nonZeroDivisors_of_noZeroDivisors (Matrix.det_mvPolynomialX_ne_zero _ k)
  exact this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem algebraMap_gen : algebraMap k (GenField k n) = genφ k n := rfl

/- English proof (translation)
The claim follows from `isUnit_iff_ne_zero.mpr (genMat_det_ne k n)`.
-/
theorem genMat_isUnit : IsUnit (genMat k n).det := isUnit_iff_ne_zero.mpr (genMat_det_ne k n)

/- English proof (translation)
Apply `uAlg_injective` to reduce the goal to its premises. Establish `: (aeval (R` using `k) (fun p : Fin n × Fin n => genMat k n p.1 p.2) : _ →+* GenField k n) = algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n) := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[algebraMap_gen]`.

Introduce `p`. Simplify using `[genMat]`. Introduce `x y hxy`. Establish `h1` using `DFunLike.congr_fun this x`. Establish `h2` using `DFunLike.congr_fun this y`.

Simplify using `only [RingHom.coe_coe] at h1 h2`. Rewrite `hxy` using `[h1, h2]`. Conclude with `IsFractionRing.injective _ (GenField k n) hxy`.
-/
theorem uAlg_gen_injective : Function.Injective (uAlg k (genMat k n) genMat_isUnit) := by
  apply uAlg_injective
  have : (aeval (R := k) (fun p : Fin n × Fin n => genMat k n p.1 p.2) : _ →+* GenField k n) =
      algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [algebraMap_gen]
    · intro p
      simp [genMat]
  intro x y hxy
  have h1 := DFunLike.congr_fun this x
  have h2 := DFunLike.congr_fun this y
  simp only [RingHom.coe_coe] at h1 h2
  rw [h1, h2] at hxy
  exact IsFractionRing.injective _ (GenField k n) hxy

end Universal

section Act

variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

def rho (G : MvPolynomial (LVar ι ζ n) k) : MvPolynomial (LVar ι ζ n) (UR k n) :=
  sharpHom isVec S (uMat k n) (uMat k n)⁻¹ (map (algebraMap k (UR k n)) G)

/- English proof (translation)
Rewrite using `[rho, sharp_nat, uAlg_uMat, uAlg_uInv, MvPolynomial.map_map, AlgHom.comp_algebraMap]`.
-/
theorem act_eq {B : Type*} [CommRing B] [Algebra k B] (g₀ : Matrix (Fin n) (Fin n) B) (h : IsUnit g₀.det)
    (G : MvPolynomial (LVar ι ζ n) k) :
    sharpHom isVec S g₀ g₀⁻¹ (map (algebraMap k B) G) = map (uAlg k g₀ h : UR k n →+* B) (rho isVec S G) := by
  rw [rho, sharp_nat, uAlg_uMat, uAlg_uInv, MvPolynomial.map_map, AlgHom.comp_algebraMap]

/- English proof (translation)
Rewrite using `[← act_eq, Matrix.mul_inv_rev, ← map_nonsing_inv _ _ (uMat_det k n), ← sharp_comp, rho, sharp_nat, MvPolynomial.map_map, AlgHom.comp_algebraMap]`.
-/
theorem sharp_map_rho {B : Type*} [CommRing B] [Algebra k B] (c : UR k n →ₐ[k] B)
    (x : Matrix (Fin n) (Fin n) B) (hxy : IsUnit (x * (uMat k n).map (c : UR k n →+* B)).det)
    (G : MvPolynomial (LVar ι ζ n) k) :
    sharpHom isVec S x x⁻¹ (map (c : UR k n →+* B) (rho isVec S G)) =
      map (uAlg k (x * (uMat k n).map (c : UR k n →+* B)) hxy : UR k n →+* B) (rho isVec S G) := by
  rw [← act_eq, Matrix.mul_inv_rev, ← map_nonsing_inv _ _ (uMat_det k n), ← sharp_comp, rho, sharp_nat, MvPolynomial.map_map,
    AlgHom.comp_algebraMap]

/- English proof (translation)
The claim follows from `act_eq isVec S (genMat k n) genMat_isUnit G`.
-/
theorem genPoint_eq (G : MvPolynomial (LVar ι ζ n) k) :
    genPoint isVec S G =
      map (uAlg k (genMat k n) genMat_isUnit : UR k n →+* GenField k n) (rho isVec S G) :=
  act_eq isVec S (genMat k n) genMat_isUnit G

/- English proof (translation)
Use `(mem_span_iff (A := GenField k n) N (genPoint isVec S G)).trans ?_` and prove the remaining obligations. Rewrite using `[genPoint_eq, slSpace_map _ uAlg_gen_injective]`.
-/
theorem carries_iff (G : MvPolynomial (LVar ι ζ n) k) (N : Submodule k (MvPolynomial (LVar ι ζ n) k)) :
    Carries isVec S G N ↔ slSpace (k := k) (rho isVec S G) ≤ N := by
  refine (mem_span_iff (A := GenField k n) N (genPoint isVec S G)).trans ?_
  rw [genPoint_eq, slSpace_map _ uAlg_gen_injective]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `sInf_le ((carries_iff isVec S G _).mpr le_rfl)`. Conclude with `le_sInf fun N hN => (carries_iff isVec S G N).mp hN`.
-/
theorem genSpace_eq (G : MvPolynomial (LVar ι ζ n) k) :
    genSpace isVec S G = slSpace (k := k) (rho isVec S G) := by
  apply le_antisymm
  · exact sInf_le ((carries_iff isVec S G _).mpr le_rfl)
  · exact le_sInf fun N hN => (carries_iff isVec S G N).mp hN

/- English proof (translation)
Rewrite using `[genSpace_eq]`. Conclude with `mem_slSpace`.
-/
theorem mem_genSpace {G f : MvPolynomial (LVar ι ζ n) k} :
    f ∈ genSpace isVec S G ↔ ∃ ℓ : UR k n →ₗ[k] k, slc ℓ (rho isVec S G) = f := by
  rw [genSpace_eq]
  exact mem_slSpace

def ev1 (k : Type*) [Field k] (n : ℕ) : UR k n →ₐ[k] k :=
  uAlg k (1 : Matrix (Fin n) (Fin n) k) (by simp)

end Act

section Torus

variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

def wV : LVar ι ζ n → (Fin n → ℤ)
  | Sum.inl (i, a) => if i ∈ S then (if isVec i then Pi.single a 1 else Pi.single a (-1)) else 0
  | Sum.inr _ => 0

abbrev wt (e : LVar ι ζ n →₀ ℕ) : Fin n → ℤ := Finsupp.weight (wV isVec S) e

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, hw]`.
-/
theorem weight_pi_apply {σ : Type*} (W : σ → Fin n → ℤ) (e : σ →₀ ℕ) (m : Fin n) (w : σ → ℤ)
    (hw : ∀ x, W x m = w x) : Finsupp.weight W e m = Finsupp.weight w e := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, hw]

/- English proof (translation)
The claim follows from `weight_pi_apply _ e m w hw`.
-/
theorem wt_apply (e : LVar ι ζ n →₀ ℕ) (m : Fin n) (w : LVar ι ζ n → ℤ) (hw : ∀ x, wV isVec S x m = w x) :
    wt isVec S e m = Finsupp.weight w e := weight_pi_apply _ e m w hw

/- English proof (translation)
The claim follows from `| Sum.inl (i, a) => if i ∈ S ∧ a = m then (if isVec i then (1 : ℤ) else -1) else 0 | Sum.inr _ => 0 := by rcases x with ⟨i, a⟩ | z · by_cases h1 : i ∈ S · by_cases h2 : a = m · subst h2 cases h3 : isVec i <;> simp [wV, h1, h3] · cases h3 : isVec i <;> simp [wV, h1, h2, h3, Ne.sym …`.
-/
theorem wV_apply (m : Fin n) (x : LVar ι ζ n) :
    wV isVec S x m = match x with
        | Sum.inl (i, a) => if i ∈ S ∧ a = m then (if isVec i then (1 : ℤ) else -1) else 0
        | Sum.inr _ => 0 := by
  rcases x with ⟨i, a⟩ | z
  · by_cases h1 : i ∈ S
    · by_cases h2 : a = m
      · subst h2
        cases h3 : isVec i <;> simp [wV, h1, h3]
      · cases h3 : isVec i <;> simp [wV, h1, h2, h3, Ne.symm h2]
    · simp [wV, h1]
  · simp [wV]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Use function extensionality and compare the values at `m`. Conclude with `(wt_apply isVec S d m _ (wV_apply isVec S m)).trans (h m hd)`. Introduce `h m d hd`.

Conclude with `(wt_apply isVec S d m _ (wV_apply isVec S m)).symm.trans (congrFun (h hd) m)`.
-/
theorem hasWeight_iff {k : Type*} [Field k] (f : MvPolynomial (LVar ι ζ n) k) (ν : Fin n → ℤ) :
    HasWeight isVec S f ν ↔ IsWeightedHomogeneous (wV isVec S) f ν := by
  constructor
  · intro h d hd
    funext m
    exact (wt_apply isVec S d m _ (wV_apply isVec S m)).trans (h m hd)
  · intro h m d hd
    exact (wt_apply isVec S d m _ (wV_apply isVec S m)).symm.trans (congrFun (h hd) m)

variable (A : Type*) [CommRing A]

abbrev TR (n : ℕ) := AddMonoidAlgebra A (Fin n → ℤ)

def dt (n : ℕ) : Matrix (Fin n) (Fin n) (TR A n) :=
  Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a 1) 1

def dti (n : ℕ) : Matrix (Fin n) (Fin n) (TR A n) :=
  Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (-1)) 1

/- English proof (translation)
Rewrite using `[dt, dti, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[AddMonoidAlgebra.single_mul_single, ← Pi.single_add, mul_one, AddMonoidAlgebra.one_def]`. Simplify using the standard rewrite rules.
-/
theorem dt_mul_dti : dt A n * dti A n = 1 := by
  rw [dt, dti, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [AddMonoidAlgebra.single_mul_single, ← Pi.single_add, mul_one, AddMonoidAlgebra.one_def]
  simp

/- English proof (translation)
The claim follows from `(Matrix.inv_eq_right_inv (dt_mul_dti A)).symm`.
-/
theorem dti_eq : dti A n = (dt A n)⁻¹ := (Matrix.inv_eq_right_inv (dt_mul_dti A)).symm

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_right_inverse (dt_mul_dti A)`.
-/
theorem dt_det : IsUnit (dt A n).det := Matrix.isUnit_det_of_right_inverse (dt_mul_dti A)

variable {A}

/- English proof (translation)
Break down `x with ⟨i, a⟩ | z` into its components or cases. Distinguish the cases in `h1 : i ∈ S`. Consider the cases of `h3 : isVec i`. Rewrite using `[sharp_covec h1 h3]`. Simplify using `[dti, Matrix.diagonal_apply, wV, h1, h3, mul_comm, apply_ite C]`.

Rewrite using `[sharp_vec h1 h3]`. Simplify using `[dt, Matrix.diagonal_apply, wV, h1, h3, mul_comm, apply_ite C]`. Rewrite using `[sharp_out h1]`. Simplify using `[wV, h1, ← AddMonoidAlgebra.one_def]`. Rewrite using `[sharp_further]`.

Simplify using `[wV, ← AddMonoidAlgebra.one_def]`.
-/
theorem torus_X (x : LVar ι ζ n) :
    sharpHom isVec S (dt A n) (dti A n) (X x) = C (AddMonoidAlgebra.single (wV isVec S x) 1) * X x := by
  classical
  rcases x with ⟨i, a⟩ | z
  · by_cases h1 : i ∈ S
    · cases h3 : isVec i
      · rw [sharp_covec h1 h3]
        simp [dti, Matrix.diagonal_apply, wV, h1, h3, mul_comm, apply_ite C]
      · rw [sharp_vec h1 h3]
        simp [dt, Matrix.diagonal_apply, wV, h1, h3, mul_comm, apply_ite C]
    · rw [sharp_out h1]
      simp [wV, h1, ← AddMonoidAlgebra.one_def]
  · rw [sharp_further]
    simp [wV, ← AddMonoidAlgebra.one_def]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [AddMonoidAlgebra.one_def]`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ih, AddMonoidAlgebra.single_mul_single, mul_one]`.
-/
theorem prod_single {κ M : Type*} [AddCommMonoid M] (s : Finset κ) (f : κ → M) :
    ∏ x ∈ s, (AddMonoidAlgebra.single (f x) (1 : A) : AddMonoidAlgebra A M) =
      AddMonoidAlgebra.single (∑ x ∈ s, f x) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, AddMonoidAlgebra.single_mul_single, mul_one]

/- English proof (translation)
Rewrite using `[monomial_eq, monomial_eq (a := AddMonoidAlgebra.single (wt isVec S e) a), map_mul, sharp_C, Finsupp.prod, map_prod]`. Simplify using `only [map_pow, torus_X, mul_pow, Finset.prod_mul_distrib, ← C_pow, AddMonoidAlgebra.single_pow, one_pow]`. Rewrite using `[← map_prod C, prod_single, ← mul_assoc, ← C_mul, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]`. Both sides reduce to the same expression.
-/
theorem torus_monomial (e : LVar ι ζ n →₀ ℕ) (a : A) :
    sharpHom isVec S (dt A n) (dti A n) (monomial e (AddMonoidAlgebra.single 0 a)) =
      monomial e (AddMonoidAlgebra.single (wt isVec S e) a) := by
  rw [monomial_eq, monomial_eq (a := AddMonoidAlgebra.single (wt isVec S e) a), map_mul, sharp_C, Finsupp.prod,
    map_prod]
  simp only [map_pow, torus_X, mul_pow, Finset.prod_mul_distrib, ← C_pow, AddMonoidAlgebra.single_pow, one_pow]
  rw [← map_prod C, prod_single, ← mul_assoc, ← C_mul, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  rfl

variable {k : Type*} [Field k] [Algebra k A]

def cf (ν : Fin n → ℤ) : TR A n →ₗ[k] A where
  toFun y := y.coeff ν
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `monomial e a`. Establish `: algebraMap A (TR A n) a = AddMonoidAlgebra.single 0 a` using `rfl`. Rewrite using `[map_monomial, this, torus_monomial, slc_monomial]`. Use extensionality with `d`.

Rewrite using `[coeff_weightedHomogeneousComponent, coeff_monomial, coeff_monomial]`. Distinguish the cases in `hd : e = d`. Substitute `hd` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`. Express the relevant statement in the definitionally equal form `(AddMonoidAlgebra.single (wt isVec S e) a).coeff ν = _`.

Rewrite using `[AddMonoidAlgebra.coeff_single, Finsupp.single_apply]`. Simplify using `[hd]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
-/
theorem torus_slice (Q : MvPolynomial (LVar ι ζ n) A) (ν : Fin n → ℤ) :
    slc (cf (k := k) ν) (sharpHom isVec S (dt A n) (dti A n) (map (algebraMap A (TR A n)) Q)) =
      weightedHomogeneousComponent (wV isVec S) ν Q := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial e a =>
    have : algebraMap A (TR A n) a = AddMonoidAlgebra.single 0 a := rfl
    rw [map_monomial, this, torus_monomial, slc_monomial]
    ext d
    rw [coeff_weightedHomogeneousComponent, coeff_monomial, coeff_monomial]
    by_cases hd : e = d
    · subst hd
      rw [if_pos rfl, if_pos rfl]
      change (AddMonoidAlgebra.single (wt isVec S e) a).coeff ν = _
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    · simp [hd]
  | add p q hp hq => simp only [map_add, hp, hq]

/- English proof (translation)
Use extensionality with `d`. Simplify using `only [coeff_weightedHomogeneousComponent, coeff_slc]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem whc_slc (ℓ : A →ₗ[k] k) (P : MvPolynomial (LVar ι ζ n) A) (ν : Fin n → ℤ) :
    weightedHomogeneousComponent (wV isVec S) ν (slc ℓ P) =
      slc ℓ (weightedHomogeneousComponent (wV isVec S) ν P) := by
  classical
  ext d
  simp only [coeff_weightedHomogeneousComponent, coeff_slc]
  split_ifs <;> simp

end Torus

section Weights

variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

def cT (k : Type*) [Field k] (n : ℕ) : UR k n →ₐ[k] TR (UR k n) n :=
  IsScalarTower.toAlgHom k (UR k n) (TR (UR k n) n)

/- English proof (translation)
Rewrite using `[Matrix.det_mul]`. Use `(dt_det _).mul ?_` and prove the remaining obligations. Establish `: ((uMat k n).map (cT k n : UR k n →+* TR (UR k n) n)).det = (cT k n : UR k n →+* TR (UR k n) n) (uMat k n).det` using `(RingHom.map_det _ _).symm`. Rewrite using `[this]`. Conclude with `(uMat_det k n).map _`.
-/
theorem cT_det : IsUnit (dt (UR k n) n * (uMat k n).map (cT k n : UR k n →+* TR (UR k n) n)).det := by
  rw [Matrix.det_mul]
  refine (dt_det _).mul ?_
  have : ((uMat k n).map (cT k n : UR k n →+* TR (UR k n) n)).det =
      (cT k n : UR k n →+* TR (UR k n) n) (uMat k n).det := (RingHom.map_det _ _).symm
  rw [this]
  exact (uMat_det k n).map _

def prF (k : Type*) [Field k] (n : ℕ) (ν : Fin n → ℤ) : UR k n →ₗ[k] UR k n :=
  cf ν ∘ₗ (uAlg k _ (cT_det (k := k) (n := n))).toLinearMap

/- English proof (translation)
Rewrite using `[← torus_slice (k := k) isVec S, dti_eq]`. Use `sharp_map_rho isVec S (cT k n) (dt _ n) cT_det G` as an intermediate fact. Express the relevant statement in the definitionally equal form `slc _ (sharpHom isVec S _ _ (map (cT k n : UR k n →+* TR (UR k n) n) _)) = _`. Rewrite using `[this, ← slc_algHom, slc_comp]`. Both sides reduce to the same expression.
-/
theorem whc_rho (G : MvPolynomial (LVar ι ζ n) k) (ν : Fin n → ℤ) :
    weightedHomogeneousComponent (wV isVec S) ν (rho isVec S G) = slc (prF k n ν) (rho isVec S G) := by
  rw [← torus_slice (k := k) isVec S, dti_eq]
  have := sharp_map_rho isVec S (cT k n) (dt _ n) cT_det G
  change slc _ (sharpHom isVec S _ _ (map (cT k n : UR k n →+* TR (UR k n) n) _)) = _
  rw [this, ← slc_algHom, slc_comp]
  rfl

/- English proof (translation)
Take `⟨ℓ, rfl⟩` from `(mem_genSpace isVec S).mp hf`. Rewrite using `[whc_slc, whc_rho, slc_comp]`. Conclude with `(mem_genSpace isVec S).mpr ⟨_, rfl⟩`.
-/
theorem whc_mem {G f : MvPolynomial (LVar ι ζ n) k} (hf : f ∈ genSpace isVec S G) (ν : Fin n → ℤ) :
    weightedHomogeneousComponent (wV isVec S) ν f ∈ genSpace isVec S G := by
  obtain ⟨ℓ, rfl⟩ := (mem_genSpace isVec S).mp hf
  rw [whc_slc, whc_rho, slc_comp]
  exact (mem_genSpace isVec S).mpr ⟨_, rfl⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, hne, hw⟩`. Take `⟨ℓ, rfl⟩` from `(mem_genSpace isVec S).mp hf`. Take `⟨e, he⟩` from `MvPolynomial.ne_zero_iff.mp hne`. Use `⟨e, ?_, (hasWeight_iff isVec S _ _).mp hw he⟩` and prove the remaining obligations.

Rewrite using `[mem_support_iff]`. Introduce `h0`. Rewrite `he` using `[coeff_slc, h0, map_zero]`. Conclude with `he rfl`. Introduce and unpack `⟨e, he, rfl⟩`.

Rewrite `he` using `[mem_support_iff]`. Choose the witnesses or unpack the hypotheses as in `⟨ℓ, hℓ⟩ : ∃ ℓ : UR k n →ₗ[k] k, ℓ (coeff e (rho isVec S G)) ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `he ((Module.forall_dual_apply_eq_zero_iff k _).mp hc)`.

Use `⟨weightedHomogeneousComponent (wV isVec S) (wt isVec S e) (slc ℓ (rho isVec S G)), whc_mem isVec S ((mem_genSpace isVec S).mpr ⟨ℓ, rfl⟩) _, ?_, (hasWeight_iff isVec S _ _).mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩` and prove the remaining obligations. Use `MvPolynomial.ne_zero_iff.mpr ⟨e, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_weightedHomogeneousComponent, if_pos rfl, coeff_slc]`. Conclude with `hℓ`.
-/
theorem isWeightOf_iff (G : MvPolynomial (LVar ι ζ n) k) (ν : Fin n → ℤ) :
    IsWeightOf isVec S (genSpace isVec S G) ν ↔ ∃ e ∈ (rho isVec S G).support, wt isVec S e = ν := by
  classical
  constructor
  · rintro ⟨f, hf, hne, hw⟩
    obtain ⟨ℓ, rfl⟩ := (mem_genSpace isVec S).mp hf
    obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.mp hne
    refine ⟨e, ?_, (hasWeight_iff isVec S _ _).mp hw he⟩
    rw [mem_support_iff]
    intro h0
    rw [coeff_slc, h0, map_zero] at he
    exact he rfl
  · rintro ⟨e, he, rfl⟩
    rw [mem_support_iff] at he
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : UR k n →ₗ[k] k, ℓ (coeff e (rho isVec S G)) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact he ((Module.forall_dual_apply_eq_zero_iff k _).mp hc)
    refine ⟨weightedHomogeneousComponent (wV isVec S) (wt isVec S e) (slc ℓ (rho isVec S G)),
      whc_mem isVec S ((mem_genSpace isVec S).mpr ⟨ℓ, rfl⟩) _, ?_,
      (hasWeight_iff isVec S _ _).mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩
    refine MvPolynomial.ne_zero_iff.mpr ⟨e, ?_⟩
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_slc]
    exact hℓ

def pm (k : Type*) [Field k] {n : ℕ} (π : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) k :=
  Matrix.of fun b a => if π b = a then 1 else 0

def pv (π : Equiv.Perm (Fin n)) : LVar ι ζ n → LVar ι ζ n
  | Sum.inl (i, a) => if i ∈ S then Sum.inl (i, π⁻¹ a) else Sum.inl (i, a)
  | Sum.inr z => Sum.inr z

end Weights

section Exponents

variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

def ant (k : Type*) [Field k] (n : ℕ) : UR k n →ₐ[k] UR k n :=
  uAlg k (uMat k n)⁻¹ (Matrix.isUnit_nonsing_inv_det _ (uMat_det k n))

/- English proof (translation)
Rewrite using `[ant, ← act_eq, Matrix.nonsing_inv_nonsing_inv _ (uMat_det k n)]`.
-/
theorem map_ant_rho (G : MvPolynomial (LVar ι ζ n) k) :
    map (ant k n : UR k n →+* UR k n) (rho isVec S G) =
      sharpHom isVec S (uMat k n)⁻¹ (uMat k n) (map (algebraMap k (UR k n)) G) := by
  rw [ant, ← act_eq, Matrix.nonsing_inv_nonsing_inv _ (uMat_det k n)]

/- English proof (translation)
Rewrite using `[map_ant_rho, sharp_nat, ant, uAlg_uInv, uAlg_uMat, Matrix.nonsing_inv_nonsing_inv _ (uMat_det k n), MvPolynomial.map_map, AlgHom.comp_algebraMap]`. Both sides reduce to the same expression.
-/
theorem map_ant_ant (G : MvPolynomial (LVar ι ζ n) k) :
    map (ant k n : UR k n →+* UR k n) (map (ant k n : UR k n →+* UR k n) (rho isVec S G)) = rho isVec S G := by
  rw [map_ant_rho, sharp_nat, ant, uAlg_uInv, uAlg_uMat, Matrix.nonsing_inv_nonsing_inv _ (uMat_det k n),
    MvPolynomial.map_map, AlgHom.comp_algebraMap]
  rfl

/- English proof (translation)
Rewrite using `[map_ant_rho, sharp_nat, uAlg_uInv, uAlg_uMat, MvPolynomial.map_map, AlgHom.comp_algebraMap]`. Both sides reduce to the same expression.
-/
theorem genH_eq (G : MvPolynomial (LVar ι ζ n) k) :
    genH isVec S G = map (uAlg k (genMat k n) genMat_isUnit : UR k n →+* GenField k n)
      (map (ant k n : UR k n →+* UR k n) (rho isVec S G)) := by
  rw [map_ant_rho, sharp_nat, uAlg_uInv, uAlg_uMat, MvPolynomial.map_map, AlgHom.comp_algebraMap]
  rfl

/- English proof (translation)
Rewrite using `[mem_support_iff, mem_support_iff, genH_eq, coeff_map, coeff_map]`. Prove the components needed by the constructor for the conclusion. Introduce `h h0`. Rewrite `h` using `[h0, map_zero, map_zero]`. Conclude with `h rfl`.

Introduce `h h0`. Apply `h` to reduce the goal to its premises. Establish `h1 : (ant k n : UR k n →+* UR k n) (coeff e (rho isVec S G)) = 0`. Apply `uAlg_gen_injective` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Conclude with `h0`. Establish `h2` using `congrArg (coeff e) (map_ant_ant isVec S G)`. Rewrite `h2` using `[coeff_map, coeff_map, h1, map_zero]`. Conclude with `h2.symm`.
-/
theorem genH_support (G : MvPolynomial (LVar ι ζ n) k) (e : LVar ι ζ n →₀ ℕ) :
    e ∈ (genH isVec S G).support ↔ e ∈ (rho isVec S G).support := by
  rw [mem_support_iff, mem_support_iff, genH_eq, coeff_map, coeff_map]
  constructor
  · intro h h0
    rw [h0, map_zero, map_zero] at h
    exact h rfl
  · intro h h0
    apply h
    have h1 : (ant k n : UR k n →+* UR k n) (coeff e (rho isVec S G)) = 0 := by
      apply uAlg_gen_injective
      rw [map_zero]
      exact h0
    have h2 := congrArg (coeff e) (map_ant_ant isVec S G)
    rw [coeff_map, coeff_map, h1, map_zero] at h2
    exact h2.symm

/- English proof (translation)
Rewrite using `[wV_apply]`. Break down `x with ⟨i, a⟩ | z` into its components or cases. Establish `hc : (if last then a.val + 1 = n else a.val = 0) ↔ a = m`. Consider the cases of `last`. Simplify using `only [Bool.false_eq_true, if_false] at hm ⊢`.

Rewrite using `[Fin.ext_iff, hm]`. Simplify using `only [if_true] at hm ⊢`. Rewrite using `[Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `by_cases h1 : i ∈ S <;> by_cases h2 : a = m <;> simp [wtX, h1, h2, hc, hm]`.

Simplify using `[wtX]`.
-/
theorem wV_eq_wtX (last : Bool) (m : Fin n) (hm : if last then m.val + 1 = n else m.val = 0) (x : LVar ι ζ n) :
    wV isVec S x m = wtX isVec S last x := by
  rw [wV_apply]
  rcases x with ⟨i, a⟩ | z
  · have hc : (if last then a.val + 1 = n else a.val = 0) ↔ a = m := by
      cases last
      · simp only [Bool.false_eq_true, if_false] at hm ⊢
        rw [Fin.ext_iff, hm]
      · simp only [if_true] at hm ⊢
        rw [Fin.ext_iff]
        omega
    by_cases h1 : i ∈ S <;> by_cases h2 : a = m <;> simp [wtX, h1, h2, hc, hm]
  · simp [wtX]

/- English proof (translation)
Rewrite using `[wt_apply isVec S e m _ (wV_eq_wtX isVec S last m hm), Finsupp.weight_apply, wExp, Finsupp.sum]`. Simplify using the standard rewrite rules.
-/
theorem wExp_eq_wt (last : Bool) (m : Fin n) (hm : if last then m.val + 1 = n else m.val = 0)
    (e : LVar ι ζ n →₀ ℕ) : wExp isVec S last e = wt isVec S e m := by
  rw [wt_apply isVec S e m _ (wV_eq_wtX isVec S last m hm), Finsupp.weight_apply, wExp, Finsupp.sum]
  simp

/- English proof (translation)
Rewrite using `[gen_mem_supp]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, he, hj⟩`. Conclude with `⟨wt isVec S e, (isWeightOf_iff isVec S G _).mpr ⟨e, (genH_support isVec S G e).mp he, rfl⟩, (wExp_eq_wt isVec S last m hm e).symm.trans hj⟩`. Introduce and unpack `⟨ν, hν, hj⟩`.

Take `⟨e, he, rfl⟩` from `(isWeightOf_iff isVec S G _).mp hν`. Conclude with `⟨e, (genH_support isVec S G e).mpr he, (wExp_eq_wt isVec S last m hm e).trans hj⟩`.
-/
theorem mem_supp_iff (last : Bool) (m : Fin n) (hm : if last then m.val + 1 = n else m.val = 0)
    (G : MvPolynomial (LVar ι ζ n) k) (j : ℤ) :
    j ∈ (genAct k isVec S last G).coeff.support ↔ ∃ ν, IsWeightOf isVec S (genSpace isVec S G) ν ∧ ν m = j := by
  rw [gen_mem_supp]
  constructor
  · rintro ⟨e, he, hj⟩
    exact ⟨wt isVec S e, (isWeightOf_iff isVec S G _).mpr ⟨e, (genH_support isVec S G e).mp he, rfl⟩,
      (wExp_eq_wt isVec S last m hm e).symm.trans hj⟩
  · rintro ⟨ν, hν, hj⟩
    obtain ⟨e, he, rfl⟩ := (isWeightOf_iff isVec S G _).mp hν
    exact ⟨e, (genH_support isVec S G e).mpr he, (wExp_eq_wt isVec S last m hm e).trans hj⟩

variable (φ : MvPolynomial (LVar ι ζ n) k →ₗ[k] MvPolynomial (LVar ι ζ n) k)
  (φL : MvPolynomial (LVar ι ζ n) (GenField k n) →ₗ[GenField k n] MvPolynomial (LVar ι ζ n) (GenField k n))
  (h1 : ∀ f, φL (map (genφ k n) f) = map (genφ k n) (φ f))
  (h2 : ∀ f, genPoint isVec S (φ f) = φL (genPoint isVec S f))

include h1 h2

end Exponents

end GS

open GS

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
