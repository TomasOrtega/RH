import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action

namespace GroundTheory.Global

open IsDedekindDomain NumberField AdeleBaseChange
open scoped NumberField.AdeleRing

noncomputable section

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  {ι : Type*} [Fintype ι]

omit [NumberField K] [NumberField L] [NumberField M] in

/- English proof (translation)
Introduce `h`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 h`. Apply `hv0` to reduce the goal to its premises. Set `χ : ι → (L →* M)` to `fun i ↦ ((τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M) : L →+* M).toMonoidHom`. Establish `hχ : Function.Injective χ`.

Introduce `i j hij`. Apply `hτ` to reduce the goal to its premises. Use extensionality with `x`. Conclude with `DFunLike.congr_fun hij x`. Establish `hli` using `(linearIndependent_monoidHom L M).comp χ hχ`.

Set `f : L →ₗ[K] M` to `∑ i, LinearMap.mulLeft K (v i) ∘ₗ ((τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M)).toLinearMap`. Establish `hf : f = 0`. Use `b.ext fun j ↦ ?_` and prove the remaining obligations. Establish `hj` using `congrFun hv j`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hj`.

Simplify `hj` using `[f]`. Establish `hsum : ∑ i, v i • ((χ i : L →* M) : L → M) = 0`. Use function extensionality and compare the values at `x`. Establish `hx` using `LinearMap.congr_fun hf x`. Simplify `hx` using `[f, χ]`.

Use function extensionality and compare the values at `i`. Conclude with `(Fintype.linearIndependent_iff.1 hli) v hsum i`.
-/
theorem det_conjugates_ne_zero [DecidableEq ι] (τ : ι → (M ≃ₐ[K] M))
    (hτ : Function.Injective fun i ↦ (τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M))
    (b : Module.Basis ι K L) :
    (Matrix.of fun i j ↦ τ i (algebraMap L M (b j))).det ≠ 0 := by
  classical
  intro h
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h
  apply hv0
  let χ : ι → (L →* M) := fun i ↦
    ((τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M) : L →+* M).toMonoidHom
  have hχ : Function.Injective χ := by
    intro i j hij
    apply hτ
    ext x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom L M).comp χ hχ
  let f : L →ₗ[K] M := ∑ i, LinearMap.mulLeft K (v i) ∘ₗ
    ((τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M)).toLinearMap
  have hf : f = 0 := by
    refine b.ext fun j ↦ ?_
    have hj := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hj
    simpa [f] using hj
  have hsum : ∑ i, v i • ((χ i : L →* M) : L → M) = 0 := by
    funext x
    have hx := LinearMap.congr_fun hf x
    simpa [f, χ] using hx
  funext i
  exact (Fintype.linearIndependent_iff.1 hli) v hsum i

/- English proof (translation)
Set `b : Module.Basis ι K L` to `(Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hcard).symm`. Set `B` to `adeleBasis b`. Set `A` to `Algebra.leftMulMatrix B y`. Set `D : Matrix ι ι M` to `Matrix.of fun i j ↦ τ i (algebraMap L M (b j))`. Establish `hA : ∀ k j, A k j = B.repr (y * B j) k` using `fun k j ↦ Algebra.leftMulMatrix_eq_repr_mul B y k j`.

Establish `hy : ∀ j, y * algebraMap L 𝔸[L] (b j) = ∑ k, adeleMap K L (A k j) * algebraMap L 𝔸[L] (b k)`. Introduce `j`. Use `conv_lhs => rw [← B.sum_repr (y * algebraMap L 𝔸[L] (b j))]`. Use `Finset.sum_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, algebraMap_adeleRing, adeleBasis_apply, hA, adeleBasis_apply]`.

Establish `key : Matrix.diagonal (fun i ↦ τ i • adeleMap L M y) * D.map (algebraMap M 𝔸[M]) = D.map (algebraMap M 𝔸[M]) * A.map (adeleMap K M)`. Use extensionality with `i j`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_apply]`. Establish `h` using `congrArg (fun z ↦ τ i • adeleMap L M z) (hy j)`. Simplify using `only [map_mul, map_sum, smul_mul', Finset.smul_sum, adeleMap_algebraMap, adeleMap_adeleMap, AdeleBaseChange.smul_algebraMap, smul_adeleMap] at h`.

Simplify using `only [Matrix.map_apply, Matrix.of_apply, D, h]`. Conclude with `Finset.sum_congr rfl fun k _ ↦ mul_comm _ _`. Establish `hdet` using `congrArg Matrix.det key`. Rewrite `hdet` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det]`. Rewrite using `[Algebra.norm_eq_matrix_det B]`.

Rewrite `hdet` using `[mul_comm]`. Establish `hu : IsUnit (algebraMap M 𝔸[M] D.det)` using `(isUnit_iff_ne_zero.2 (det_conjugates_ne_zero τ hτ b)).map _`. Conclude with `(hu.mul_left_cancel hdet).symm`.
-/
theorem adeleMap_norm_eq_prod (τ : ι → (M ≃ₐ[K] M))
    (hτ : Function.Injective fun i ↦ (τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M))
    (hcard : Fintype.card ι = Module.finrank K L) (y : 𝔸[L]) :
    adeleMap K M (Algebra.norm 𝔸[K] y) = ∏ i, τ i • adeleMap L M y := by
  classical
  let b : Module.Basis ι K L :=
    (Module.finBasis K L).reindex (Fintype.equivFinOfCardEq hcard).symm
  let B := adeleBasis b
  let A := Algebra.leftMulMatrix B y
  let D : Matrix ι ι M := Matrix.of fun i j ↦ τ i (algebraMap L M (b j))
  have hA : ∀ k j, A k j = B.repr (y * B j) k := fun k j ↦
    Algebra.leftMulMatrix_eq_repr_mul B y k j
  have hy : ∀ j, y * algebraMap L 𝔸[L] (b j) =
      ∑ k, adeleMap K L (A k j) * algebraMap L 𝔸[L] (b k) := by
    intro j
    conv_lhs => rw [← B.sum_repr (y * algebraMap L 𝔸[L] (b j))]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Algebra.smul_def, algebraMap_adeleRing, adeleBasis_apply, hA, adeleBasis_apply]
  have key : Matrix.diagonal (fun i ↦ τ i • adeleMap L M y) * D.map (algebraMap M 𝔸[M]) =
      D.map (algebraMap M 𝔸[M]) * A.map (adeleMap K M) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
    have h := congrArg (fun z ↦ τ i • adeleMap L M z) (hy j)
    simp only [map_mul, map_sum, smul_mul', Finset.smul_sum, adeleMap_algebraMap,
      adeleMap_adeleMap, AdeleBaseChange.smul_algebraMap, smul_adeleMap] at h
    simp only [Matrix.map_apply, Matrix.of_apply, D, h]
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det] at hdet
  rw [Algebra.norm_eq_matrix_det B]
  rw [mul_comm] at hdet
  have hu : IsUnit (algebraMap M 𝔸[M] D.det) :=
    (isUnit_iff_ne_zero.2 (det_conjugates_ne_zero τ hτ b)).map _
  exact (hu.mul_left_cancel hdet).symm

/- English proof (translation)
The claim follows from `Units.ext (by rw [coe_ideleEmbedding, coe_ideleNorm, adeleMap_norm_eq_prod τ hτ hcard, Units.coe_prod] rfl)`.
-/
theorem ideleEmbedding_ideleNorm_eq_prod (τ : ι → (M ≃ₐ[K] M))
    (hτ : Function.Injective fun i ↦ (τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M))
    (hcard : Fintype.card ι = Module.finrank K L) (x : IdeleGroup L) :
    ideleEmbedding K M (ideleNorm K L x) = ∏ i, τ i • ideleEmbedding L M x :=
  Units.ext (by
    rw [coe_ideleEmbedding, coe_ideleNorm, adeleMap_norm_eq_prod τ hτ hcard, Units.coe_prod]
    rfl)

/- English proof (translation)
Take `⟨x, rfl⟩` from `IdeleClassGroup.mk_surjective L c`. Simplify using `only [ideleClassNorm_mk, ideleClassMap_mk, ideleEmbedding_ideleNorm_eq_prod τ hτ hcard, smul_mk, map_prod]`.
-/
theorem ideleClassMap_ideleClassNorm_eq_prod (τ : ι → (M ≃ₐ[K] M))
    (hτ : Function.Injective fun i ↦ (τ i : M →ₐ[K] M).comp (IsScalarTower.toAlgHom K L M))
    (hcard : Fintype.card ι = Module.finrank K L) (c : IdeleClassGroup L) :
    ideleClassMap K M (ideleClassNorm K L c) = ∏ i, τ i • ideleClassMap L M c := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L c
  simp only [ideleClassNorm_mk, ideleClassMap_mk, ideleEmbedding_ideleNorm_eq_prod τ hτ hcard,
    smul_mk, map_prod]

end

end GroundTheory.Global
