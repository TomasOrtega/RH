import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul k e`. Simplify using `only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]`. Consider the case `add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]`.
-/
theorem tensor_repr_map {ι : Type} (b : Module.Basis ι F E) {K K' : Type} [CommRing K] [Algebra F K]
    [CommRing K'] [Algebra F K'] (φ : K →ₐ[F] K') (y : K ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis K' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) y) i =
      φ ((Algebra.TensorProduct.basis K b).repr y i) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul k e =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis F E`. Rewrite using `[Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K' b), Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K b)]`. Rewrite using `[show (φ : K → K') = φ.toRingHom from rfl, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply]`. Establish `h1 : (1 : K') ⊗ₜ[F] b j = Algebra.TensorProduct.map φ (AlgHom.id F E) ((1 : K) ⊗ₜ[F] b j)`. Simplify using the standard rewrite rules. Rewrite using `[h1, ← map_mul, tensor_repr_map b φ]`. Both sides reduce to the same expression.
-/
theorem tensor_norm_map [FiniteDimensional F E] {K K' : Type} [CommRing K] [Algebra F K]
    [CommRing K'] [Algebra F K'] (φ : K →ₐ[F] K') (y : K ⊗[F] E) :
    Algebra.norm K' (Algebra.TensorProduct.map φ (AlgHom.id F E) y) = φ (Algebra.norm K y) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K' b),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K b)]
  rw [show (φ : K → K') = φ.toRingHom from rfl, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.basis_apply]
  have h1 : (1 : K') ⊗ₜ[F] b j = Algebra.TensorProduct.map φ (AlgHom.id F E) ((1 : K) ⊗ₜ[F] b j) := by
    simp
  rw [h1, ← map_mul, tensor_repr_map b φ]
  rfl

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis F E`. Rewrite using `[Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K b), Algebra.norm_eq_matrix_det b, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul]`.

Simplify using the standard rewrite rules.
-/
theorem tensor_norm_one_tmul [FiniteDimensional F E] (K : Type) [CommRing K] [Algebra F K] (e : E) :
    Algebra.norm K ((1 : K) ⊗ₜ[F] e) = algebraMap F K (Algebra.norm F e) := by
  classical
  let b := Module.Free.chooseBasis F E
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis K b), Algebra.norm_eq_matrix_det b,
    RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul]
  simp

end

/- English proof (translation)
Introduce `F E _ _ _ _`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `K K' _ _ _ _ φ x ⟨y, hy⟩`. Use `⟨Algebra.TensorProduct.map φ (AlgHom.id F E) y, ?_⟩` and prove the remaining obligations. Rewrite using `[tensor_norm_map φ y, hy, AlgHom.commutes]`.

Introduce `K _ _ e`. Conclude with `⟨(1 : K) ⊗ₜ[F] e, tensor_norm_one_tmul K e⟩`. Introduce and unpack `K _ _ x y hy0 ⟨a, ha⟩ ⟨c, hc⟩`. Establish `hyK : algebraMap F K y ≠ 0` using `(_root_.map_ne_zero _).mpr hy0`. Establish `hu : IsUnit (Algebra.lmul K (K ⊗[F] E) c)`.

Rewrite using `[LinearMap.isUnit_iff_isUnit_det, ← Algebra.norm_apply, hc]`. Conclude with `hyK.isUnit`. Take `⟨d, hd⟩` from `((Module.End.isUnit_iff _).mp hu).2 1`. Establish `hd' : c * d = 1` using `hd`. Establish `hn : Algebra.norm K c * Algebra.norm K d = 1`.

Rewrite using `[← map_mul, hd', map_one]`. Use `⟨a * d, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ha, map_mul]`. Rewrite `hn` using `[hc]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tnorm_baseChange : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E], (∀ (K K' : Type) [Field K] [Algebra F K] [Field K'] [Algebra F K'] (_ : K →ₐ[F] K') (x : F), TNorm F E K x → TNorm F E K' x) ∧ (∀ (K : Type) [Field K] [Algebra F K] (e : E), TNorm F E K (Algebra.norm F e)) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x y : F), y ≠ 0 → TNorm F E K (x * y) → TNorm F E K y → TNorm F E K x := by
  intro F E _ _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rintro K K' _ _ _ _ φ x ⟨y, hy⟩
    refine ⟨Algebra.TensorProduct.map φ (AlgHom.id F E) y, ?_⟩
    rw [tensor_norm_map φ y, hy, AlgHom.commutes]
  · intro K _ _ e
    exact ⟨(1 : K) ⊗ₜ[F] e, tensor_norm_one_tmul K e⟩
  · rintro K _ _ x y hy0 ⟨a, ha⟩ ⟨c, hc⟩
    have hyK : algebraMap F K y ≠ 0 := (_root_.map_ne_zero _).mpr hy0
    have hu : IsUnit (Algebra.lmul K (K ⊗[F] E) c) := by
      rw [LinearMap.isUnit_iff_isUnit_det, ← Algebra.norm_apply, hc]
      exact hyK.isUnit
    obtain ⟨d, hd⟩ := ((Module.End.isUnit_iff _).mp hu).2 1
    have hd' : c * d = 1 := hd
    have hn : Algebra.norm K c * Algebra.norm K d = 1 := by
      rw [← map_mul, hd', map_one]
    refine ⟨a * d, ?_⟩
    rw [map_mul, ha, map_mul]
    rw [hc] at hn
    calc algebraMap F K x * algebraMap F K y * Algebra.norm K d
        = algebraMap F K x * (algebraMap F K y * Algebra.norm K d) := by ring
      _ = algebraMap F K x := by rw [hn, mul_one]

end GlobalTheory.CNorm
