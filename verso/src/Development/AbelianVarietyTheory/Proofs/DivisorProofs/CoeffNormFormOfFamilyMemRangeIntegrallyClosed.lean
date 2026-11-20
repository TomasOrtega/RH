import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZero
open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace GlobalTheory.NormSheaf.IntegralCoeff

open MvPolynomial
open scoped TensorProduct

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use extensionality with `a c`. Simplify using `[Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_apply]`.
-/
theorem leftMulMatrix_sum_tmul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (x : Fin m → L) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis (MvPolynomial (Fin m) K) (Module.finBasis K L))
      (∑ i, (X i : MvPolynomial (Fin m) K) ⊗ₜ[K] x i) =
    ∑ i, (X i : MvPolynomial (Fin m) K) •
      (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* MvPolynomial (Fin m) K) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a c
  simp [Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_repr_tmul,
    Algebra.TensorProduct.basis_apply]

/- English proof (translation)
Establish `hd` using `GlobalTheory.CharpolyDvd.matrix_charpoly_dvd_pow M _ h`. Rewrite `hd` using `[← Polynomial.map_pow]`. Establish `hc` using `Polynomial.isIntegral_coeff_of_dvd (g ^ Fintype.card n) M.charpoly (hg.pow _) M.charpoly_monic hd 0`. Rewrite using `[Matrix.det_eq_sign_charpoly_coeff]`. Conclude with `(isIntegral_one.neg.pow _).mul hc`.
-/
theorem isIntegral_det_of_aeval {R' F : Type} [CommRing R'] [Field F] [Algebra R' F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (g : Polynomial R') (hg : g.Monic)
    (h : Polynomial.aeval M (g.map (algebraMap R' F)) = 0) : IsIntegral R' M.det := by
  have hd := GlobalTheory.CharpolyDvd.matrix_charpoly_dvd_pow M _ h
  rw [← Polynomial.map_pow] at hd
  have hc := Polynomial.isIntegral_coeff_of_dvd (g ^ Fintype.card n) M.charpoly (hg.pow _) M.charpoly_monic hd 0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  exact (isIntegral_one.neg.pow _).mul hc

end GlobalTheory.NormSheaf.IntegralCoeff

namespace GlobalTheory.NormSheaf.IntegralCoeff

open MvPolynomial
open scoped TensorProduct

/- English proof (translation)
Use `letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial`. Use `set R := MvPolynomial (Fin m) K`. Use `set R' := MvPolynomial (Fin m) A`. Set `F` to `FractionRing R`. Use `haveI : IsScalarTower R' R F := inferInstance`.

Set `S` to `R ⊗[K] L`. Use `letI : Algebra R' S := ((algebraMap R S).comp (algebraMap R' R)).toAlgebra`. Set `y : S` to `∑ i, (X i : R) ⊗ₜ[K] x i`. Establish `hy : IsIntegral R' y`. Use `IsIntegral.sum _ fun i _ => ?_` and prove the remaining obligations.

Establish `e : (X i : R) ⊗ₜ[K] x i = algebraMap R' S (X i) * (1 ⊗ₜ[K] x i)`. Establish `hX : algebraMap R' R (X i) = X i` using `MvPolynomial.map_X _ _`. Express the relevant statement in the definitionally equal form `_ = algebraMap R S (algebraMap R' R (X i)) * _`. Rewrite using `[hX]`. Express the relevant statement in the definitionally equal form `_ = ((X i : R) ⊗ₜ[K] (1 : L)) * (1 ⊗ₜ[K] x i)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Rewrite using `[e]`. Use `isIntegral_algebraMap.mul ?_` and prove the remaining obligations. Use `IsIntegral.map_of_comp_eq (algebraMap A R') (Algebra.TensorProduct.includeRight : L →ₐ[K] S).toRingHom ?_ (hx i)` and prove the remaining obligations. Use `RingHom.ext fun a => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(algebraMap R' R (algebraMap A R' a)) ⊗ₜ[K] (1 : L) = (1 : R) ⊗ₜ[K] algebraMap A L a`. Establish `h1 : algebraMap R' R (algebraMap A R' a) = algebraMap K R (algebraMap A K a)`. Express the relevant statement in the definitionally equal form `MvPolynomial.map (algebraMap A K) (C a) = C (algebraMap A K a)`. Conclude with `MvPolynomial.map_C _ _`. Rewrite using `[h1, IsScalarTower.algebraMap_apply A K L, Algebra.algebraMap_eq_smul_one (A := R) (algebraMap A K a), Algebra.algebraMap_eq_smul_one (A := L) (algebraMap A K a), TensorProduct.smul_tmul]`.

Take `⟨g, hgm, hgy⟩` from `hy`. Set `bS` to `Algebra.TensorProduct.basis R (Module.finBasis K L)`. Set `φ : S →ₐ[R] Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F` to `(AlgHom.mapMatrix (Algebra.ofId R F)).comp (Algebra.leftMulMatrix bS)`. Establish `hM : φ y = (algebraMap R F).mapMatrix (∑ i, (X i : R) • (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* R))`. Rewrite using `[← leftMulMatrix_sum_tmul K L x]`.

Both sides reduce to the same expression. Establish `h0 : Polynomial.aeval (φ y) (g.map (algebraMap R' F)) = 0`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map]`. Establish `hh : (algebraMap F (Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F)).comp (algebraMap R' F) = φ.toRingHom.comp (algebraMap R' S)`. Use `RingHom.ext fun r => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `algebraMap F _ (algebraMap R' F r) = φ (algebraMap R S (algebraMap R' R r))`. Rewrite using `[AlgHom.commutes, IsScalarTower.algebraMap_apply R' R F]`. Conclude with `(IsScalarTower.algebraMap_apply R F _ _).symm`. Rewrite using `[hh]`. Establish `h2` using `Polynomial.hom_eval₂ g (algebraMap R' S) φ.toRingHom y`.

Rewrite `h2` using `[hgy, map_zero]`. Conclude with `h2.symm`. Establish `hdet` using `isIntegral_det_of_aeval _ g hgm h0`. Rewrite `hdet` using `[hM, ← RingHom.map_det]`. Conclude with `(isIntegral_algebraMap_iff (IsFractionRing.injective R F)).mp hdet`.
-/
theorem isIntegral_normForm (A K L : Type) [CommRing A] [Field K] [Field L] [Algebra A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L) (hx : ∀ i, IsIntegral A (x i)) :
    letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
    IsIntegral (MvPolynomial (Fin m) A) (GlobalTheory.NormSheaf.normForm K L x) := by
  classical
  letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
  set R := MvPolynomial (Fin m) K
  set R' := MvPolynomial (Fin m) A
  let F := FractionRing R
  haveI : IsScalarTower R' R F := inferInstance
  let S := R ⊗[K] L
  letI : Algebra R' S := ((algebraMap R S).comp (algebraMap R' R)).toAlgebra
  let y : S := ∑ i, (X i : R) ⊗ₜ[K] x i
  have hy : IsIntegral R' y := by
    refine IsIntegral.sum _ fun i _ => ?_
    have e : (X i : R) ⊗ₜ[K] x i = algebraMap R' S (X i) * (1 ⊗ₜ[K] x i) := by
      have hX : algebraMap R' R (X i) = X i := MvPolynomial.map_X _ _
      change _ = algebraMap R S (algebraMap R' R (X i)) * _
      rw [hX]
      change _ = ((X i : R) ⊗ₜ[K] (1 : L)) * (1 ⊗ₜ[K] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    refine isIntegral_algebraMap.mul ?_
    refine IsIntegral.map_of_comp_eq (algebraMap A R')
      (Algebra.TensorProduct.includeRight : L →ₐ[K] S).toRingHom ?_ (hx i)
    refine RingHom.ext fun a => ?_
    change (algebraMap R' R (algebraMap A R' a)) ⊗ₜ[K] (1 : L) = (1 : R) ⊗ₜ[K] algebraMap A L a
    have h1 : algebraMap R' R (algebraMap A R' a) = algebraMap K R (algebraMap A K a) := by
      change MvPolynomial.map (algebraMap A K) (C a) = C (algebraMap A K a)
      exact MvPolynomial.map_C _ _
    rw [h1, IsScalarTower.algebraMap_apply A K L, Algebra.algebraMap_eq_smul_one (A := R) (algebraMap A K a),
      Algebra.algebraMap_eq_smul_one (A := L) (algebraMap A K a), TensorProduct.smul_tmul]
  obtain ⟨g, hgm, hgy⟩ := hy
  let bS := Algebra.TensorProduct.basis R (Module.finBasis K L)
  let φ : S →ₐ[R] Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F :=
    (AlgHom.mapMatrix (Algebra.ofId R F)).comp (Algebra.leftMulMatrix bS)
  have hM : φ y = (algebraMap R F).mapMatrix
      (∑ i, (X i : R) • (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* R)) := by
    rw [← leftMulMatrix_sum_tmul K L x]
    rfl
  have h0 : Polynomial.aeval (φ y) (g.map (algebraMap R' F)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hh : (algebraMap F (Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F)).comp (algebraMap R' F)
        = φ.toRingHom.comp (algebraMap R' S) := by
      refine RingHom.ext fun r => ?_
      change algebraMap F _ (algebraMap R' F r) = φ (algebraMap R S (algebraMap R' R r))
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R' R F]
      exact (IsScalarTower.algebraMap_apply R F _ _).symm
    rw [hh]
    have h2 := Polynomial.hom_eval₂ g (algebraMap R' S) φ.toRingHom y
    rw [hgy, map_zero] at h2
    exact h2.symm
  have hdet := isIntegral_det_of_aeval _ g hgm h0
  rw [hM, ← RingHom.map_det] at hdet
  exact (isIntegral_algebraMap_iff (IsFractionRing.injective R F)).mp hdet

end GlobalTheory.NormSheaf.IntegralCoeff

namespace GlobalTheory.NormSheaf.IntegralCoeff

/- English proof (translation)
Introduce `A K L _ _ _ _ _ _ _ _ _ _ _ m x hx s`. Use `letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial`. Establish `key` using `isIntegral_normForm A K L x hx`. Establish `hc` using `MvPolynomial.isIntegral_iff_isIntegral_coeff.mp key s`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hc`.

Conclude with `⟨a, ha⟩`.
-/
theorem coeff_normForm_mem_range : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L), (∀ i, IsIntegral A (x i)) →
    ∀ s, (GlobalTheory.NormSheaf.normForm K L x).coeff s ∈ (algebraMap A K).range := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _ m x hx s
  letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
  have key := isIntegral_normForm A K L x hx
  have hc := MvPolynomial.isIntegral_iff_isIntegral_coeff.mp key s
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc
  exact ⟨a, ha⟩

end GlobalTheory.NormSheaf.IntegralCoeff
