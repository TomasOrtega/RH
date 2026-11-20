import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp

open Polynomial

namespace GlobalTheory.UnitLemma.Centraliser

/- English proof (translation)
Use `set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def`. Use `set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def`. Establish `hab : Commute a b` using `Algebra.commutes X b`. Establish `key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q`. Introduce `q`.

Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Take `⟨H1, h1⟩` from `hp`. Take `⟨H2, h2⟩` from `hq`. Conclude with `⟨H1 + H2, by rw [mul_add, h1, h2, map_add, map_add]; abel⟩`.

Consider the case `monomial k c`. Use `⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂, mul_sub]`. Take `⟨H, hH⟩` from `key p`. Establish `hb : aeval b p = 0`.

Rewrite using `[hb_def, aeval_algHom_apply, hp, map_zero]`. Establish `ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p`. Rewrite using `[ha_def, aeval_algebraMap_apply, aeval_X_left_apply]`. Establish `hch : (a - b).det = M.charpoly` using `rfl`. Use `⟨H.det, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]`. Simplify using the standard rewrite rules.
-/
theorem charpoly_dvd_pow_of_aeval_eq_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by
  set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def
  set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def
  have hab : Commute a b := Algebra.commutes X b
  have key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨H1, h1⟩ := hp
      obtain ⟨H2, h2⟩ := hq
      exact ⟨H1 + H2, by rw [mul_add, h1, h2, map_add, map_add]; abel⟩
    | monomial k c =>
      refine ⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩
      rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂,
        mul_sub]
  obtain ⟨H, hH⟩ := key p
  have hb : aeval b p = 0 := by
    rw [hb_def, aeval_algHom_apply, hp, map_zero]
  have ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p := by
    rw [ha_def, aeval_algebraMap_apply, aeval_X_left_apply]
  have hch : (a - b).det = M.charpoly := rfl
  refine ⟨H.det, ?_⟩
  rw [← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]
  simp

/- English proof (translation)
Establish `h1 : aeval (Algebra.lmul K.E B.A B.g) p = 0`. Rewrite using `[aeval_algHom_apply, hp, map_zero]`. Set `bs` to `Module.finBasis K.E B.A`. Establish `h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul K.E B.A B.g)) p = 0`. Rewrite using `[aeval_algHom_apply, h1, map_zero]`.

Establish `h3` using `charpoly_dvd_pow_of_aeval_eq_zero _ p h2`. Establish `h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul K.E B.A B.g)).charpoly = B.P`. Conclude with `LinearMap.charpoly_toMatrix _ bs`. Rewrite `h3` using `[h4]`. Conclude with `hsep.squarefree.isRadical _ _ h3`.
-/
theorem P_dvd_of_aeval_eq_zero {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (p : K.E[X])
    (hp : aeval B.g p = 0) : B.P ∣ p := by
  have h1 : aeval (Algebra.lmul K.E B.A B.g) p = 0 := by
    rw [aeval_algHom_apply, hp, map_zero]
  let bs := Module.finBasis K.E B.A
  have h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul K.E B.A B.g)) p = 0 := by
    rw [aeval_algHom_apply, h1, map_zero]
  have h3 := charpoly_dvd_pow_of_aeval_eq_zero _ p h2
  have h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul K.E B.A B.g)).charpoly = B.P := by
        exact LinearMap.charpoly_toMatrix _ bs
  rw [h4] at h3
  exact hsep.squarefree.isRadical _ _ h3

/- English proof (translation)
Establish `h` using `LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)`. Establish `h' : Algebra.lmul K.E B.A (aeval B.g B.P) = 0`. Rewrite using `[← aeval_algHom_apply]`. Conclude with `h`. Simplify using `using congrArg (fun f : Module.End K.E B.A => f 1) h'`.
-/
theorem aeval_g_P {K : UQ} (B : InvAlg K) : aeval B.g B.P = 0 := by
  have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft K.E B.g)
  have h' : Algebra.lmul K.E B.A (aeval B.g B.P) = 0 := by
    rw [← aeval_algHom_apply]; exact h
  simpa using congrArg (fun f : Module.End K.E B.A => f 1) h'

/- English proof (translation)
Establish `hm : B.P.Monic` using `LinearMap.charpoly_monic _`. Establish `hP : eval₂ (↑(Algebra.ofId K.E B.A)) B.g B.P = 0` using `aeval_g_P B`. Set `φ` to `AdjoinRoot.liftAlgHom B.P (Algebra.ofId K.E B.A) B.g hP`. Set `pb` to `AdjoinRoot.powerBasis' hm`. Use `haveI : Module.Finite K.E (AdjoinRoot B.P) := pb.finite`.

Establish `hrank : Module.finrank K.E (AdjoinRoot B.P) = Module.finrank K.E B.A`. Rewrite using `[pb.finrank, AdjoinRoot.powerBasis'_dim]`. Conclude with `LinearMap.charpoly_natDegree _`. Establish `hinj : Function.Injective φ.toLinearMap`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `z hz`. Take `⟨p, rfl⟩` from `AdjoinRoot.mk_surjective z`. Rewrite using `[AdjoinRoot.mk_eq_zero]`. Apply `P_dvd_of_aeval_eq_zero B hsep` to reduce the goal to its premises. Simplify `hz` using `[φ, AdjoinRoot.liftAlgHom_mk, aeval_def]`.

Take `⟨z, hz⟩` from `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj y`. Take `⟨p, rfl⟩` from `AdjoinRoot.mk_surjective z`. Conclude with `⟨p, by simpa [φ, AdjoinRoot.liftAlgHom_mk, aeval_def] using hz⟩`.
-/
theorem exists_aeval_eq {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (y : B.A) :
    ∃ p : K.E[X], aeval B.g p = y := by
  have hm : B.P.Monic := LinearMap.charpoly_monic _
  have hP : eval₂ (↑(Algebra.ofId K.E B.A)) B.g B.P = 0 := aeval_g_P B
  let φ := AdjoinRoot.liftAlgHom B.P (Algebra.ofId K.E B.A) B.g hP
  let pb := AdjoinRoot.powerBasis' hm
  haveI : Module.Finite K.E (AdjoinRoot B.P) := pb.finite
  have hrank : Module.finrank K.E (AdjoinRoot B.P) = Module.finrank K.E B.A := by
    rw [pb.finrank, AdjoinRoot.powerBasis'_dim]
    exact LinearMap.charpoly_natDegree _
  have hinj : Function.Injective φ.toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    rw [AdjoinRoot.mk_eq_zero]
    apply P_dvd_of_aeval_eq_zero B hsep
    simpa [φ, AdjoinRoot.liftAlgHom_mk, aeval_def] using hz
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj y
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  exact ⟨p, by simpa [φ, AdjoinRoot.liftAlgHom_mk, aeval_def] using hz⟩

/- English proof (translation)
Take `⟨p, rfl⟩` from `exists_aeval_eq B hsep a`. Take `⟨m, hm⟩` from `ha`. Establish `h1 : B.P ∣ p ^ m` using `P_dvd_of_aeval_eq_zero B hsep _ (by rw [map_pow, hm])`. Take `⟨q, rfl⟩` from `hsep.squarefree.isRadical m p h1`. Rewrite using `[map_mul, aeval_g_P, zero_mul]`.
-/
theorem eq_zero_of_isNilpotent {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (a : B.A)
    (ha : IsNilpotent a) : a = 0 := by
  obtain ⟨p, rfl⟩ := exists_aeval_eq B hsep a
  obtain ⟨m, hm⟩ := ha
  have h1 : B.P ∣ p ^ m := P_dvd_of_aeval_eq_zero B hsep _ (by rw [map_pow, hm])
  obtain ⟨q, rfl⟩ := hsep.squarefree.isRadical m p h1
  rw [map_mul, aeval_g_P, zero_mul]

/- English proof (translation)
Apply `eq_zero_of_isNilpotent B hsep` to reduce the goal to its premises. Set `bs` to `Module.finBasis K.E B.A`. Establish `hN : IsNilpotent (Algebra.leftMulMatrix bs a)`. Apply `ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow` to reduce the goal to its premises. Introduce `k hk _`.

Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[← map_pow, ← Algebra.trace_eq_matrix_trace, pow_succ']`. Conclude with `ha _`. Take `⟨m, hm⟩` from `hN`. Use `⟨m, Algebra.leftMulMatrix_injective bs ?_⟩` and prove the remaining obligations.

Rewrite using `[map_pow, hm, map_zero]`.
-/
theorem eq_zero_of_trace_mul {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (a : B.A)
    (ha : ∀ y, Algebra.trace K.E B.A (a * y) = 0) : a = 0 := by
  apply eq_zero_of_isNilpotent B hsep
  let bs := Module.finBasis K.E B.A
  have hN : IsNilpotent (Algebra.leftMulMatrix bs a) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace, pow_succ']
    exact ha _
  obtain ⟨m, hm⟩ := hN
  refine ⟨m, Algebra.leftMulMatrix_injective bs ?_⟩
  rw [map_pow, hm, map_zero]

end GlobalTheory.UnitLemma.Centraliser
