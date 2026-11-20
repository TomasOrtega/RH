import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Polynomial

noncomputable section

namespace GlobalTheory.JR.Et

/- English proof (translation)
Use `set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def`. Use `set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def`. Establish `hab : Commute a b` using `Algebra.commutes X b`. Establish `key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q`. Introduce `q`.

Proceed by induction on `q using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Take `⟨H1, h1⟩` from `hp`. Take `⟨H2, h2⟩` from `hq`. Conclude with `⟨H1 + H2, by rw [mul_add, h1, h2, map_add, map_add]; abel⟩`.

Consider the case `monomial k c`. Use `⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂, mul_sub]`. Take `⟨H, hH⟩` from `key p`. Establish `hb : aeval b p = 0`.

Rewrite using `[hb_def, aeval_algHom_apply, hp, map_zero]`. Establish `ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p`. Rewrite using `[ha_def, aeval_algebraMap_apply, aeval_X_left_apply]`. Establish `hch : (a - b).det = M.charpoly` using `rfl`. Use `⟨H.det, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]`. Simplify using the standard rewrite rules.
-/
theorem charpoly_dvd_pow_of_aeval_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
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

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

/- English proof (translation)
Establish `h` using `LinearMap.aeval_self_charpoly (Algebra.lmul F A.K z)`. Establish `h' : Algebra.lmul F A.K (aeval z (LinearMap.charpoly (Algebra.lmul F A.K z))) = 0`. Rewrite using `[← aeval_algHom_apply]`. Conclude with `h`. Simplify using `using congrArg (fun f : Module.End F A.K => f 1) h'`.
-/
theorem aeval_self_charpoly_lmul (A : Et F E) (z : A.K) :
    aeval z (LinearMap.charpoly (Algebra.lmul F A.K z)) = 0 := by
  have h := LinearMap.aeval_self_charpoly (Algebra.lmul F A.K z)
  have h' : Algebra.lmul F A.K (aeval z (LinearMap.charpoly (Algebra.lmul F A.K z))) = 0 := by
    rw [← aeval_algHom_apply]; exact h
  simpa using congrArg (fun f : Module.End F A.K => f 1) h'

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `hl : LinearMap.charpoly (Algebra.lmul F A.K z) ∈ Polynomial.lifts (algebraMap (NormedField.valuation (K` using `F)).integer F) := by`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `i`.

Use `⟨⟨_, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `hz i` after adjusting the coercions. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic _)`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap F, hq]`. Conclude with `aeval_self_charpoly_lmul A z`. Introduce and unpack `⟨p, hpm, hp⟩ i`. Establish `hp' : aeval z (p.map (algebraMap (NormedField.valuation (K` using `F)).integer F)) = 0 := by`. Rewrite using `[Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]`.

Conclude with `hp`. Establish `h1 : aeval (Algebra.lmul F A.K z) (p.map (algebraMap (NormedField.valuation (K` using `F)).integer F)) = 0 := by`. Rewrite using `[aeval_algHom_apply, hp', map_zero]`. Set `bs` to `Module.finBasis F A.K`. Establish `h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z)) (p.map (algebraMap (NormedField.valuation (K` using `F)).integer F)) = 0 := by`.

Rewrite using `[aeval_algHom_apply, h1, map_zero]`. Establish `h3` using `charpoly_dvd_pow_of_aeval_zero _ _ h2`. Establish `h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z)).charpoly = LinearMap.charpoly (Algebra.lmul F A.K z)` using `LinearMap.charpoly_toMatrix _ bs`. Rewrite `h3` using `[h4, ← Polynomial.map_pow]`. Establish `h5` using `Polynomial.isIntegral_coeff_of_dvd _ _ (hpm.pow _) (LinearMap.charpoly_monic _) h3 i`.

Establish `h6` using `(Valuation.integer.integers (NormedField.valuation (K := F))).mem_of_integral h5`. Rewrite `h6` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `h6` after adjusting the coercions.
-/
theorem mem_OK_iff_isIntegral [IsUltrametricDist F] (A : Et F E) (z : A.K) :
    z ∈ A.OK ↔ IsIntegral (NormedField.valuation (K := F)).integer z := by
  constructor
  · intro hz
    have hl : LinearMap.charpoly (Algebra.lmul F A.K z) ∈
        Polynomial.lifts (algebraMap (NormedField.valuation (K := F)).integer F) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      refine ⟨⟨_, ?_⟩, rfl⟩
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
      exact_mod_cast hz i
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic _)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap F, hq]
    exact aeval_self_charpoly_lmul A z
  · rintro ⟨p, hpm, hp⟩ i
    have hp' : aeval z (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]; exact hp
    have h1 : aeval (Algebra.lmul F A.K z) (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [aeval_algHom_apply, hp', map_zero]
    let bs := Module.finBasis F A.K
    have h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z))
        (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [aeval_algHom_apply, h1, map_zero]
    have h3 := charpoly_dvd_pow_of_aeval_zero _ _ h2
    have h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z)).charpoly =
        LinearMap.charpoly (Algebra.lmul F A.K z) := LinearMap.charpoly_toMatrix _ bs
    rw [h4, ← Polynomial.map_pow] at h3
    have h5 := Polynomial.isIntegral_coeff_of_dvd _ _ (hpm.pow _) (LinearMap.charpoly_monic _) h3 i
    have h6 := (Valuation.integer.integers (NormedField.valuation (K := F))).mem_of_integral h5
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h6
    exact_mod_cast h6

/- English proof (translation)
Introduce `F E _ _ _ _ hU A`. Use `haveI : IsUltrametricDist F := hU.ultraF`. Use `⟨(integralClosure (NormedField.valuation (K := F)).integer A.K).toSubring, ?_⟩` and prove the remaining obligations. Use extensionality with `z`. Conclude with `(mem_OK_iff_isIntegral A z).symm`.
-/
theorem OK_isSubring : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  intro F E _ _ _ _ hU A
  haveI : IsUltrametricDist F := hU.ultraF
  refine ⟨(integralClosure (NormedField.valuation (K := F)).integer A.K).toSubring, ?_⟩
  ext z
  exact (mem_OK_iff_isIntegral A z).symm

end GlobalTheory.JR.Et
