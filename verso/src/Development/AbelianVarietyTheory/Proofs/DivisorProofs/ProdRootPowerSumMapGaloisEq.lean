import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSumMapFrobeniusPowStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

/- English proof (translation)
Introduce `F F' _ _ _ _ θ k P`. Establish `: Finite F` using `Finite.of_injective _ (algebraMap F F').injective`. Use `letI := Fintype.ofFinite F`. Establish `hb` using `FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F'`. Rewrite using `[← Fintype.prod_bijective _ hb (fun n => rootSum θ k (P.map ((FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1 : F' ≃ₐ[F] F') : F' →+* F'))) _ (fun _ => rfl)]`.

Rewrite using `[Finset.prod_range (fun j => rootSum θ (k * Nat.card F ^ j) P)]`. Use `Finset.prod_congr rfl fun n _ => ?_` and prove the remaining obligations. Use `haveI : CharP F (ringChar F) := ringChar.charP F`. Take `⟨r, hp, hcard⟩` from `FiniteField.card F (ringChar F)`. Establish `hchar : ringChar F' = ringChar F` using `(Algebra.ringChar_eq F F').symm`.

Establish `key` using `GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F' θ ((FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1 : F' ≃ₐ[F] F') : F' →+* F') (r * n.1) (fun x => by`. Rewrite using `[hchar, pow_mul, ← hcard]`. Use `show (FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1) x = _`. Rewrite using `[AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]) k P`. Rewrite using `[key, hchar, pow_mul, ← hcard, Nat.card_eq_fintype_card]`.
-/
theorem prod_rootSum_map_algEquiv : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (θ : AlgebraicClosure F' →* ℂ) (k : ℕ) (P : F'[X]),
    ∏ t : F' ≃ₐ[F] F', rootSum θ k (P.map (t : F' →+* F')) =
      ∏ j ∈ Finset.range (Module.finrank F F'), rootSum θ (k * Nat.card F ^ j) P := by
  intro F F' _ _ _ _ θ k P
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  letI := Fintype.ofFinite F
  have hb := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F'
  rw [← Fintype.prod_bijective _ hb
    (fun n => rootSum θ k (P.map ((FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1 : F' ≃ₐ[F] F') : F' →+* F')))
    _ (fun _ => rfl)]
  rw [Finset.prod_range (fun j => rootSum θ (k * Nat.card F ^ j) P)]
  refine Finset.prod_congr rfl fun n _ => ?_
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨r, hp, hcard⟩ := FiniteField.card F (ringChar F)
  have hchar : ringChar F' = ringChar F := (Algebra.ringChar_eq F F').symm
  have key := GlobalTheory.T.rootSum_map_frobenius_pow_eq_rootSum_mul F' θ
    ((FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1 : F' ≃ₐ[F] F') : F' →+* F') (r * n.1) (fun x => by
      rw [hchar, pow_mul, ← hcard]
      show (FiniteField.frobeniusAlgEquivOfAlgebraic F F' ^ n.1) x = _
      rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]) k P
  rw [key, hchar, pow_mul, ← hcard, Nat.card_eq_fintype_card]

end GlobalTheory.Shin
