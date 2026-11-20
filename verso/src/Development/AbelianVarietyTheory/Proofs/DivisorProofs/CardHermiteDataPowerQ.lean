import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaExponentHnfGL

open GroundTheory.Automorphic GLnLocal Iwasawa
open scoped ValuativeRel

namespace GlobalTheory.HermCount

/- English proof (translation)
Establish `hq` using `cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[F]) (IsDiscreteValuationRing.not_a_field _) (i := t)`. Rewrite `hq` using `[Submodule.cardQuot_apply, Submodule.cardQuot_apply, maximalIdeal_pow_eq]`. Rewrite using `[Res, hq]`. Both sides reduce to the same expression.
-/
theorem card_res (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (t : ℕ) :
    Nat.card (Res F t) = Spherical.qF F ^ t := by
  have hq := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal 𝒪[F])
    (IsDiscreteValuationRing.not_a_field _) (i := t)
  rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply, maximalIdeal_pow_eq] at hq
  rw [Res, hq]
  rfl

/- English proof (translation)
Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) (p := fun p : Fin n × Fin n => p.1 < p.2) (by simp) (fun p => l p.1)]`. Rewrite using `[Finset.sum_filter, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_filter]`. Simplify using `only`.

Rewrite using `[Finset.sum_const, smul_eq_mul]`. Use `congr 1`. Establish `: (Finset.univ.filter fun j : Fin n => i < j) = Finset.Ioi i`. Use extensionality with `j`. Simplify using the standard rewrite rules.

Rewrite using `[this, Fin.card_Ioi]`.
-/
theorem sum_pos (n : ℕ) (l : Fin n → ℕ) :
    ∑ p : Pos n, l p.1.1 = ∑ i : Fin n, (n - 1 - i.val) * l i := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2)
    (p := fun p : Fin n × Fin n => p.1 < p.2) (by simp) (fun p => l p.1)]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  simp only
  rw [Finset.sum_const, smul_eq_mul]
  congr 1
  have : (Finset.univ.filter fun j : Fin n => i < j) = Finset.Ioi i := by
    ext j; simp
  rw [this, Fin.card_Ioi]

/- English proof (translation)
Introduce `F _ _ _ _ n l`. Rewrite using `[HData, Nat.card_pi]`. Simplify using `only [card_res]`. Rewrite using `[Finset.prod_pow_eq_pow_sum, sum_pos]`.
-/
theorem card_hData : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (l : Fin n → ℕ),
    Nat.card (GlobalTheory.HermCount.HData F n l) = Spherical.qF F ^ (∑ i : Fin n, (n - 1 - i.val) * l i) := by
  intro F _ _ _ _ n l
  rw [HData, Nat.card_pi]
  simp only [card_res]
  rw [Finset.prod_pow_eq_pow_sum, sum_pos]

end GlobalTheory.HermCount
