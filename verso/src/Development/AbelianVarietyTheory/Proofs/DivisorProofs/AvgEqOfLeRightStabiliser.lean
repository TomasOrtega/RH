import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

/- English proof (translation)
Introduce `H _ u S hS hi`. Use `haveI : S.FiniteIndex := ⟨hi⟩`. Use `haveI : (rStab u).FiniteIndex := Subgroup.finiteIndex_of_le hS`. Establish `hRi : (rStab u).index ≠ 0` using `Subgroup.FiniteIndex.index_ne_zero`. Establish `hu : ∀ x : H, u ((QuotientGroup.mk x : H ⧸ rStab u).out) = u x`.

Introduce `x`. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (rStab u) x`. Rewrite using `[hk]`. Conclude with `k.2 x`. Set `e` to `Subgroup.quotientEquivProdOfLE hS`.

Establish `he : ∀ q : H ⧸ S, ((e q).1 : H ⧸ rStab u) = QuotientGroup.mk q.out`. Introduce `q`. Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Use `haveI : Fintype (H ⧸ S) := Fintype.ofFinite _`.

Use `haveI : Fintype (H ⧸ rStab u) := Fintype.ofFinite _`. Use `haveI : Finite ((rStab u) ⧸ S.subgroupOf (rStab u)) := by`. Establish `: Finite ((H ⧸ rStab u) × (rStab u) ⧸ S.subgroupOf (rStab u))` using `Finite.of_equiv _ e`. Conclude with `Finite.prod_right (H ⧸ rStab u)`. Use `haveI : Fintype ((rStab u) ⧸ S.subgroupOf (rStab u)) := Fintype.ofFinite _`.

Establish `hsum : ∑ᶠ q : H ⧸ S, u q.out = (S.relIndex (rStab u) : ℂ) * ∑ᶠ p : H ⧸ rStab u, u p.out`. Rewrite using `[finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]`. Establish `h1 : ∀ q : H ⧸ S, u q.out = (fun p : (H ⧸ rStab u) × ((rStab u) ⧸ S.subgroupOf (rStab u)) => u p.1.out) (e q)`. Introduce `q`. Simplify using `only`.

Rewrite using `[he q, hu]`. Rewrite using `[Finset.sum_congr rfl (fun q _ => h1 q), Equiv.sum_comp e (fun p => u p.1.out), Fintype.sum_prod_type]`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[← Finset.mul_sum]`. Use `congr 1`.

Rewrite using `[Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]`. Rewrite using `[avg, hsum, ← Subgroup.relIndex_mul_index hS]`. Establish `h2 : (S.relIndex (rStab u) : ℂ) ≠ 0`. Establish `: S.relIndex (rStab u) ≠ 0`. Introduce `h0`.

Apply `hi` to reduce the goal to its premises. Rewrite using `[← Subgroup.relIndex_mul_index hS, h0, zero_mul]`. Conclude with `this` after adjusting the coercions. Establish `h3 : ((rStab u).index : ℂ) ≠ 0` using `by exact_mod_cast hRi`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem avg_eq_of_le_rStab : ∀ (H : Type) [Group H] (u : H → ℂ) (S : Subgroup H), S ≤ rStab u → S.index ≠ 0 →
    avg u = (S.index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ u S hS hi
  haveI : S.FiniteIndex := ⟨hi⟩
  haveI : (rStab u).FiniteIndex := Subgroup.finiteIndex_of_le hS
  have hRi : (rStab u).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hu : ∀ x : H, u ((QuotientGroup.mk x : H ⧸ rStab u).out) = u x := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
    rw [hk]
    exact k.2 x
  let e := Subgroup.quotientEquivProdOfLE hS
  have he : ∀ q : H ⧸ S, ((e q).1 : H ⧸ rStab u) = QuotientGroup.mk q.out := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  haveI : Fintype (H ⧸ S) := Fintype.ofFinite _
  haveI : Fintype (H ⧸ rStab u) := Fintype.ofFinite _
  haveI : Finite ((rStab u) ⧸ S.subgroupOf (rStab u)) := by
    have : Finite ((H ⧸ rStab u) × (rStab u) ⧸ S.subgroupOf (rStab u)) := Finite.of_equiv _ e
    exact Finite.prod_right (H ⧸ rStab u)
  haveI : Fintype ((rStab u) ⧸ S.subgroupOf (rStab u)) := Fintype.ofFinite _
  have hsum : ∑ᶠ q : H ⧸ S, u q.out =
      (S.relIndex (rStab u) : ℂ) * ∑ᶠ p : H ⧸ rStab u, u p.out := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    have h1 : ∀ q : H ⧸ S, u q.out = (fun p : (H ⧸ rStab u) × ((rStab u) ⧸ S.subgroupOf (rStab u)) =>
        u p.1.out) (e q) := by
      intro q
      simp only
      rw [he q, hu]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), Equiv.sum_comp e (fun p => u p.1.out),
      Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [avg, hsum, ← Subgroup.relIndex_mul_index hS]
  have h2 : (S.relIndex (rStab u) : ℂ) ≠ 0 := by
    have : S.relIndex (rStab u) ≠ 0 := by
      intro h0; apply hi; rw [← Subgroup.relIndex_mul_index hS, h0, zero_mul]
    exact_mod_cast this
  have h3 : ((rStab u).index : ℂ) ≠ 0 := by exact_mod_cast hRi
  push_cast
  field_simp

end GlobalTheory.BCT
