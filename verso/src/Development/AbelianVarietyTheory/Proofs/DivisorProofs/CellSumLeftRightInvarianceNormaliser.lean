import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

/- English proof (translation)
Introduce `G _ K N h g k₁ k₂ hh hk₁ hk₂ hN hN'`. Unfold `cellSum`. Rewrite using `[← finsum_comp_equiv (MulAction.toPerm k₁ : Equiv.Perm (G ⧸ K))]`. Use `finsum_congr fun x => ?_` and prove the remaining obligations. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : K, (k₁ • x).out = k₁ * x.out * k := by`.

Rewrite using `[← MulAction.Quotient.mk_smul_out]`. Conclude with `QuotientGroup.mk_out_eq_mul K _`. Rewrite using `[MulAction.toPerm_apply, hk]`. Establish `e : h (k₁ * x.out * k) = h x.out` using `hh ⟨k₁, hk₁⟩ k _`. Rewrite using `[e]`.

Use `if_congr ⟨?_, ?_⟩ rfl rfl` and prove the remaining obligations. Introduce and unpack `⟨u, hu, k', hk', e'⟩`. Use `⟨k₂ * u * k₂⁻¹, hN u hu, k₂ * k' * (k : G)⁻¹, K.mul_mem (K.mul_mem hk₂ hk') (K.inv_mem k.2), ?_⟩` and prove the remaining obligations. Establish `: x.out = k₁⁻¹ * (k₁ * x.out * k) * (k : G)⁻¹` using `by group`. Rewrite using `[this, e']`.

Use `group`. Introduce and unpack `⟨u, hu, k', hk', e'⟩`. Use `⟨k₂⁻¹ * u * k₂, hN' u hu, k₂⁻¹ * k' * k, K.mul_mem (K.mul_mem (K.inv_mem hk₂) hk') k.2, ?_⟩` and prove the remaining obligations. Rewrite using `[e']`. Use `group`.
-/
theorem cellInv_holds : CellInv := by
  classical
  intro G _ K N h g k₁ k₂ hh hk₁ hk₂ hN hN'
  unfold cellSum
  rw [← finsum_comp_equiv (MulAction.toPerm k₁ : Equiv.Perm (G ⧸ K))]
  refine finsum_congr fun x => ?_
  obtain ⟨k, hk⟩ : ∃ k : K, (k₁ • x).out = k₁ * x.out * k := by
    rw [← MulAction.Quotient.mk_smul_out]
    exact QuotientGroup.mk_out_eq_mul K _
  rw [MulAction.toPerm_apply, hk]
  have e : h (k₁ * x.out * k) = h x.out := hh ⟨k₁, hk₁⟩ k _
  rw [e]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨u, hu, k', hk', e'⟩
    refine ⟨k₂ * u * k₂⁻¹, hN u hu, k₂ * k' * (k : G)⁻¹, K.mul_mem (K.mul_mem hk₂ hk') (K.inv_mem k.2), ?_⟩
    have : x.out = k₁⁻¹ * (k₁ * x.out * k) * (k : G)⁻¹ := by group
    rw [this, e']; group
  · rintro ⟨u, hu, k', hk', e'⟩
    refine ⟨k₂⁻¹ * u * k₂, hN' u hu, k₂⁻¹ * k' * k, K.mul_mem (K.mul_mem (K.inv_mem hk₂) hk') k.2, ?_⟩
    rw [e']; group

end GlobalTheory.SatakeWeyl
