import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
open NumberField

namespace GlobalTheory

/- English proof (translation)
Use `set c : G0 → LL := fun g => eC g * ((A.chi g)⁻¹ : LLˣ) with hc`. Establish `hchi : ∀ g k : G0, (((A.chi g)⁻¹ : LLˣ) : LL) * (((A.chi (g⁻¹ * k))⁻¹ : LLˣ) : LL) = (((A.chi k)⁻¹ : LLˣ) : LL)`. Introduce `g k`. Rewrite using `[← Units.val_mul, ← mul_inv, ← map_mul, mul_inv_cancel_left]`. Establish `hcc : ∀ k, ∑ g, c g * c (g⁻¹ * k) = c k`.

Introduce `k`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[hc, ← hchi g k]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = c k := by rw [← Finset.sum_mul, he k]`. Establish `hE : A.eOp eC = ∑ g, c g • A.ρ g` using `rfl`. Rewrite using `[← Module.End.mul_eq_comp, hE, Finset.sum_mul_sum]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[← Equiv.sum_comp (Equiv.mulLeft g) (fun k => (c g * c (g⁻¹ * k)) • A.ρ k)]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, smul_mul_smul_comm]`. Use `_ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • A.ρ k := by`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`. Use `_ = ∑ k, c k • A.ρ k := by`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hcc k]`.
-/
theorem eOp_comp_self_of_conv_idem {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL)
    (he : ∀ k, ∑ g, eC g * eC (g⁻¹ * k) = eC k) : A.eOp eC ∘ₗ A.eOp eC = A.eOp eC := by
  set c : G0 → LL := fun g => eC g * ((A.chi g)⁻¹ : LLˣ) with hc
  have hchi : ∀ g k : G0, (((A.chi g)⁻¹ : LLˣ) : LL) * (((A.chi (g⁻¹ * k))⁻¹ : LLˣ) : LL)
      = (((A.chi k)⁻¹ : LLˣ) : LL) := by
    intro g k
    rw [← Units.val_mul, ← mul_inv, ← map_mul, mul_inv_cancel_left]
  have hcc : ∀ k, ∑ g, c g * c (g⁻¹ * k) = c k := by
    intro k
    calc ∑ g, c g * c (g⁻¹ * k)
        = ∑ g, (eC g * eC (g⁻¹ * k)) * (((A.chi k)⁻¹ : LLˣ) : LL) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [hc, ← hchi g k]; ring
      _ = c k := by rw [← Finset.sum_mul, he k]
  have hE : A.eOp eC = ∑ g, c g • A.ρ g := rfl
  rw [← Module.End.mul_eq_comp, hE, Finset.sum_mul_sum]
  calc ∑ g, ∑ h, (c g • A.ρ g) * (c h • A.ρ h)
      = ∑ g, ∑ k, (c g * c (g⁻¹ * k)) • A.ρ k := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [← Equiv.sum_comp (Equiv.mulLeft g) (fun k => (c g * c (g⁻¹ * k)) • A.ρ k)]
        refine Finset.sum_congr rfl fun h _ => ?_
        simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, smul_mul_smul_comm]
    _ = ∑ k, (∑ g, c g * c (g⁻¹ * k)) • A.ρ k := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ k, c k • A.ρ k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcc k]

end GlobalTheory
