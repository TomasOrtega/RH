import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
open NumberField

namespace GlobalTheory

open Formalism.IndefR.Arith

/- English proof (translation)
Introduce `LL Ks _ _ _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G0 _ _ A eC hcl hint hMK J0 lam0 x hx`. Rewrite `hx`, the goal using `[FormsL.Mall, Submodule.mem_inf]`. Establish `hρspan : ∀ g, ∀ y ∈ Submodule.span (𝓞 LL) (A.MK : Set WL), A.ρ g y ∈ Submodule.span (𝓞 LL) (A.MK : Set WL)`. Introduce `g y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem z hz => exact Submodule.subset_span (hMK g z hz)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Submodule.add_mem _ ha hb`. Consider the case `smul r a _ ha`.

Rewrite using `[← algebraMap_smul LL r a, LinearMap.map_smul, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ r ha`. Establish `hchi : ∀ g, IsIntegral ℤ (((A.chi g)⁻¹ : LLˣ) : LL)`. Introduce `g`. Establish `h1 : ((A.chi g)⁻¹) ^ (orderOf g) = 1`.

Rewrite using `[← map_inv, ← map_pow, inv_pow, pow_orderOf_eq_one, inv_one, map_one]`. Use `IsIntegral.of_pow (orderOf_pos g) ?_` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, h1, Units.val_one]`. Conclude with `isIntegral_one`. Establish `hchic : ∀ p g : G0, A.chi (p * g * p⁻¹) = A.chi g`.

Introduce `p g`. Rewrite using `[map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[FormsL.eOp_apply, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Establish `hi : IsIntegral ℤ (((Fintype.card G0 : ℕ) : LL) * (eC g * ((A.chi g)⁻¹ : LLˣ)))`. Rewrite using `[← mul_assoc]`. Conclude with `(hint g).mul (hchi g)`. Take `⟨r, hr⟩ : ∃ r : 𝓞 LL, algebraMap (𝓞 LL) LL r = ((Fintype.card G0 : ℕ) : LL) * (eC g * ((A.chi g)⁻¹ : LLˣ))` from `⟨⟨_, hi⟩, rfl⟩`.

Rewrite using `[← hr, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ r (hρspan g x hx.1)`. Establish `hcomm : ∀ p : G0, A.ρ p (A.eOp eC x) = A.eOp eC (A.ρ p x)`. Introduce `p`. Rewrite using `[FormsL.eOp_apply, FormsL.eOp_apply, map_sum]`.

Simplify using `only [LinearMap.map_smul]`. Use `Fintype.sum_equiv (MulAut.conj p).toEquiv _ _ fun g => ?_` and prove the remaining obligations. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]`. Rewrite using `[hcl g p, hchic p g, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]`. Introduce `p`.

Use `show A.ρ p (((Fintype.card G0 : ℕ) : LL) • A.eOp eC x) = ((A.chi p * lam0 p : LLˣ) : LL) • (((Fintype.card G0 : ℕ) : LL) • A.eOp eC x)`. Rewrite using `[LinearMap.map_smul, hcomm, hx.2 p, LinearMap.map_smul, smul_comm]`.
-/
theorem card_smul_eOp_mem_Mall : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL),
    (∀ g h, eC (h * g * h⁻¹) = eC g) → (∀ g, IsIntegral ℤ ((Fintype.card G0 : LL) * eC g)) →
    (∀ g f, f ∈ A.MK → A.ρ g f ∈ A.MK) → ∀ (J0 : Subgroup G0) (lam0 : J0 →* LLˣ),
    ∀ x ∈ A.Mall J0 lam0, ((Fintype.card G0 : ℕ) : LL) • A.eOp eC x ∈ A.Mall J0 lam0 := by
  intro LL Ks _ _ _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G0 _ _ A eC hcl hint hMK J0 lam0 x hx
  classical
  rw [FormsL.Mall, Submodule.mem_inf] at hx ⊢
  have hρspan : ∀ g, ∀ y ∈ Submodule.span (𝓞 LL) (A.MK : Set WL),
      A.ρ g y ∈ Submodule.span (𝓞 LL) (A.MK : Set WL) := by
    intro g y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span (hMK g z hz)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
        rw [← algebraMap_smul LL r a, LinearMap.map_smul, algebraMap_smul]
        exact Submodule.smul_mem _ r ha
  have hchi : ∀ g, IsIntegral ℤ (((A.chi g)⁻¹ : LLˣ) : LL) := by
    intro g
    have h1 : ((A.chi g)⁻¹) ^ (orderOf g) = 1 := by
      rw [← map_inv, ← map_pow, inv_pow, pow_orderOf_eq_one, inv_one, map_one]
    refine IsIntegral.of_pow (orderOf_pos g) ?_
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    exact isIntegral_one
  have hchic : ∀ p g : G0, A.chi (p * g * p⁻¹) = A.chi g := by
    intro p g
    rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]
  constructor
  · rw [FormsL.eOp_apply, Finset.smul_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    rw [smul_smul]
    have hi : IsIntegral ℤ (((Fintype.card G0 : ℕ) : LL) * (eC g * ((A.chi g)⁻¹ : LLˣ))) := by
      rw [← mul_assoc]; exact (hint g).mul (hchi g)
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 LL, algebraMap (𝓞 LL) LL r =
        ((Fintype.card G0 : ℕ) : LL) * (eC g * ((A.chi g)⁻¹ : LLˣ)) := ⟨⟨_, hi⟩, rfl⟩
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (hρspan g x hx.1)
  · have hcomm : ∀ p : G0, A.ρ p (A.eOp eC x) = A.eOp eC (A.ρ p x) := by
      intro p
      rw [FormsL.eOp_apply, FormsL.eOp_apply, map_sum]
      simp only [LinearMap.map_smul]
      refine Fintype.sum_equiv (MulAut.conj p).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      rw [hcl g p, hchic p g, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
        inv_mul_cancel_right]
    intro p
    show A.ρ p (((Fintype.card G0 : ℕ) : LL) • A.eOp eC x) =
      ((A.chi p * lam0 p : LLˣ) : LL) • (((Fintype.card G0 : ℕ) : LL) • A.eOp eC x)
    rw [LinearMap.map_smul, hcomm, hx.2 p, LinearMap.map_smul, smul_comm]

end GlobalTheory
