import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
open NumberField

open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `LL Ks _ _ _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G0 _ _ A eC σ hid hu hc x y`. Establish `hunit : ∀ g : G0, starRingEnd ℂ (σ ((A.chi g : LLˣ) : LL)) = (σ ((A.chi g : LLˣ) : LL))⁻¹`. Introduce `g`. Use `set z := σ ((A.chi g : LLˣ) : LL)`. Establish `hpow : z ^ orderOf g = 1`.

Establish `h1 : A.chi g ^ orderOf g = 1` using `by rw [← map_pow, pow_orderOf_eq_one, map_one]`. Establish `h2 : ((A.chi g : LLˣ) : LL) ^ orderOf g = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, h1, Units.val_one]`. Simplify using `only [z]`. Rewrite using `[← map_pow, h2, map_one]`.

Establish `hn : ‖z‖ = 1` using `Complex.norm_eq_one_of_pow_eq_one hpow (orderOf_pos g).ne'`. Establish `hz : z ≠ 0` using `by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn`. Establish `hm : z * starRingEnd ℂ z = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]`. Simplify using the standard rewrite rules.

Conclude with `eq_inv_of_mul_eq_one_right hm`. Establish `key : ∀ g u v, ⟪A.j σ (A.ρ g u), A.j σ v⟫_ℂ = ⟪A.j σ u, A.j σ (A.ρ g⁻¹ v)⟫_ℂ`. Introduce `g u v`. Establish `h1 : A.ρ g (A.ρ g⁻¹ v) = v`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.

Rewrite using `[← hu g u (A.ρ g⁻¹ v), h1]`. Establish `sa : ∀ u v, ⟪A.j σ (A.eOp eC u), A.j σ v⟫_ℂ = ⟪A.j σ u, A.j σ (A.eOp eC v)⟫_ℂ`. Introduce `u v`. Simplify using `only [Formalism.IndefR.Arith.FormsL.eOp_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum, inner_smul_left, inner_smul_right]`. Use `conv_rhs => rw [← Equiv.sum_comp (Equiv.inv G0)]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[key g, Equiv.inv_apply]`. Use `congr 1`. Rewrite using `[map_mul, map_mul, map_mul, hc, map_inv, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, map_inv₀, hunit]`. Simplify using `only [Units.val_inv_eq_inv_val, map_inv₀, inv_inv]`.

Establish `horth : ⟪A.j σ (A.eOp eC x), A.j σ (y - A.eOp eC y)⟫_ℂ = 0`. Establish `hy : A.eOp eC (A.eOp eC y) = A.eOp eC y` using `LinearMap.congr_fun hid y`. Rewrite using `[sa, map_sub, hy, sub_self, map_zero, inner_zero_right]`. Rewrite using `[map_add]`. Establish `h` using `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth`.

Simplify `h` using `only [sq]`.
-/
theorem twistedProjector_orthogonal_of_unitary : ∀ {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
    {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    {G0 : Type} [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (eC : G0 → LL), ∀ σ : LL →+* ℂ, A.eOp eC ∘ₗ A.eOp eC = A.eOp eC →
    (∀ g x y, inner ℂ (A.j σ (A.ρ g x)) (A.j σ (A.ρ g y)) = inner ℂ (A.j σ x) (A.j σ y)) →
    (∀ g, σ (eC g⁻¹) = starRingEnd ℂ (σ (eC g))) →
    ∀ x y, ‖A.j σ (A.eOp eC x + (y - A.eOp eC y))‖ ^ 2 = ‖A.j σ (A.eOp eC x)‖ ^ 2 + ‖A.j σ (y - A.eOp eC y)‖ ^ 2 := by
  intro LL Ks _ _ _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G0 _ _ A eC σ hid hu hc x y
  have hunit : ∀ g : G0, starRingEnd ℂ (σ ((A.chi g : LLˣ) : LL)) = (σ ((A.chi g : LLˣ) : LL))⁻¹ := by
    intro g
    set z := σ ((A.chi g : LLˣ) : LL)
    have hpow : z ^ orderOf g = 1 := by
      have h1 : A.chi g ^ orderOf g = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      have h2 : ((A.chi g : LLˣ) : LL) ^ orderOf g = 1 := by
        rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
      simp only [z]; rw [← map_pow, h2, map_one]
    have hn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow (orderOf_pos g).ne'
    have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
    have hm : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    exact eq_inv_of_mul_eq_one_right hm
  have key : ∀ g u v, ⟪A.j σ (A.ρ g u), A.j σ v⟫_ℂ = ⟪A.j σ u, A.j σ (A.ρ g⁻¹ v)⟫_ℂ := by
    intro g u v
    have h1 : A.ρ g (A.ρ g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← hu g u (A.ρ g⁻¹ v), h1]
  have sa : ∀ u v, ⟪A.j σ (A.eOp eC u), A.j σ v⟫_ℂ = ⟪A.j σ u, A.j σ (A.eOp eC v)⟫_ℂ := by
    intro u v
    simp only [Formalism.IndefR.Arith.FormsL.eOp_apply, map_sum, map_smulₛₗ, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right]
    conv_rhs => rw [← Equiv.sum_comp (Equiv.inv G0)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [key g, Equiv.inv_apply]
    congr 1
    rw [map_mul, map_mul, map_mul, hc, map_inv, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
      map_inv₀, map_inv₀, map_inv₀, hunit]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
  have horth : ⟪A.j σ (A.eOp eC x), A.j σ (y - A.eOp eC y)⟫_ℂ = 0 := by
    have hy : A.eOp eC (A.eOp eC y) = A.eOp eC y := LinearMap.congr_fun hid y
    rw [sa, map_sub, hy, sub_self, map_zero, inner_zero_right]
  rw [map_add]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  simpa only [sq] using h

end GlobalTheory
