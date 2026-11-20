import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModPerm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFacSlash

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Establish `hex : ∀ t ∈ Tm m, ∃ (γ' : SL(2, ℤ)) (t' : ℕ × ℕ × ℕ), t' ∈ Tm m ∧ Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t'`. Introduce `t ht`. Apply `hnf_exists hm` to reduce the goal to its premises. Rewrite using `[Matrix.det_mul, perm_Tmat_det hm ht, Matrix.SpecialLinearGroup.det_coe, mul_one]`. Use `choose! g σ hσ hg using hex`.

Establish `hinvR : ∀ A : SL(2, ℤ), (A : Matrix (Fin 2) (Fin 2) ℤ) * ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1`. Introduce `A`. Rewrite using `[← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]`. Establish `hinvL : ∀ A : SL(2, ℤ), ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (A : Matrix (Fin 2) (Fin 2) ℤ) = 1`. Introduce `A`.

Rewrite using `[← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]`. Establish `hinj : Set.InjOn σ (Tm m)`. Introduce `t1 h1 t2 h2 he`. Establish `e1` using `hg t1 h1`. Establish `e2` using `hg t2 h2`.

Rewrite `e2` using `[← he]`. Establish `key : Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (Tmat t2 * (γ : Matrix (Fin 2) (Fin 2) ℤ))`. Rewrite using `[e1, e2, Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc, mul_assoc (g t1 : Matrix (Fin 2) (Fin 2) ℤ), hinvL, mul_one]`. Apply `hnf_unique hm h1 h2 (g t1 * (g t2)⁻¹)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, hinvR, mul_one]`. Use `_ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by`. Rewrite using `[key]`. Simplify using `only [mul_assoc]`. Use `_ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 := by`.

Rewrite using `[mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hinvR, mul_one]`. Establish `himg : (Tm m).image σ = Tm m`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `x hx`. Take `⟨t, ht, rfl⟩` from `Finset.mem_image.mp hx`.

Conclude with `hσ t ht`. Rewrite using `[Finset.card_image_of_injOn hinj]`. Establish `hprod : ∀ F : ℕ × ℕ × ℕ → ℂ, ∏ t ∈ Tm m, F (σ t) = ∏ t ∈ Tm m, F t`. Introduce `F`. Use `conv_rhs => rw [← himg]`.

Rewrite using `[Finset.prod_image hinj]`. Establish `hfac : ∏ t ∈ Tm m, fac (σ t) τ = ∏ t ∈ Tm m, fac t τ` using `hprod (fun t => fac t τ)`. Establish `hden : ∏ t ∈ Tm m, ((σ t).2.2 : ℂ) = ∏ t ∈ Tm m, (t.2.2 : ℂ)` using `hprod (fun t => (t.2.2 : ℂ))`. Establish `hne : ∏ t ∈ Tm m, (t.2.2 : ℂ) ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`.

Introduce `t ht`. Conclude with `(Tm_pos hm ht).2.ne'` after adjusting the coercions. Establish `hstep : ∏ t ∈ Tm m, fac t (γ • τ) = ∏ t ∈ Tm m, (denom γ τ ^ 24 * ((t.2.2 : ℂ) / (σ t).2.2) ^ 12 * fac (σ t) τ)` using `Finset.prod_congr rfl (fun t ht => fac_smul (Tm_pos hm ht) (Tm_pos hm (hσ t ht)) γ (g t) (hg t ht) τ)`. Unfold `Gm`. Rewrite using `[hstep, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, hfac, Finset.prod_pow, Finset.prod_div_distrib, hden, div_self hne, one_pow, mul_one]`.
-/
theorem Gm_smul {m : ℕ} (hm : 0 < m) (γ : SL(2, ℤ)) (τ : ℍ) :
    Gm m (γ • τ) = denom γ τ ^ (24 * (Tm m).card) * Gm m τ := by
  classical
  have hex : ∀ t ∈ Tm m, ∃ (γ' : SL(2, ℤ)) (t' : ℕ × ℕ × ℕ), t' ∈ Tm m ∧
      Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t' := by
    intro t ht
    apply hnf_exists hm
    rw [Matrix.det_mul, perm_Tmat_det hm ht, Matrix.SpecialLinearGroup.det_coe, mul_one]
  choose! g σ hσ hg using hex
  have hinvR : ∀ A : SL(2, ℤ),
      (A : Matrix (Fin 2) (Fin 2) ℤ) * ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinvL : ∀ A : SL(2, ℤ),
      ((A⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (A : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    intro A
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hinj : Set.InjOn σ (Tm m) := by
    intro t1 h1 t2 h2 he
    have e1 := hg t1 h1
    have e2 := hg t2 h2
    rw [← he] at e2
    have key : Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
          (Tmat t2 * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
      rw [e1, e2, Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc, mul_assoc (g t1 : Matrix (Fin 2) (Fin 2) ℤ),
        hinvL, mul_one]
    apply hnf_unique hm h1 h2 (g t1 * (g t2)⁻¹)
    calc Tmat t1 = Tmat t1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [mul_assoc, hinvR, mul_one]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 *
            (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [key]; simp only [mul_assoc]
      _ = ((g t1 * (g t2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t2 := by
          rw [mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hinvR, mul_one]
  have himg : (Tm m).image σ = Tm m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      exact hσ t ht
    · rw [Finset.card_image_of_injOn hinj]
  have hprod : ∀ F : ℕ × ℕ × ℕ → ℂ, ∏ t ∈ Tm m, F (σ t) = ∏ t ∈ Tm m, F t := by
    intro F
    conv_rhs => rw [← himg]
    rw [Finset.prod_image hinj]
  have hfac : ∏ t ∈ Tm m, fac (σ t) τ = ∏ t ∈ Tm m, fac t τ := hprod (fun t => fac t τ)
  have hden : ∏ t ∈ Tm m, ((σ t).2.2 : ℂ) = ∏ t ∈ Tm m, (t.2.2 : ℂ) := hprod (fun t => (t.2.2 : ℂ))
  have hne : ∏ t ∈ Tm m, (t.2.2 : ℂ) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro t ht
    exact_mod_cast (Tm_pos hm ht).2.ne'
  have hstep : ∏ t ∈ Tm m, fac t (γ • τ) =
      ∏ t ∈ Tm m, (denom γ τ ^ 24 * ((t.2.2 : ℂ) / (σ t).2.2) ^ 12 * fac (σ t) τ) :=
    Finset.prod_congr rfl (fun t ht => fac_smul (Tm_pos hm ht) (Tm_pos hm (hσ t ht)) γ (g t) (hg t ht) τ)
  unfold Gm
  rw [hstep, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, hfac,
    Finset.prod_pow, Finset.prod_div_distrib, hden, div_self hne, one_pow, mul_one]

end ReciprocityTheory.ChartRestriction.L1
