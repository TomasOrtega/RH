import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open Matrix
open scoped Matrix ComplexOrder ENNReal

noncomputable section

/- English proof (translation)
Introduce `f p q s hs Γ hd hU`. Take `⟨c, hc, hsepΓ⟩` from `sumBd_sep Γ hd hU`. Take `⟨C, hC, hbound⟩` from `sumBd_sum (p := p) (q := q) (f := f) hs hc`. Use `⟨C, hC, fun v hv => ?_⟩` and prove the remaining obligations. Use `choose G hG hGw using fun k => sumBd_frame (hv k)`.

Set `x : Γ → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ` to `fun γ k => ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * G k`. Establish `hxU : ∀ a k, IsUpq (x a k)` using `fun a k => sumBd_isUpq_mul (hU a.1 a.2 k) (hG k)`. Establish `hxsep : ∀ a b : Γ, a ≠ b → ∃ k i j, c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖`. Introduce `a b hab`. Establish `hmem : b.1 * a.1⁻¹ ∈ Γ` using `Γ.mul_mem b.2 (Γ.inv_mem a.2)`.

Establish `hne : b.1 * a.1⁻¹ ≠ 1` using `fun h => hab (Subtype.ext (mul_inv_eq_one.mp h).symm)`. Take `⟨k, i, j, hk⟩` from `hsepΓ _ hmem hne`. Use `⟨k, i, j, le_of_le_of_eq hk ?_⟩` and prove the remaining obligations. Establish `: x b k * (x a k)⁻¹ = (((b.1 * a.1⁻¹) k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)`. Simplify using `only [x, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv]`.

Rewrite using `[Matrix.mul_inv_rev]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (G k), sumBd_mul_inv (hG k), Matrix.one_mul]`. Rewrite using `[this]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `γ`. Rewrite using `[Finset.prod_congr rfl fun k _ => hGw k _ (hU γ.1 γ.2 k) s]`. Use `_ ≤ C := hbound Γ x hxU hxsep`.
-/
theorem SumBoundStatement_holds : SumBoundStatement := by
  intro f p q s hs Γ hd hU
  obtain ⟨c, hc, hsepΓ⟩ := sumBd_sep Γ hd hU
  obtain ⟨C, hC, hbound⟩ := sumBd_sum (p := p) (q := q) (f := f) hs hc
  refine ⟨C, hC, fun v hv => ?_⟩
  choose G hG hGw using fun k => sumBd_frame (hv k)
  let x : Γ → Fin f → Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fun γ k =>
    ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * G k
  have hxU : ∀ a k, IsUpq (x a k) := fun a k => sumBd_isUpq_mul (hU a.1 a.2 k) (hG k)
  have hxsep : ∀ a b : Γ, a ≠ b → ∃ k i j,
      c ≤ ‖(x b k * (x a k)⁻¹) i j - (1 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) i j‖ := by
    intro a b hab
    have hmem : b.1 * a.1⁻¹ ∈ Γ := Γ.mul_mem b.2 (Γ.inv_mem a.2)
    have hne : b.1 * a.1⁻¹ ≠ 1 := fun h => hab (Subtype.ext (mul_inv_eq_one.mp h).symm)
    obtain ⟨k, i, j, hk⟩ := hsepΓ _ hmem hne
    refine ⟨k, i, j, le_of_le_of_eq hk ?_⟩
    have : x b k * (x a k)⁻¹ = (((b.1 * a.1⁻¹) k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
      simp only [x, Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.coe_units_inv]
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (G k), sumBd_mul_inv (hG k), Matrix.one_mul]
    rw [this]
  calc ∑' γ : Γ, ENNReal.ofReal (∏ k, dpow (mob ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Zof v k)) s)
      = ∑' γ : Γ, ENNReal.ofReal (∏ k, (Complex.normSq (det (x γ k).toBlocks₂₂))⁻¹ ^ s) := by
        congr 1; funext γ
        rw [Finset.prod_congr rfl fun k _ => hGw k _ (hU γ.1 γ.2 k) s]
    _ ≤ C := hbound Γ x hxU hxsep

end
end ReciprocityTheory.ChartRestriction.G.AR.Up
