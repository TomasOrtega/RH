import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitScalarMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeparableCharpolyConstSmul
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

namespace GlobalTheory.ExtChar

/- English proof (translation)
Introduce `n _ ε μ' _ V _ _ _ m π' π h' hext Θ' hΘ g hg`. Establish `hcen : ∀ j : ZMod n, Θ' (cen ε j * g) = (((ZMod.toCircle j : Circle) : ℂ) ^ m)⁻¹ * Θ' g`. Introduce `j`. Use `set ζ : Circle := ZMod.toCircle j`. Establish `h1mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε`.

Simplify using `using GlobalTheory.SUChar.suMat_mem ε 1`. Establish `hmat : GlobalTheory.SUChar.suMat ε (cen ε j) = ((ζ : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[suMat_cen]`. Use `show ((ζ⁻¹ : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = _`. Rewrite using `[Circle.coe_inv]`.

Establish `hmem : ((ζ : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε` using `hmat ▸ GlobalTheory.SUChar.suMat_mem ε (cen ε j)`. Establish `hnorm : ‖(ζ : ℂ)⁻¹‖ = 1` using `by rw [norm_inv, Circle.norm_coe, inv_one]`. Establish `e1` using `hext 1 (by simp) _ hmem`. Establish `e2` using `hext (ζ : ℂ)⁻¹ hnorm 1 h1mem`. Rewrite `e1` using `[one_smul, _root_.one_zpow, one_smul]`.

Establish `hone : π' 1 = 1` using `h'.1.1`. Establish `hrep : ∀ v, GlobalTheory.SUChar.suRep h' (cen ε j) v = ((ζ : ℂ) ^ m)⁻¹ • v`. Introduce `v`. Use `show π' (GlobalTheory.SUChar.suMat ε (cen ε j)) v = _`. Rewrite using `[hmat, ← e1, e2, hone, _root_.inv_zpow]`.

Both sides reduce to the same expression. Establish `hne : ((ζ : ℂ) ^ m)⁻¹ ≠ 0` using `inv_ne_zero (zpow_ne_zero _ (by simp))`. Conclude with `GlobalTheory.CentralCharSU.charFn_central_mul n ε μ' V π' h' Θ' hΘ (cen ε j) _ _ hmat hne hrep g hg`. Rewrite using `[avgChar]`. Establish `hz : ∀ j : ZMod n, ((ZMod.toCircle j : Circle) : ℂ) ^ m * Θ' (cen ε j * g) = Θ' g`.

Introduce `j`. Rewrite using `[hcen, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (by simp)), one_mul]`. Simplify using `only [hz, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast NeZero.ne n), one_mul]`.
-/
theorem avgChar_eq_of_ext : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h' : IsURepOn (SUset ε) π'), Ext ε m π' π → ∀ Θ' : SUJ ε → ℂ, IsCharFn (suMat ε) μ' (suRep h') Θ' → ∀ g : SUJ ε, IsRegSS (suMat ε g) → GlobalTheory.ExtChar.avgChar ε m Θ' g = Θ' g := by
  intro n _ ε μ' _ V _ _ _ m π' π h' hext Θ' hΘ g hg
  have hcen : ∀ j : ZMod n, Θ' (cen ε j * g) = (((ZMod.toCircle j : Circle) : ℂ) ^ m)⁻¹ * Θ' g := by
    intro j
    set ζ : Circle := ZMod.toCircle j
    have h1mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
      simpa using GlobalTheory.SUChar.suMat_mem ε 1
    have hmat : GlobalTheory.SUChar.suMat ε (cen ε j) = ((ζ : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [suMat_cen]
      show ((ζ⁻¹ : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = _
      rw [Circle.coe_inv]
    have hmem : ((ζ : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := hmat ▸ GlobalTheory.SUChar.suMat_mem ε (cen ε j)
    have hnorm : ‖(ζ : ℂ)⁻¹‖ = 1 := by rw [norm_inv, Circle.norm_coe, inv_one]
    have e1 := hext 1 (by simp) _ hmem
    have e2 := hext (ζ : ℂ)⁻¹ hnorm 1 h1mem
    rw [one_smul, _root_.one_zpow, one_smul] at e1
    have hone : π' 1 = 1 := h'.1.1
    have hrep : ∀ v, GlobalTheory.SUChar.suRep h' (cen ε j) v = ((ζ : ℂ) ^ m)⁻¹ • v := by
      intro v
      show π' (GlobalTheory.SUChar.suMat ε (cen ε j)) v = _
      rw [hmat, ← e1, e2, hone, _root_.inv_zpow]
      rfl
    have hne : ((ζ : ℂ) ^ m)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by simp))
    exact GlobalTheory.CentralCharSU.charFn_central_mul n ε μ' V π' h' Θ' hΘ (cen ε j) _ _ hmat hne hrep g hg
  rw [avgChar]
  have hz : ∀ j : ZMod n, ((ZMod.toCircle j : Circle) : ℂ) ^ m * Θ' (cen ε j * g) = Θ' g := by
    intro j
    rw [hcen, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (by simp)), one_mul]
  simp only [hz, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast NeZero.ne n), one_mul]

end GlobalTheory.ExtChar
