import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.StepData

/- English proof (translation)
Introduce `k _ _ _ _ A B _ _ _ _ ϖ hϖ i μ Φ hsupp hper g g' hg hgi hg' hg'i`. Establish `hϖ0 : (ϖ : k) ≠ 0` using `ϖ.ne_zero`. Establish `hvp : valuation k ((ϖ : k) ^ (i + 1)) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff]`. Conclude with `pow_ne_zero _ hϖ0`.

Prove the components needed by the constructor for the conclusion. Introduce `x hx r s`. Establish `hΦ : Φ ((g'⁻¹ : GL B k).val * x * g.val) ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises.

Simplify using `only [om, h0, mul_zero]`. Establish `hz` using `hsupp _ hΦ`. Establish `hx' : (ϖ : k) ^ (i + 1) • x = ((ϖ : k) ^ (i + 1) • g'.val) * ((g'⁻¹ : GL B k).val * x * g.val) * (g⁻¹ : GL A k).val`. Rewrite using `[Matrix.smul_mul, Matrix.smul_mul]`. Use `congr 1`.

Simplify using `only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Establish `hint : IntM ((ϖ : k) ^ (i + 1) • x)` using `by rw [hx']; exact (hg'i.mul hz).mul hg`. Establish `h1 : valuation k ((ϖ : k) ^ (i + 1) * x r s) ≤ 1` using `hint r s`. Rewrite `h1` using `[map_mul]`.

Rewrite using `[Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel_left₀ hvp]`. Use `_ ≤ (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * 1 := by gcongr`. Use `_ = _ := mul_one _`.

Introduce `x y hy`. Establish `hy' : IntM (((ϖ : k) ^ (i + 1))⁻¹ • y)` using `fun r s => by show valuation k (((ϖ : k) ^ (i + 1))⁻¹ * y r s) ≤ 1`. Rewrite using `[map_mul, map_inv₀]`. Combine the equalities or inequalities in the displayed calculation. Establish `hc : (ϖ : k) * (ϖ : k) ^ i * ((ϖ : k) ^ (i + 1))⁻¹ = 1`.

Rewrite using `[pow_succ]`. Clear the denominators using the available nonvanishing facts. Establish `heq : (g'⁻¹ : GL B k).val * y * g.val = (ϖ : k) • ((g'⁻¹ : GL B k).val * (((ϖ : k) ^ (i + 1))⁻¹ • y) * ((ϖ : k) ^ i • g.val))`. Rewrite using `[Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul, hc, one_smul]`. Establish `hM : IntM ((g'⁻¹ : GL B k).val * (((ϖ : k) ^ (i + 1))⁻¹ • y) * ((ϖ : k) ^ i • g.val))` using `(hg'.mul hy').mul hgi`.

Establish `hmax : MaxM ((g'⁻¹ : GL B k).val * y * g.val)`. Rewrite using `[heq]`. Introduce `r s`. Rewrite using `[Matrix.smul_apply, smul_eq_mul, map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left zero_le hϖ (hM r s)`.

Simplify using `only [om, Matrix.mul_add, Matrix.add_mul, hper _ _ hmax]`.
-/
theorem om_support_period : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (ϖ : kˣ), valuation k (ϖ : k) < 1 → ∀ (i : ℕ)
    (μ : kˣ →* ℂˣ) (Φ : Matrix B A k → ℂ), (∀ x, Φ x ≠ 0 → IntM x) → (∀ x y, MaxM y → Φ (x + y) = Φ x) →
    ∀ (g : GL A k) (g' : GL B k), IntM (g⁻¹ : GL A k).val → IntM ((ϖ : k) ^ i • g.val) →
      IntM (g'⁻¹ : GL B k).val → IntM ((ϖ : k) ^ (i + 1) • g'.val) →
    (∀ x, om μ g g' Φ x ≠ 0 → ∀ r s, valuation k (x r s) ≤ valuation k (((ϖ ^ (i + 1))⁻¹ : kˣ) : k)) ∧
    (∀ x y, (∀ r s, valuation k (y r s) ≤ valuation k ((ϖ : k) ^ (i + 1))) → om μ g g' Φ (x + y) = om μ g g' Φ x) := by
  intro k _ _ _ _ A B _ _ _ _ ϖ hϖ i μ Φ hsupp hper g g' hg hgi hg' hg'i
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  have hvp : valuation k ((ϖ : k) ^ (i + 1)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact pow_ne_zero _ hϖ0
  constructor
  · intro x hx r s
    have hΦ : Φ ((g'⁻¹ : GL B k).val * x * g.val) ≠ 0 := by
      intro h0; apply hx; simp only [om, h0, mul_zero]
    have hz := hsupp _ hΦ
    have hx' : (ϖ : k) ^ (i + 1) • x = ((ϖ : k) ^ (i + 1) • g'.val) * ((g'⁻¹ : GL B k).val * x * g.val) *
        (g⁻¹ : GL A k).val := by
      rw [Matrix.smul_mul, Matrix.smul_mul]
      congr 1
      simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    have hint : IntM ((ϖ : k) ^ (i + 1) • x) := by rw [hx']; exact (hg'i.mul hz).mul hg
    have h1 : valuation k ((ϖ : k) ^ (i + 1) * x r s) ≤ 1 := hint r s
    rw [map_mul] at h1
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀]
    calc valuation k (x r s) = (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * (valuation k ((ϖ : k) ^ (i + 1)) * valuation k (x r s)) := by
          rw [inv_mul_cancel_left₀ hvp]
      _ ≤ (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  · intro x y hy
    have hy' : IntM (((ϖ : k) ^ (i + 1))⁻¹ • y) := fun r s => by
      show valuation k (((ϖ : k) ^ (i + 1))⁻¹ * y r s) ≤ 1
      rw [map_mul, map_inv₀]
      calc _ ≤ (valuation k ((ϖ : k) ^ (i + 1)))⁻¹ * valuation k ((ϖ : k) ^ (i + 1)) := by gcongr; exact hy r s
        _ = 1 := inv_mul_cancel₀ hvp
    have hc : (ϖ : k) * (ϖ : k) ^ i * ((ϖ : k) ^ (i + 1))⁻¹ = 1 := by
      rw [pow_succ]; field_simp
    have heq : (g'⁻¹ : GL B k).val * y * g.val = (ϖ : k) • ((g'⁻¹ : GL B k).val * (((ϖ : k) ^ (i + 1))⁻¹ • y) * ((ϖ : k) ^ i • g.val)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul, hc, one_smul]
    have hM : IntM ((g'⁻¹ : GL B k).val * (((ϖ : k) ^ (i + 1))⁻¹ • y) * ((ϖ : k) ^ i • g.val)) :=
      (hg'.mul hy').mul hgi
    have hmax : MaxM ((g'⁻¹ : GL B k).val * y * g.val) := by
      rw [heq]
      intro r s
      rw [Matrix.smul_apply, smul_eq_mul, map_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hϖ (hM r s)
    simp only [om, Matrix.mul_add, Matrix.add_mul, hper _ _ hmax]

end GlobalTheory.StepData
