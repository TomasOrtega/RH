import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DerivGA

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hm : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b`. Introduce `a b`. Simplify using `[toMK, toM]`. Establish `hi : ∀ a : KG ε, toMK a⁻¹ * toMK a = 1`. Introduce `a`.

Simplify using `[toMK, toM]`. Establish `hop : ∀ a b : KG ε, T.op (a * b) = T.op a * T.op b`. Introduce `a b`. Simplify using `[KType.op]`. Establish `hop1 : ∀ a : KG ε, T.op a⁻¹ * T.op a = 1`.

Introduce `a`. Simplify using `only [KType.op, map_inv]`. Rewrite using `[← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]`. Establish `hγ0 : γ 0 = 1`. Use extensionality with `i j`.

Establish `h00` using `congrFun (congrFun (hγ 0) i) j`. Simplify `h00` using `[toMK, toM]`. Establish `hk2 : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ toMK k * Jm ε = Jm ε * toMK k`. Simplify `k.2` using `[KG, Kset, toM, toMK]`. Establish `hst : star (toMK k) * toMK k = 1` using `Matrix.mem_unitaryGroup_iff'.1 hk2.1`.

Establish `hst' : toMK k * star (toMK k) = 1` using `Matrix.mem_unitaryGroup_iff.1 hk2.1`. Establish `hkinv : toMK k⁻¹ = (toMK k)ᴴ`. Rewrite using `[← Matrix.star_eq_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Establish `hinjk : Function.Injective (toMK k).mulVec`.

Introduce `v w hvw`. Establish `h2` using `congrArg (star (toMK k)).mulVec hvw`. Simplify `h2` using `[Matrix.mulVec_mulVec, hst]`. Establish `hzP : toMK k⁻¹ * x * toMK k ∈ OmegaSet n`. Apply `posSet_subset_omega` to reduce the goal to its premises.

Use `show (toMK k⁻¹ * x * toMK k).PosDef`. Rewrite using `[hkinv]`. Conclude with `hx.conjTranspose_mul_mul_same hinjk`. Establish `hexp : ∀ A : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp A * NormedSpace.exp (-A) = 1`. Introduce `A`.

Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl A)), add_neg_cancel, NormedSpace.exp_zero]`. Establish `hinvγ : ∀ t : ℝ, toMK (γ t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Y))`. Introduce `t`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hexp, mul_one]`.

Use `_ = (toMK (γ t)⁻¹ * toMK (γ t)) * NormedSpace.exp (-((t : ℂ) • Y)) := by`. Rewrite using `[hγ t, mul_assoc]`. Use `_ = _ := by rw [hi, one_mul]`. Establish `hf : ∀ t : ℝ, toMK (k * γ t)⁻¹ * x * toMK (k * γ t) = NormedSpace.exp (-((t : ℂ) • Y)) * (toMK k⁻¹ * x * toMK k) * NormedSpace.exp ((t : ℂ) • Y)`. Introduce `t`.

Rewrite using `[_root_.mul_inv_rev, hm, hm, hinvγ, hγ]`. Simplify using `only [mul_assoc]`. Establish `hQe : ∀ t : ℝ, T.op (1 * (γ t)⁻¹) * T.op k⁻¹ = T.op (k * γ t)⁻¹`. Introduce `t`. Rewrite using `[one_mul, _root_.mul_inv_rev, hop]`.

Establish `hfun : (fun t : ℝ => Gint T μ x (k * γ t)) = fun t : ℝ => PhiM μ (NormedSpace.exp (-((t : ℂ) • Y)) * (toMK k⁻¹ * x * toMK k) * NormedSpace.exp ((t : ℂ) • Y)) • (T.op (k * γ t) * projW T * (T.op (1 * (γ t)⁻¹) * T.op k⁻¹))`. Use function extensionality and compare the values at `t`. Simplify using `only [Gint]`. Rewrite using `[hf t, hQe t]`. Establish `hP` using `hasDerivAt_op T k hY γ hγ`.

Establish `hδ : ∀ t : ℝ, toMK ((fun s : ℝ => (γ s)⁻¹) t) = NormedSpace.exp ((t : ℂ) • (-Y))`. Introduce `t`. Rewrite using `[smul_neg]`. Conclude with `hinvγ t`. Establish `hQ` using `(hasDerivAt_op T 1 (inK_neg hY) (fun s : ℝ => (γ s)⁻¹) hδ).mul_const (T.op k⁻¹)`.

Establish `hM` using `(hP.mul_const (projW T)).mul hQ`. Establish `hφ : HasDerivAt (fun t : ℝ => PhiM μ (NormedSpace.exp (-((t : ℂ) • Y)) * (toMK k⁻¹ * x * toMK k) * NormedSpace.exp ((t : ℂ) • Y))) (fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k) (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k))) 0`. Establish `hd` using `((phiM_differentiableOn μ).differentiableAt (isOpen_omega.mem_nhds hzP)).hasFDerivAt`. Establish `h0 : toMK k⁻¹ * x * toMK k = NormedSpace.exp (-(((0 : ℝ) : ℂ) • Y)) * (toMK k⁻¹ * x * toMK k) * NormedSpace.exp (((0 : ℝ) : ℂ) • Y)`. Simplify using the standard rewrite rules.

Conclude with `(hd.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) (dga_path Y _) h0`. Establish `hop1' : T.op 1 = 1` using `by simp [KType.op]`. Rewrite using `[hfun]`. Use `hφ.smul hM using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals try rfl`.

Simplify using `only [hγ0, mul_one, one_mul, inv_one, hop1', map_neg, Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero]`. Rewrite using `[add_comm]`. Simplify using `only [Pi.mul_apply, hγ0, mul_one, inv_one, hop1', one_mul]`. Use `congrArg₂ (· + ·) (congrArg _ ?_) rfl` and prove the remaining obligations. Use `noncomm_ring`.
-/
theorem hasDerivAt_Gint {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y)
    (γ : ℝ → KG ε) (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) :
    HasDerivAt (fun t => Gint T μ x (k * γ t))
      (fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k)
          (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k)) •
          (T.op k * projW T * T.op k⁻¹) +
        PhiM μ (toMK k⁻¹ * x * toMK k) •
          (T.op k * (T.dτ Y * projW T - projW T * T.dτ Y) * T.op k⁻¹)) 0 := by
  have hm : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := by
    intro a b
    simp [toMK, toM]
  have hi : ∀ a : KG ε, toMK a⁻¹ * toMK a = 1 := by
    intro a
    simp [toMK, toM]
  have hop : ∀ a b : KG ε, T.op (a * b) = T.op a * T.op b := by
    intro a b
    simp [KType.op]
  have hop1 : ∀ a : KG ε, T.op a⁻¹ * T.op a = 1 := by
    intro a
    simp only [KType.op, map_inv]
    rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
  have hγ0 : γ 0 = 1 := by
    ext i j
    have h00 := congrFun (congrFun (hγ 0) i) j
    simpa [toMK, toM] using h00
  have hk2 : toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ toMK k * Jm ε = Jm ε * toMK k := by
    simpa [KG, Kset, toM, toMK] using k.2
  have hst : star (toMK k) * toMK k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk2.1
  have hst' : toMK k * star (toMK k) = 1 := Matrix.mem_unitaryGroup_iff.1 hk2.1
  have hkinv : toMK k⁻¹ = (toMK k)ᴴ := by
    rw [← Matrix.star_eq_conjTranspose]
    calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * star (toMK k)) := by rw [hst', mul_one]
      _ = (toMK k⁻¹ * toMK k) * star (toMK k) := by rw [mul_assoc]
      _ = star (toMK k) := by rw [hi, one_mul]
  have hinjk : Function.Injective (toMK k).mulVec := by
    intro v w hvw
    have h2 := congrArg (star (toMK k)).mulVec hvw
    simpa [Matrix.mulVec_mulVec, hst] using h2
  have hzP : toMK k⁻¹ * x * toMK k ∈ OmegaSet n := by
    apply posSet_subset_omega
    show (toMK k⁻¹ * x * toMK k).PosDef
    rw [hkinv]
    exact hx.conjTranspose_mul_mul_same hinjk
  have hexp : ∀ A : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
    intro A
    rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_right (Commute.refl A)), add_neg_cancel,
      NormedSpace.exp_zero]
  have hinvγ : ∀ t : ℝ, toMK (γ t)⁻¹ = NormedSpace.exp (-((t : ℂ) • Y)) := by
    intro t
    calc toMK (γ t)⁻¹
        = toMK (γ t)⁻¹ * (NormedSpace.exp ((t : ℂ) • Y) * NormedSpace.exp (-((t : ℂ) • Y))) := by
          rw [hexp, mul_one]
      _ = (toMK (γ t)⁻¹ * toMK (γ t)) * NormedSpace.exp (-((t : ℂ) • Y)) := by
          rw [hγ t, mul_assoc]
      _ = _ := by rw [hi, one_mul]
  have hf : ∀ t : ℝ, toMK (k * γ t)⁻¹ * x * toMK (k * γ t) =
      NormedSpace.exp (-((t : ℂ) • Y)) * (toMK k⁻¹ * x * toMK k) * NormedSpace.exp ((t : ℂ) • Y) := by
    intro t
    rw [_root_.mul_inv_rev, hm, hm, hinvγ, hγ]
    simp only [mul_assoc]
  have hQe : ∀ t : ℝ, T.op (1 * (γ t)⁻¹) * T.op k⁻¹ = T.op (k * γ t)⁻¹ := by
    intro t
    rw [one_mul, _root_.mul_inv_rev, hop]
  have hfun : (fun t : ℝ => Gint T μ x (k * γ t)) = fun t : ℝ =>
      PhiM μ (NormedSpace.exp (-((t : ℂ) • Y)) * (toMK k⁻¹ * x * toMK k) *
        NormedSpace.exp ((t : ℂ) • Y)) •
        (T.op (k * γ t) * projW T * (T.op (1 * (γ t)⁻¹) * T.op k⁻¹)) := by
    funext t
    simp only [Gint]
    rw [hf t, hQe t]
  have hP := hasDerivAt_op T k hY γ hγ
  have hδ : ∀ t : ℝ, toMK ((fun s : ℝ => (γ s)⁻¹) t) = NormedSpace.exp ((t : ℂ) • (-Y)) := by
    intro t
    rw [smul_neg]
    exact hinvγ t
  have hQ := (hasDerivAt_op T 1 (inK_neg hY) (fun s : ℝ => (γ s)⁻¹) hδ).mul_const (T.op k⁻¹)
  have hM := (hP.mul_const (projW T)).mul hQ
  have hφ : HasDerivAt (fun t : ℝ => PhiM μ (NormedSpace.exp (-((t : ℂ) • Y)) *
      (toMK k⁻¹ * x * toMK k) * NormedSpace.exp ((t : ℂ) • Y)))
      (fderiv ℂ (PhiM μ) (toMK k⁻¹ * x * toMK k)
        (toMK k⁻¹ * x * toMK k * Y - Y * (toMK k⁻¹ * x * toMK k))) 0 := by
    have hd := ((phiM_differentiableOn μ).differentiableAt (isOpen_omega.mem_nhds hzP)).hasFDerivAt
    have h0 : toMK k⁻¹ * x * toMK k = NormedSpace.exp (-(((0 : ℝ) : ℂ) • Y)) *
        (toMK k⁻¹ * x * toMK k) * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) := by
      simp
    exact (hd.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) (dga_path Y _) h0
  have hop1' : T.op 1 = 1 := by simp [KType.op]
  rw [hfun]
  convert hφ.smul hM using 1
  all_goals try rfl
  simp only [hγ0, mul_one, one_mul, inv_one, hop1', map_neg, Complex.ofReal_zero, zero_smul,
    neg_zero, NormedSpace.exp_zero]
  rw [add_comm]
  simp only [Pi.mul_apply, hγ0, mul_one, inv_one, hop1', one_mul]
  refine congrArg₂ (· + ·) (congrArg _ ?_) rfl
  noncomm_ring
