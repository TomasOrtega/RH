import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨z₀, hz₀⟩ : ∃ z₀, θ z₀ ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Apply `hθ0` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Assume the negation of the conclusion as `hz`.

Conclude with `hc ⟨z, hz⟩`. Establish `hW : IsOpen {z | θ z ≠ 0}` using `isOpen_ne_fun hθ continuous_const`. Establish `hEq : Set.EqOn f₁ f₂ {z | θ z ≠ 0}` using `fun z hz => mul_right_cancel₀ hz (h z)`. Establish `hall` using `GlobalTheory.SCV.eqOn_of_eqOn_open isOpen_univ isPreconnected_univ h₁.differentiableOn h₂.differentiableOn hW ⟨z₀, hz₀⟩ (Set.subset_univ _) hEq`. Use function extensionality and compare the values at `z`.

Conclude with `hall (Set.mem_univ z)`.
-/
theorem entire_eq_of_mul_eq_mul_right {f₁ f₂ θ : E → ℂ} (h₁ : Differentiable ℂ f₁)
    (h₂ : Differentiable ℂ f₂) (hθ : Continuous θ) (hθ0 : θ ≠ 0)
    (h : ∀ z, f₁ z * θ z = f₂ z * θ z) : f₁ = f₂ := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, θ z₀ ≠ 0 := by
    by_contra hc
    apply hθ0
    funext z
    by_contra hz
    exact hc ⟨z, hz⟩
  have hW : IsOpen {z | θ z ≠ 0} := isOpen_ne_fun hθ continuous_const
  have hEq : Set.EqOn f₁ f₂ {z | θ z ≠ 0} := fun z hz => mul_right_cancel₀ hz (h z)
  have hall := GlobalTheory.SCV.eqOn_of_eqOn_open isOpen_univ isPreconnected_univ h₁.differentiableOn
    h₂.differentiableOn hW ⟨z₀, hz₀⟩ (Set.subset_univ _) hEq
  funext z
  exact hall (Set.mem_univ z)

/- English proof (translation)
Use `set F : E → E →L[ℂ] ℂ := fun z => (h z)⁻¹ • fderiv ℂ h z with hFdef`. Establish `hfd : Differentiable ℂ (fderiv ℂ h)`. Introduce `z`. Conclude with `(GlobalTheory.SCV.differentiableOn_fderiv isOpen_univ hd.differentiableOn).differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ z))`. Establish `hF : Differentiable ℂ F` using `(hd.inv h0).smul hfd`.

Establish `hFper : ∀ x, ∀ s ∈ S, F (x + s) = F x`. Introduce `x s hs`. Take `⟨c, hc⟩` from `hper s hs`. Establish `hc0 : c ≠ 0`. Introduce `hc0`.

Apply `h0 s` to reduce the goal to its premises. Use `hc 0` as an intermediate fact. Rewrite `this` using `[zero_add, hc0, zero_mul]`. Then use the resulting hypothesis. Establish `hfun : (fun z => h (z + s)) = fun z => c * h z` using `funext hc`. Establish `hder : fderiv ℂ h (x + s) = c • fderiv ℂ h x`.

Rewrite using `[← fderiv_comp_add_right, hfun, fderiv_const_mul (hd x) c]`. Simplify using `only [hFdef]`. Rewrite using `[hder, hc, smul_smul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc0, mul_one]`. Establish `hconst : ∀ z, F z = F 0` using `fun z => GlobalTheory.entire_apply_eq_of_periodic_of_span_real hF hS hFper z 0`. Establish `hdh : ∀ z, fderiv ℂ h z = h z • F 0`.

Introduce `z`. Rewrite using `[← hconst z, hFdef]`. Simplify using `only`. Rewrite using `[smul_smul, mul_inv_cancel₀ (h0 z), one_smul]`. Use `⟨F 0, fun z => ?_⟩` and prove the remaining obligations.

Establish `hG : ∀ y, HasFDerivAt (fun z => h z * Complex.exp (-(F 0) z)) (0 : E →L[ℂ] ℂ) y`. Introduce `y`. Establish `h1 : HasFDerivAt h (h y • F 0) y`. Rewrite using `[← hdh]`. Conclude with `(hd y).hasFDerivAt`.

Establish `h2 : HasFDerivAt (fun z => Complex.exp (-(F 0) z)) (Complex.exp (-(F 0) y) • (-(F 0))) y` using `((F 0).hasFDerivAt.neg).cexp`. Use `(h1.mul h2).congr_fderiv ?_` and prove the remaining obligations. Simplify using `only [smul_neg, smul_smul, mul_comm (h y), neg_add_cancel]`. Establish `hGc` using `is_const_of_fderiv_eq_zero (f := fun z => h z * Complex.exp (-(F 0) z)) (fun y => (hG y).differentiableAt) (fun y => (hG y).fderiv) z 0`. Simplify using `only [map_zero, neg_zero, Complex.exp_zero, mul_one] at hGc`.

Rewrite using `[← hGc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]`.
-/
theorem entire_eq_exp_linear_of_multiplier [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {h : E → ℂ} (hd : Differentiable ℂ h) (h0 : ∀ z, h z ≠ 0) {S : Set E}
    (hS : Submodule.span ℝ S = ⊤) (hper : ∀ s ∈ S, ∃ c : ℂ, ∀ z, h (z + s) = c * h z) :
    ∃ L : E →L[ℂ] ℂ, ∀ z, h z = h 0 * Complex.exp (L z) := by
  set F : E → E →L[ℂ] ℂ := fun z => (h z)⁻¹ • fderiv ℂ h z with hFdef
  have hfd : Differentiable ℂ (fderiv ℂ h) := by
    intro z
    exact (GlobalTheory.SCV.differentiableOn_fderiv isOpen_univ hd.differentiableOn).differentiableAt
      (isOpen_univ.mem_nhds (Set.mem_univ z))
  have hF : Differentiable ℂ F := (hd.inv h0).smul hfd
  have hFper : ∀ x, ∀ s ∈ S, F (x + s) = F x := by
    intro x s hs
    obtain ⟨c, hc⟩ := hper s hs
    have hc0 : c ≠ 0 := by
      intro hc0
      apply h0 s
      have := hc 0
      rwa [zero_add, hc0, zero_mul] at this
    have hfun : (fun z => h (z + s)) = fun z => c * h z := funext hc
    have hder : fderiv ℂ h (x + s) = c • fderiv ℂ h x := by
      rw [← fderiv_comp_add_right, hfun, fderiv_const_mul (hd x) c]
    simp only [hFdef]
    rw [hder, hc, smul_smul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  have hconst : ∀ z, F z = F 0 := fun z =>
    GlobalTheory.entire_apply_eq_of_periodic_of_span_real hF hS hFper z 0
  have hdh : ∀ z, fderiv ℂ h z = h z • F 0 := by
    intro z
    rw [← hconst z, hFdef]
    simp only
    rw [smul_smul, mul_inv_cancel₀ (h0 z), one_smul]
  refine ⟨F 0, fun z => ?_⟩
  have hG : ∀ y, HasFDerivAt (fun z => h z * Complex.exp (-(F 0) z)) (0 : E →L[ℂ] ℂ) y := by
    intro y
    have h1 : HasFDerivAt h (h y • F 0) y := by
      rw [← hdh]
      exact (hd y).hasFDerivAt
    have h2 : HasFDerivAt (fun z => Complex.exp (-(F 0) z)) (Complex.exp (-(F 0) y) • (-(F 0))) y :=
      ((F 0).hasFDerivAt.neg).cexp
    refine (h1.mul h2).congr_fderiv ?_
    simp only [smul_neg, smul_smul, mul_comm (h y), neg_add_cancel]
  have hGc := is_const_of_fderiv_eq_zero (f := fun z => h z * Complex.exp (-(F 0) z))
    (fun y => (hG y).differentiableAt) (fun y => (hG y).fderiv) z 0
  simp only [map_zero, neg_zero, Complex.exp_zero, mul_one] at hGc
  rw [← hGc, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

end General

/- English proof (translation)
Introduce `H1 H2 g τ hτ w h hd h0 hrel`. Take `⟨⟨hθd, hqp⟩, hθ0⟩` from `H1 g τ hτ`. Take `⟨-, hspan, -⟩` from `H2 g τ hτ`. Establish `hmult : ∀ n n' : Fin g → ℤ, ∀ z, h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z`. Introduce `n n'`.

Use `set A : (Fin g → ℂ) → ℂ := fun z => eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) with hA`. Establish `hAne : ∀ z, A z ≠ 0` using `fun z => by`. Simplify using `only [hA, eC]`. Conclude with `Complex.exp_ne_zero _`. Establish `hAw : ∀ z, A (z + w) = A z * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w))`.

Introduce `z`. Simplify using `only [hA]`. Rewrite using `[← eC_add, dotProduct_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hAc : Continuous A`. Simplify using `only [hA, eC]`. Conclude with `Complex.continuous_exp.comp (continuous_const.mul (continuous_const.mul (continuous_const.add (continuous_const.dotProduct continuous_id))))`. Establish `hne : (fun z => A z * theta 0 0 z τ) ≠ 0`. Introduce `hz`.

Apply `hθ0` to reduce the goal to its premises. Use function extensionality and compare the values at `z`. Use `congrFun hz z` as an intermediate fact. Simplify using `only [Pi.zero_apply, mul_eq_zero] at this`. Conclude with `this.resolve_left (hAne z)`.

Establish `hEq : ∀ z, h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) * (A z * theta 0 0 z τ) = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z * (A z * theta 0 0 z τ)`. Introduce `z`. Establish `e2 : theta 0 0 (z + (τ *ᵥ ofIntVec n + ofIntVec n')) τ = A z * theta 0 0 z τ`. Rewrite using `[← add_assoc]`. Conclude with `hqp n n' z`.

Establish `e3 : theta 0 0 (z + w + (τ *ᵥ ofIntVec n + ofIntVec n')) τ = A (z + w) * theta 0 0 (z + w) τ`. Rewrite using `[← add_assoc]`. Conclude with `hqp n n' (z + w)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hAw, hrel]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `z`. Conclude with `congrFun (entire_eq_of_mul_eq_mul_right (f₁ := fun z => h (z + (τ *ᵥ ofIntVec n + ofIntVec n'))) (f₂ := fun z => eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z) (hd.comp (differentiable_id.add_const _)) ((differentiable_const _).mul hd) (hAc.mul hθd.continuous) hne hEq) z`. Establish `hS : ∀ s ∈ (periodLattice τ : Set (Fin g → ℂ)), ∃ c : ℂ, ∀ z, h (z + s) = c * h z`. Introduce and unpack `s ⟨n, n', rfl⟩`.

Conclude with `⟨_, hmult n n'⟩`. Take `⟨L, hL⟩` from `entire_eq_exp_linear_of_multiplier hd h0 hspan hS`. Establish `hexp : ∀ n n' : Fin g → ℤ, Complex.exp (L (τ *ᵥ ofIntVec n + ofIntVec n')) = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w))`. Introduce `n n'`. Establish `e` using `hmult n n' 0`.

Rewrite `e` using `[zero_add]`. Establish `e' : h 0 * Complex.exp (L (τ *ᵥ ofIntVec n + ofIntVec n')) = h 0 * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w))`. Rewrite using `[← hL, e, mul_comm]`. Conclude with `mul_left_cancel₀ (h0 0) e'`. Establish `hk : ∀ j : Fin g, ∃ m : ℤ, L (Pi.single j 1) = m * (2 * Real.pi * Complex.I)`.

Introduce `j`. Establish `e` using `hexp 0 (Pi.single j 1)`. Establish `hv : τ *ᵥ ofIntVec (0 : Fin g → ℤ) + ofIntVec (Pi.single j 1) = Pi.single j 1`. Rewrite using `[ofIntVec_zero, mulVec_zero, zero_add]`. Use extensionality with `i`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[ofIntVec]`. Simplify using `[ofIntVec, hij]`. Rewrite `e` using `[hv, ofIntVec_zero, zero_dotProduct, mul_zero, eC_zero]`.

Conclude with `Complex.exp_eq_one_iff.mp e`. Use `choose k hk using hk`. Establish `hLz : ∀ z, L z = 2 * Real.pi * Complex.I * (ofIntVec k ⬝ᵥ z)`. Introduce `z`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hsi : (Pi.single i (z i) : Fin g → ℂ) = z i • (Pi.single i 1 : Fin g → ℂ)`. Use extensionality with `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`. Rewrite using `[hsi, map_smul, smul_eq_mul]`. Use `_ = 2 * Real.pi * Complex.I * (ofIntVec k ⬝ᵥ z) := by`.

Simplify using `only [hk, dotProduct, ofIntVec, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hm : ∀ j : Fin g, ∃ m : ℤ, w j + (τ *ᵥ ofIntVec k) j = m`. Introduce `j`.

Establish `e` using `hexp (Pi.single j 1) 0`. Rewrite `e` using `[ofIntVec_zero, add_zero, hLz]`. Establish `hdot1 : ofIntVec (Pi.single j 1) ⬝ᵥ w = w j`. Simplify using `[ofIntVec, dotProduct, Pi.single_apply]`. Establish `hdot2 : ofIntVec k ⬝ᵥ (τ *ᵥ ofIntVec (Pi.single j 1)) = (τ *ᵥ ofIntVec k) j`.

Rewrite using `[dot_mulVec_symm hτ.1]`. Simplify using `[ofIntVec, dotProduct, Pi.single_apply]`. Rewrite `e` using `[hdot1, hdot2]`. Unfold `eC at e`. Establish `e2 : Complex.exp (2 * Real.pi * Complex.I * (w j + (τ *ᵥ ofIntVec k) j)) = 1`.

Rewrite using `[mul_add, Complex.exp_add, e, ← Complex.exp_add, show 2 * (Real.pi : ℂ) * Complex.I * w j + 2 * Real.pi * Complex.I * (-(1 : ℂ) * w j) = 0 by ring, Complex.exp_zero]`. Take `⟨m, hm⟩` from `Complex.exp_eq_one_iff.mp e2`. Conclude with `⟨m, mul_left_cancel₀ Complex.two_pi_I_ne_zero (by rw [hm]; ring)⟩`. Use `choose m hm using hm`. Use `show ∃ n n' : Fin g → ℤ, w = τ *ᵥ ofIntVec n + ofIntVec n'`.

Use `⟨-k, m, ?_⟩` and prove the remaining obligations. Use extensionality with `j`. Establish `hj` using `hm j`. Rewrite using `[ofIntVec_neg, mulVec_neg, Pi.add_apply, Pi.neg_apply]`. Simplify using `only [ofIntVec] at hj ⊢`.

Take the linear combination `hj`.
-/
theorem mem_periodLattice_of_theta_translate_eq_unit_mul :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → (Differentiable ℂ (fun z => theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => theta 0 0 z τ) (z + τ *ᵥ ofIntVec n + ofIntVec n') = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) * (fun z => theta 0 0 z τ) z) ∧ (fun z => theta 0 0 z τ) ≠ 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → DiscreteTopology (periodLattice τ) ∧ Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) → ∀ (w : Fin g → ℂ) (h : (Fin g → ℂ) → ℂ), Differentiable ℂ h → (∀ z, h z ≠ 0) → (∀ z, theta 0 0 (z + w) τ = h z * theta 0 0 z τ) → w ∈ periodLattice τ) := by
  intro H1 H2 g τ hτ w h hd h0 hrel
  obtain ⟨⟨hθd, hqp⟩, hθ0⟩ := H1 g τ hτ
  obtain ⟨-, hspan, -⟩ := H2 g τ hτ
  have hmult : ∀ n n' : Fin g → ℤ, ∀ z, h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) =
      eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z := by
    intro n n'
    set A : (Fin g → ℂ) → ℂ := fun z =>
      eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) / 2 + ofIntVec n ⬝ᵥ z)) with hA
    have hAne : ∀ z, A z ≠ 0 := fun z => by
      simp only [hA, eC]
      exact Complex.exp_ne_zero _
    have hAw : ∀ z, A (z + w) = A z * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) := by
      intro z
      simp only [hA]
      rw [← eC_add, dotProduct_add]
      congr 1
      ring
    have hAc : Continuous A := by
      simp only [hA, eC]
      exact Complex.continuous_exp.comp (continuous_const.mul (continuous_const.mul
        (continuous_const.add (continuous_const.dotProduct continuous_id))))
    have hne : (fun z => A z * theta 0 0 z τ) ≠ 0 := by
      intro hz
      apply hθ0
      funext z
      have := congrFun hz z
      simp only [Pi.zero_apply, mul_eq_zero] at this
      exact this.resolve_left (hAne z)
    have hEq : ∀ z, h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) * (A z * theta 0 0 z τ) =
        eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z * (A z * theta 0 0 z τ) := by
      intro z
      have e2 : theta 0 0 (z + (τ *ᵥ ofIntVec n + ofIntVec n')) τ = A z * theta 0 0 z τ := by
        rw [← add_assoc]
        exact hqp n n' z
      have e3 : theta 0 0 (z + w + (τ *ᵥ ofIntVec n + ofIntVec n')) τ =
          A (z + w) * theta 0 0 (z + w) τ := by
        rw [← add_assoc]
        exact hqp n n' (z + w)
      calc h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) * (A z * theta 0 0 z τ)
          = h (z + (τ *ᵥ ofIntVec n + ofIntVec n')) *
              theta 0 0 (z + (τ *ᵥ ofIntVec n + ofIntVec n')) τ := by rw [e2]
        _ = theta 0 0 (z + (τ *ᵥ ofIntVec n + ofIntVec n') + w) τ := (hrel _).symm
        _ = theta 0 0 (z + w + (τ *ᵥ ofIntVec n + ofIntVec n')) τ := by rw [add_right_comm]
        _ = A (z + w) * theta 0 0 (z + w) τ := e3
        _ = eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z * (A z * theta 0 0 z τ) := by
          rw [hAw, hrel]
          ring
    intro z
    exact congrFun (entire_eq_of_mul_eq_mul_right
      (f₁ := fun z => h (z + (τ *ᵥ ofIntVec n + ofIntVec n')))
      (f₂ := fun z => eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) * h z)
      (hd.comp (differentiable_id.add_const _)) ((differentiable_const _).mul hd)
      (hAc.mul hθd.continuous) hne hEq) z
  have hS : ∀ s ∈ (periodLattice τ : Set (Fin g → ℂ)), ∃ c : ℂ, ∀ z, h (z + s) = c * h z := by
    rintro s ⟨n, n', rfl⟩
    exact ⟨_, hmult n n'⟩
  obtain ⟨L, hL⟩ := entire_eq_exp_linear_of_multiplier hd h0 hspan hS
  have hexp : ∀ n n' : Fin g → ℤ, Complex.exp (L (τ *ᵥ ofIntVec n + ofIntVec n')) =
      eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) := by
    intro n n'
    have e := hmult n n' 0
    rw [zero_add] at e
    have e' : h 0 * Complex.exp (L (τ *ᵥ ofIntVec n + ofIntVec n')) =
        h 0 * eC (-(1 : ℂ) * (ofIntVec n ⬝ᵥ w)) := by
      rw [← hL, e, mul_comm]
    exact mul_left_cancel₀ (h0 0) e'
  have hk : ∀ j : Fin g, ∃ m : ℤ, L (Pi.single j 1) = m * (2 * Real.pi * Complex.I) := by
    intro j
    have e := hexp 0 (Pi.single j 1)
    have hv : τ *ᵥ ofIntVec (0 : Fin g → ℤ) + ofIntVec (Pi.single j 1) = Pi.single j 1 := by
      rw [ofIntVec_zero, mulVec_zero, zero_add]
      ext i
      by_cases hij : i = j
      · subst hij
        simp [ofIntVec]
      · simp [ofIntVec, hij]
    rw [hv, ofIntVec_zero, zero_dotProduct, mul_zero, eC_zero] at e
    exact Complex.exp_eq_one_iff.mp e
  choose k hk using hk
  have hLz : ∀ z, L z = 2 * Real.pi * Complex.I * (ofIntVec k ⬝ᵥ z) := by
    intro z
    calc L z = L (∑ i, Pi.single i (z i)) := by rw [Finset.univ_sum_single]
      _ = ∑ i, z i * L (Pi.single i 1) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hsi : (Pi.single i (z i) : Fin g → ℂ) = z i • (Pi.single i 1 : Fin g → ℂ) := by
          ext j
          by_cases hj : j = i
          · subst hj
            simp
          · simp [hj]
        rw [hsi, map_smul, smul_eq_mul]
      _ = 2 * Real.pi * Complex.I * (ofIntVec k ⬝ᵥ z) := by
        simp only [hk, dotProduct, ofIntVec, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
  have hm : ∀ j : Fin g, ∃ m : ℤ, w j + (τ *ᵥ ofIntVec k) j = m := by
    intro j
    have e := hexp (Pi.single j 1) 0
    rw [ofIntVec_zero, add_zero, hLz] at e
    have hdot1 : ofIntVec (Pi.single j 1) ⬝ᵥ w = w j := by
      simp [ofIntVec, dotProduct, Pi.single_apply]
    have hdot2 : ofIntVec k ⬝ᵥ (τ *ᵥ ofIntVec (Pi.single j 1)) = (τ *ᵥ ofIntVec k) j := by
      rw [dot_mulVec_symm hτ.1]
      simp [ofIntVec, dotProduct, Pi.single_apply]
    rw [hdot1, hdot2] at e
    unfold eC at e
    have e2 : Complex.exp (2 * Real.pi * Complex.I * (w j + (τ *ᵥ ofIntVec k) j)) = 1 := by
      rw [mul_add, Complex.exp_add, e, ← Complex.exp_add,
        show 2 * (Real.pi : ℂ) * Complex.I * w j + 2 * Real.pi * Complex.I * (-(1 : ℂ) * w j) = 0 by
          ring, Complex.exp_zero]
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp e2
    exact ⟨m, mul_left_cancel₀ Complex.two_pi_I_ne_zero (by rw [hm]; ring)⟩
  choose m hm using hm
  show ∃ n n' : Fin g → ℤ, w = τ *ᵥ ofIntVec n + ofIntVec n'
  refine ⟨-k, m, ?_⟩
  ext j
  have hj := hm j
  rw [ofIntVec_neg, mulVec_neg, Pi.add_apply, Pi.neg_apply]
  simp only [ofIntVec] at hj ⊢
  linear_combination hj

end GlobalTheory
