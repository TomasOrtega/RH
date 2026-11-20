import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.HodgeChart

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in

/- English proof (translation)
Introduce `n a g rk ha ρ τ₀ B hr hr1 hrk hholo hsymm hpsd hsupp htoric habel`. Use `set cst : ℂ := (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) with hcst`. Establish `him : cst.im = -Real.log ρ / (2 * Real.pi)`. Establish `hp : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Establish `e : cst = ((-Real.log ρ / (2 * Real.pi) : ℝ) : ℂ) * Complex.I`.

Rewrite using `[hcst]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, Complex.im_ofReal_mul, Complex.I_im, _root_.mul_one]`. Establish `hBs : ∀ i (j k : Fin g), B i k j = B i j k` using `fun i j k => by`. Use `(hpsd i).isHermitian.apply j k` as an intermediate fact. Simplify using `at this`. Conclude with `this` after adjusting the coercions.

Establish `hmaps : ∀ z ∈ polydisc n 1, ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ`. Introduce `u hu`. Rewrite using `[mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le]`. Establish `: ‖u‖ < 1` using `(pi_norm_lt_iff one_pos).2 hu`. Combine the equalities or inequalities in the displayed calculation.

Establish `hdiff : DifferentiableOn ℂ (fun z : Fin n → ℂ => ρ • z) (polydisc n 1)` using `((differentiable_id.const_smul (ρ : ℂ)).differentiableOn).congr fun u _ => by`. Use function extensionality and compare the values at `k`. Simplify using `[Complex.real_smul]`. Use `⟨⟨hrk, fun j k => ?_, fun z hz => ?_, hpsd, hsupp, htoric, fun z hz => ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations. Establish `h1` using `(hholo j k).comp hdiff hmaps`.

Use `(h1.add (differentiableOn_const (∑ i, cst * (B i j k : ℂ)))).congr fun z _ => ?_` and prove the remaining obligations. Simplify using `[Matrix.add_apply, Matrix.sum_apply, Function.comp]`. Use `Matrix.IsSymm.ext fun j k => ?_` and prove the remaining obligations. Use `(hsymm _ (hmaps z hz)).apply j k` as an intermediate fact. Simplify using `only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, hBs, this]`.

Establish `h1` using `habel _ (hmaps z hz)`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `⟨j, hj⟩ ⟨k, hk⟩`. Simplify using `[Matrix.sum_apply, hsupp _ j k (Or.inl hj)]`. Establish `hρu : ρ • (ρ⁻¹ • u) = u` using `smul_inv_smul₀ hr.ne' u`.

Use extensionality with `j k`. Establish `hu' : ∀ i : Fin a, tlog ((ρ⁻¹ • u) (Fin.castLE ha i)) = Real.log ρ / (2 * Real.pi) + tlog (u (Fin.castLE ha i))`. Introduce `i`. Rewrite using `[Pi.smul_apply, tlog, tlog, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, Real.log_mul (inv_pos.2 hr).ne' (norm_ne_zero_iff.2 (hu i)), Real.log_inv]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [hodgeGram, imPeriod, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, hu', hρu, Complex.add_im, Complex.im_sum, smul_eq_mul]`. Use `push_cast`. Simplify using `only [Complex.smul_im, Complex.intCast_im, Complex.intCast_re, smul_eq_mul, him, add_mul, Finset.sum_add_distrib]`. Simplify using `only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero, add_zero, him]`. Use `push_cast`.

Simplify using `only [zero_add]`. Simplify using `only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem periodChart_rescale_ball : ∀ (n a g rk : ℕ) (ha : a ≤ n) (ρ : ℝ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ → ρ ≤ 1 → rk ≤ g → (∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (τ₀ z).IsSymm) → (∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0) → (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B ∧ ∀ z : Fin n → ℂ, (∀ i : Fin a, z (Fin.castLE ha i) ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B (ρ⁻¹ • z) = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z := by
  intro n a g rk ha ρ τ₀ B hr hr1 hrk hholo hsymm hpsd hsupp htoric habel
  set cst : ℂ := (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) with hcst
  have him : cst.im = -Real.log ρ / (2 * Real.pi) := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e : cst = ((-Real.log ρ / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hcst]; push_cast; field_simp; rw [Complex.I_sq]; ring
    rw [e, Complex.im_ofReal_mul, Complex.I_im, _root_.mul_one]
  have hBs : ∀ i (j k : Fin g), B i k j = B i j k := fun i j k => by
    have := (hpsd i).isHermitian.apply j k
    simp at this
    exact_mod_cast this
  have hmaps : ∀ z ∈ polydisc n 1, ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    intro u hu
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le]
    have : ‖u‖ < 1 := (pi_norm_lt_iff one_pos).2 hu
    calc ρ * ‖u‖ < ρ * 1 := by gcongr
      _ = ρ := _root_.mul_one ρ
  have hdiff : DifferentiableOn ℂ (fun z : Fin n → ℂ => ρ • z) (polydisc n 1) :=
    ((differentiable_id.const_smul (ρ : ℂ)).differentiableOn).congr fun u _ => by
      funext k; simp [Complex.real_smul]
  refine ⟨⟨hrk, fun j k => ?_, fun z hz => ?_, hpsd, hsupp, htoric, fun z hz => ?_⟩, fun u hu => ?_⟩
  · have h1 := (hholo j k).comp hdiff hmaps
    refine (h1.add (differentiableOn_const (∑ i, cst * (B i j k : ℂ)))).congr fun z _ => ?_
    simp [Matrix.add_apply, Matrix.sum_apply, Function.comp]
  · refine Matrix.IsSymm.ext fun j k => ?_
    have := (hsymm _ (hmaps z hz)).apply j k
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, hBs, this]
  · have h1 := habel _ (hmaps z hz)
    convert h1 using 1
    ext ⟨j, hj⟩ ⟨k, hk⟩
    simp [Matrix.sum_apply, hsupp _ j k (Or.inl hj)]
  · have hρu : ρ • (ρ⁻¹ • u) = u := smul_inv_smul₀ hr.ne' u
    ext j k
    have hu' : ∀ i : Fin a, tlog ((ρ⁻¹ • u) (Fin.castLE ha i)) = Real.log ρ / (2 * Real.pi) + tlog (u (Fin.castLE ha i)) := by
      intro i
      rw [Pi.smul_apply, tlog, tlog, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le,
        Real.log_mul (inv_pos.2 hr).ne' (norm_ne_zero_iff.2 (hu i)), Real.log_inv]
      ring
    simp only [hodgeGram, imPeriod, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      hu', hρu, Complex.add_im, Complex.im_sum, smul_eq_mul]
    push_cast
    simp only [Complex.smul_im, Complex.intCast_im, Complex.intCast_re, smul_eq_mul, him, add_mul, Finset.sum_add_distrib]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero, add_zero, him]
    push_cast
    simp only [zero_add]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

end GlobalTheory.LieBase.HodgeChart
