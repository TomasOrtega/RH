import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt
open scoped ENNReal Classical

/- English proof (translation)
Establish `key : ∀ u : α → ℝ, eLpNorm u 2 μ ^ 2 = ∫⁻ a, ENNReal.ofReal (u a ^ 2) ∂μ` using `fun u => by`. Establish `e` using `eLpNorm_nnreal_pow_eq_lintegral (f := u) (μ := μ) (p := 2) two_ne_zero`. Simplify using `only [NNReal.coe_ofNat, ENNReal.rpow_ofNat, ENNReal.coe_ofNat] at e`. Rewrite using `[e]`. Use `lintegral_congr fun a => ?_` and prove the remaining obligations.

Rewrite using `[Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]`. Rewrite using `[key, key]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_add (sq_nonneg _) hC]`. Conclude with `ENNReal.ofReal_le_ofReal (h a)`.

Use `_ = ∫⁻ a, ENNReal.ofReal (g a ^ 2) ∂μ + ENNReal.ofReal C * μ Set.univ := by`. Rewrite using `[lintegral_add_right _ measurable_const, lintegral_const]`. Use `_ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hμ)`.
-/
theorem eLpNorm_sq_le_add {α : Type} [MeasurableSpace α] {μ : Measure α} (hμ : μ Set.univ ≤ 1) {f g : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ a, f a ^ 2 ≤ g a ^ 2 + C) : eLpNorm f 2 μ ^ 2 ≤ eLpNorm g 2 μ ^ 2 + ENNReal.ofReal C := by
  have key : ∀ u : α → ℝ, eLpNorm u 2 μ ^ 2 = ∫⁻ a, ENNReal.ofReal (u a ^ 2) ∂μ := fun u => by
    have e := eLpNorm_nnreal_pow_eq_lintegral (f := u) (μ := μ) (p := 2) two_ne_zero
    simp only [NNReal.coe_ofNat, ENNReal.rpow_ofNat, ENNReal.coe_ofNat] at e
    rw [e]
    refine lintegral_congr fun a => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [key, key]
  calc ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂μ ≤ ∫⁻ a, ENNReal.ofReal (g a ^ 2) + ENNReal.ofReal C ∂μ :=
        lintegral_mono fun a => by
          rw [← ENNReal.ofReal_add (sq_nonneg _) hC]
          exact ENNReal.ofReal_le_ofReal (h a)
    _ = ∫⁻ a, ENNReal.ofReal (g a ^ 2) ∂μ + ENNReal.ofReal C * μ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hμ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Break down `Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure σ.fieldRange) with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h1 : H.rt0 ∈ σ.fieldRange.topologicalClosure` using `Subfield.le_topologicalClosure _ ⟨_, hσ⟩`. Rewrite `h1` using `[h]`. Take `⟨t, ht⟩` from `h1`.

Establish `h2` using `H.sqrt_neg_disc_sq`. Rewrite `h2` using `[← ht]`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `h3 : t ^ 2 = -(H.d : ℝ)`. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Use `push_cast`. Conclude with `h2`. Use polynomial arithmetic with `[sq_nonneg t]`. Rewrite using `[denseRange_iff_closure_range]`. Conclude with `congrArg (fun K : Subfield ℂ => (K : Set ℂ)) h`.
-/
theorem denseRange_of_goodEmb {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) : DenseRange σ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure σ.fieldRange) with h | h
  · exfalso
    have h1 : H.rt0 ∈ σ.fieldRange.topologicalClosure :=
      Subfield.le_topologicalClosure _ ⟨_, hσ⟩
    rw [h] at h1
    obtain ⟨t, ht⟩ := h1
    have h2 := H.sqrt_neg_disc_sq
    rw [← ht] at h2
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have h3 : t ^ 2 = -(H.d : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact h2
    nlinarith [sq_nonneg t]
  · rw [denseRange_iff_closure_range]
    exact congrArg (fun K : Subfield ℂ => (K : Set ℂ)) h

section Model

variable {r : ℕ} {Cp : Type} [Fintype Cp] {X : Cp → FD.Data E r} {la : ∀ k, FD.Wt (X k).Ψ r}

/- English proof (translation)
Assemble the required witnesses or components as `⟨(supE X la P).toReal, ENNReal.toReal_nonneg, fun p => (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top X la hP)).1 (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p)⟩`.
-/
theorem exists_ptN_le {P : FDSec X} (hP : P ∈ holSub X la) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : FPt X, ptN la P ⟨p.1, p.2.1⟩ ≤ M :=
  ⟨(supE X la P).toReal, ENNReal.toReal_nonneg, fun p => (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top X la hP)).1
    (le_iSup (fun p : FPt X => ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)) p)⟩

omit [Fintype Cp] in

/- English proof (translation)
The claim follows from `pnorm_add_le _ _ _ _ _`.
-/
theorem ptN_add_le (P Q : FDSec X) (z : Σ k, FD.Frame (X k).Ψ r) : ptN la (P + Q) z ≤ ptN la P z + ptN la Q z :=
  pnorm_add_le _ _ _ _ _

omit [Fintype Cp] in

/- English proof (translation)
The claim follows from `pnorm_smul _ _ _ _ _`.
-/
theorem ptN_smul (a : ℂ) (P : FDSec X) (z : Σ k, FD.Frame (X k).Ψ r) : ptN la (a • P) z = ‖a‖ * ptN la P z :=
  pnorm_smul _ _ _ _ _

/- English proof (translation)
Establish `h0 : ∀ z, ptN la (0 : FDSec X) z = 0` using `fun z => pnorm_zero _ _ _`. Proceed by induction on `hQ using Submodule.span_induction with`. Consider the case `mem P hP`. Take `⟨f, hf, rfl⟩` from `hP`. Conclude with `fun ε hε => ⟨f, hf, fun p => by rw [sub_self, h0]; exact hε.le⟩`.

Consider the case `zero => exact fun ε hε => ⟨0, zero_mem _, fun p => by rw [map_zero, sub_self, h0]; exact hε.le⟩`. Consider the case `add P Q _ _ hP hQ`. Introduce `ε hε`. Take `⟨f, hf, h₁⟩` from `hP (ε / 2) (half_pos hε)`. Take `⟨g, hg, h₂⟩` from `hQ (ε / 2) (half_pos hε)`.

Use `⟨f + g, add_mem hf hg, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, show P + Q - (rd f + rd g) = (P - rd f) + (Q - rd g) by abel]`. Conclude with `(ptN_add_le _ _ _).trans (by linarith [h₁ p, h₂ p])`. Consider the case `smul a P _ hP`. Introduce `ε hε`.

Establish `ha : 0 < ‖a‖ + 1` using `by positivity`. Take `⟨f, hf, h₁⟩` from `hP (ε / 2 / (‖a‖ + 1)) (by positivity)`. Take `⟨M, hM, h₂⟩` from `exists_ptN_le (hC f hf)`. Take `⟨b, hb⟩` from `hσ.exists_dist_lt a (show 0 < ε / 2 / (M + 1) by positivity)`. Rewrite `hb` using `[dist_eq_norm, lt_div_iff₀ (by positivity)]`.

Use `⟨b • f, C.smul_mem b hf, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, show a • P - σ b • rd f = a • (P - rd f) + (a - σ b) • rd f by`. Rewrite using `[smul_sub, sub_smul]`. Use the proof step `abel]`. Use `(ptN_add_le _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[ptN_smul, ptN_smul]`. Establish `e₁` using `(le_div_iff₀ ha).1 (h₁ p)`. Establish `e₂` using `mul_le_mul_of_nonneg_left (h₂ p) (norm_nonneg (a - σ b))`. Use polynomial arithmetic with `[ptN_nonneg la (P - rd f) ⟨p.1, p.2.1⟩, norm_nonneg (a - σ b)]`.
-/
theorem exists_ptN_sub_le {K W : Type} [Field K] [AddCommGroup W] [Module K W] {σ : K →+* ℂ} (hσ : DenseRange σ)
    (rd : W →ₛₗ[σ] FDSec X) (C : Submodule K W) (hC : ∀ f ∈ C, rd f ∈ holSub X la) {Q : FDSec X}
    (hQ : Q ∈ Submodule.span ℂ (rd '' C)) :
    ∀ ε : ℝ, 0 < ε → ∃ f ∈ C, ∀ p : FPt X, ptN la (Q - rd f) ⟨p.1, p.2.1⟩ ≤ ε := by
  have h0 : ∀ z, ptN la (0 : FDSec X) z = 0 := fun z => pnorm_zero _ _ _
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact fun ε hε => ⟨f, hf, fun p => by rw [sub_self, h0]; exact hε.le⟩
  | zero => exact fun ε hε => ⟨0, zero_mem _, fun p => by rw [map_zero, sub_self, h0]; exact hε.le⟩
  | add P Q _ _ hP hQ =>
    intro ε hε
    obtain ⟨f, hf, h₁⟩ := hP (ε / 2) (half_pos hε)
    obtain ⟨g, hg, h₂⟩ := hQ (ε / 2) (half_pos hε)
    refine ⟨f + g, add_mem hf hg, fun p => ?_⟩
    rw [map_add, show P + Q - (rd f + rd g) = (P - rd f) + (Q - rd g) by abel]
    exact (ptN_add_le _ _ _).trans (by linarith [h₁ p, h₂ p])
  | smul a P _ hP =>
    intro ε hε
    have ha : 0 < ‖a‖ + 1 := by positivity
    obtain ⟨f, hf, h₁⟩ := hP (ε / 2 / (‖a‖ + 1)) (by positivity)
    obtain ⟨M, hM, h₂⟩ := exists_ptN_le (hC f hf)
    obtain ⟨b, hb⟩ := hσ.exists_dist_lt a (show 0 < ε / 2 / (M + 1) by positivity)
    rw [dist_eq_norm, lt_div_iff₀ (by positivity)] at hb
    refine ⟨b • f, C.smul_mem b hf, fun p => ?_⟩
    rw [map_smulₛₗ, show a • P - σ b • rd f = a • (P - rd f) + (a - σ b) • rd f by
      rw [smul_sub, sub_smul]; abel]
    refine (ptN_add_le _ _ _).trans ?_
    rw [ptN_smul, ptN_smul]
    have e₁ := (le_div_iff₀ ha).1 (h₁ p)
    have e₂ := mul_le_mul_of_nonneg_left (h₂ p) (norm_nonneg (a - σ b))
    nlinarith [ptN_nonneg la (P - rd f) ⟨p.1, p.2.1⟩, norm_nonneg (a - σ b)]

variable {D : Formalism.BasicNotions.D7} (V : Formalism.BasicNotions.TH.HSp D) (dict : Formalism.L2.Theta.GA D V → Σ k, FD.Frame (X k).Ψ r)
  (μ : Measure (AutQ V))

/- English proof (translation)
Establish `hQ' : Q ∈ holSub X la` using `(Submodule.span_le.2 (by rintro _ ⟨f, hf, rfl⟩; exact hC f hf)) hQ`. Take `⟨M, hM, h₂⟩` from `exists_ptN_le hQ'`. Establish `hfin` using `petE_ne_top V dict μ hμ hd hQ'`. Use `set A := (petE V dict μ la Q).toReal with hA`. Establish `step : ∀ ε : ℝ, 0 < ε → ptN la Q ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (A ^ 2 + (2 * M * ε + ε ^ 2)) + (2 * (M + ε) * ε + ε ^ 2)` using `fun ε hε => by`.

Take `⟨f, hf, h₁⟩` from `exists_ptN_sub_le hσ rd C hC hQ ε hε`. Establish `up : ∀ p : FPt X, ptN la (rd f) ⟨p.1, p.2.1⟩ ≤ ptN la Q ⟨p.1, p.2.1⟩ + ε` using `fun p => by`. Establish `e` using `ptN_add_le (la := la) Q ((-1 : ℂ) • (Q - rd f)) ⟨p.1, p.2.1⟩`. Rewrite `e` using `[ptN_smul, show Q + (-1 : ℂ) • (Q - rd f) = rd f by rw [neg_one_smul]; abel, norm_neg, norm_one, one_mul]`. Combine the linear relations using `[h₁ p]`.

Establish `dn : ptN la Q ⟨z.1, z.2.1⟩ ≤ ptN la (rd f) ⟨z.1, z.2.1⟩ + ε`. Establish `e` using `ptN_add_le (la := la) (rd f) (Q - rd f) ⟨z.1, z.2.1⟩`. Rewrite `e` using `[add_sub_cancel]`. Combine the linear relations using `[h₁ z]`. Establish `hC0 : 0 ≤ 2 * M * ε + ε ^ 2` using `by positivity`.

Establish `e₁ : petE V dict μ la (rd f) ^ 2 ≤ petE V dict μ la Q ^ 2 + ENNReal.ofReal (2 * M * ε + ε ^ 2)` using `eLpNorm_sq_le_add hμ hC0 fun q => by`. Establish `a₁ : ptN la (rd f) (dict q.out) ≤ ptN la Q (dict q.out) + ε` using `up ⟨_, _, hd q.out⟩`. Establish `a₂ : ptN la Q (dict q.out) ≤ M` using `h₂ ⟨_, _, hd q.out⟩`. Establish `a₃` using `pow_le_pow_left₀ (ptN_nonneg _ _ _) a₁ 2`. Use the polynomial consequences of the given equalities and inequalities.

Establish `e₂` using `ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top hfin, ENNReal.ofReal_ne_top⟩) e₁`. Rewrite `e₂` using `[ENNReal.toReal_add (ENNReal.pow_ne_top hfin) ENNReal.ofReal_ne_top, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofReal hC0]`. Establish `e₃` using `(h f hf).trans (mul_le_mul_of_nonneg_left e₂ hB)`. Establish `e₄` using `pow_le_pow_left₀ (ptN_nonneg _ _ _) dn 2`. Establish `e₅ : ptN la (rd f) ⟨z.1, z.2.1⟩ ≤ M + ε` using `by linarith [up z, h₂ z]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `lim : Filter.Tendsto (fun ε : ℝ => B * (A ^ 2 + (2 * M * ε + ε ^ 2)) + (2 * (M + ε) * ε + ε ^ 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (B * A ^ 2))`. Use `Filter.Tendsto.mono_left (Continuous.tendsto' (by fun_prop) _ _ (by simp)) nhdsWithin_le_nhds` and prove the remaining obligations. Conclude with `ge_of_tendsto lim (eventually_nhdsWithin_of_forall step)`.
-/
theorem ptN_sq_le_of_mem_span (hμ : μ Set.univ ≤ 1) (hd : ∀ g, (dict g).2 ∈ (X (dict g).1).dom)
    {K W : Type} [Field K] [AddCommGroup W] [Module K W] {σ : K →+* ℂ} (hσ : DenseRange σ)
    (rd : W →ₛₗ[σ] FDSec X) (C : Submodule K W) (hC : ∀ f ∈ C, rd f ∈ holSub X la) (z : FPt X) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ f ∈ C, ptN la (rd f) ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (petE V dict μ la (rd f)).toReal ^ 2) {Q : FDSec X}
    (hQ : Q ∈ Submodule.span ℂ (rd '' C)) :
    ptN la Q ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (petE V dict μ la Q).toReal ^ 2 := by
  have hQ' : Q ∈ holSub X la := (Submodule.span_le.2 (by rintro _ ⟨f, hf, rfl⟩; exact hC f hf)) hQ
  obtain ⟨M, hM, h₂⟩ := exists_ptN_le hQ'
  have hfin := petE_ne_top V dict μ hμ hd hQ'
  set A := (petE V dict μ la Q).toReal with hA
  have step : ∀ ε : ℝ, 0 < ε →
      ptN la Q ⟨z.1, z.2.1⟩ ^ 2 ≤ B * (A ^ 2 + (2 * M * ε + ε ^ 2)) + (2 * (M + ε) * ε + ε ^ 2) := fun ε hε => by
    obtain ⟨f, hf, h₁⟩ := exists_ptN_sub_le hσ rd C hC hQ ε hε
    have up : ∀ p : FPt X, ptN la (rd f) ⟨p.1, p.2.1⟩ ≤ ptN la Q ⟨p.1, p.2.1⟩ + ε := fun p => by
      have e := ptN_add_le (la := la) Q ((-1 : ℂ) • (Q - rd f)) ⟨p.1, p.2.1⟩
      rw [ptN_smul, show Q + (-1 : ℂ) • (Q - rd f) = rd f by rw [neg_one_smul]; abel, norm_neg, norm_one,
        one_mul] at e
      linarith [h₁ p]
    have dn : ptN la Q ⟨z.1, z.2.1⟩ ≤ ptN la (rd f) ⟨z.1, z.2.1⟩ + ε := by
      have e := ptN_add_le (la := la) (rd f) (Q - rd f) ⟨z.1, z.2.1⟩
      rw [add_sub_cancel] at e
      linarith [h₁ z]
    have hC0 : 0 ≤ 2 * M * ε + ε ^ 2 := by positivity
    have e₁ : petE V dict μ la (rd f) ^ 2 ≤ petE V dict μ la Q ^ 2 + ENNReal.ofReal (2 * M * ε + ε ^ 2) :=
      eLpNorm_sq_le_add hμ hC0 fun q => by
        have a₁ : ptN la (rd f) (dict q.out) ≤ ptN la Q (dict q.out) + ε := up ⟨_, _, hd q.out⟩
        have a₂ : ptN la Q (dict q.out) ≤ M := h₂ ⟨_, _, hd q.out⟩
        have a₃ := pow_le_pow_left₀ (ptN_nonneg _ _ _) a₁ 2
        nlinarith
    have e₂ := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.pow_ne_top hfin, ENNReal.ofReal_ne_top⟩) e₁
    rw [ENNReal.toReal_add (ENNReal.pow_ne_top hfin) ENNReal.ofReal_ne_top, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hC0] at e₂
    have e₃ := (h f hf).trans (mul_le_mul_of_nonneg_left e₂ hB)
    have e₄ := pow_le_pow_left₀ (ptN_nonneg _ _ _) dn 2
    have e₅ : ptN la (rd f) ⟨z.1, z.2.1⟩ ≤ M + ε := by linarith [up z, h₂ z]
    nlinarith
  have lim : Filter.Tendsto (fun ε : ℝ => B * (A ^ 2 + (2 * M * ε + ε ^ 2)) + (2 * (M + ε) * ε + ε ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (B * A ^ 2)) := by
    refine Filter.Tendsto.mono_left (Continuous.tendsto' (by fun_prop) _ _ (by simp)) nhdsWithin_le_nhds
  exact ge_of_tendsto lim (eventually_nhdsWithin_of_forall step)

end Model

section Berg

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} {D : Formalism.BasicNotions.D7}
  {V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D}
  {dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r} {Z : Comp Xo c}

/- English proof (translation)
Proceed by induction on `hQ using Submodule.span_induction with`. Consider the case `mem P hP`. Take `⟨f, hf, rfl⟩` from `hP`. Conclude with `rdU_eq_zero _ hf.2 hz`. Consider the case `zero => rfl`.

Consider the case `add P Q _ _ hP hQ => rw [Pi.add_apply, Pi.add_apply, hP, hQ, add_zero]`. Consider the case `smul a P _ hP => rw [Pi.smul_apply, Pi.smul_apply, hP, smul_zero]`.
-/
theorem eq_zero_of_mem_span_cuspOn {G : WTZ E} {σ : c.F →+* ℂ} {Q : FDSec (U σ).X}
    (hQ : Q ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z G : Set (Rul Xo c))))
    {z : Σ k, FD.Frame ((U σ).X k).Ψ r} (hz : z ∉ framesOn (U σ) Z) : Q z.1 z.2 = 0 := by
  induction hQ using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨f, hf, rfl⟩ := hP
    exact rdU_eq_zero _ hf.2 hz
  | zero => rfl
  | add P Q _ _ hP hQ => rw [Pi.add_apply, Pi.add_apply, hP, hQ, add_zero]
  | smul a P _ hP => rw [Pi.smul_apply, Pi.smul_apply, hP, smul_zero]

/- English proof (translation)
Distinguish the cases in `h : bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ = ⊤`. Conclude with `h ▸ le_top`. Establish `hB` using `(bergCusp_le_iff ENNReal.toReal_nonneg).1 (ENNReal.ofReal_toReal h).ge`. Rewrite using `[← ENNReal.ofReal_toReal h]`. Use `set B := (bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩).toReal`.

Establish `hB0 : 0 ≤ B` using `ENNReal.toReal_nonneg`. Use `set μ := muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z`. Establish `hμ : μ Set.univ ≤ 1` using `muPart_univ_le _ _ _`. Establish `hfin` using `fun P (hP : P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G)) => petE_ne_top (V (goodOf c σ)) (dict (goodOf c σ)) μ hμ hd hP`. Use `(bergE_le_iff _ _ μ hfin z ENNReal.ofReal_ne_top).2 fun P hP => ?_` and prove the remaining obligations.

Take `⟨Q, hQ, hPQ⟩` from `hspan P hP`. Establish `key` using `ptN_sq_le_of_mem_span (V (goodOf c σ)) (dict (goodOf c σ)) μ hμ hd (denseRange_of_goodEmb (goodEmb_goodOf c σ)) (rdU (U (goodOf c σ))) (cuspOn U Z G) (fun f hf => (mem_cuspW.1 hf.1).2 _ (goodEmb_goodOf c σ)) z hB0 (fun f hf => by`. Establish `e` using `hB f hf`. Establish `hl` using `lieFacZ_pos (Dw := Dw) x G`. Simplify using `only [homN, petOn, petAt, mul_pow] at e`.

Conclude with `le_of_mul_le_mul_left (e.trans_eq (by ring)) (pow_pos hl 2)) hQ`. Establish `hle : ∀ w, ptN (modelWt (U (goodOf c σ)) G) Q w ≤ ptN (modelWt (U (goodOf c σ)) G) P w` using `fun w => by`. Distinguish the cases in `hw : w ∈ framesOn (U (goodOf c σ)) Z`. Simplify using `only [ptN, FD.Data.pnorm, hPQ w hw, le_refl]`. Use `le_trans (le_of_eq ?_) (ptN_nonneg _ P w)` and prove the remaining obligations.

Simplify using `only [ptN, FD.Data.pnorm, eq_zero_of_mem_span_cuspOn hQ hw, norm_zero, zero_mul]`. Establish `hpet : petE (V (goodOf c σ)) (dict (goodOf c σ)) μ (modelWt (U (goodOf c σ)) G) Q ≤ petE (V (goodOf c σ)) (dict (goodOf c σ)) μ (modelWt (U (goodOf c σ)) G) P` using `eLpNorm_mono fun q => by`. Rewrite using `[Real.norm_of_nonneg (ptN_nonneg _ _ _), Real.norm_of_nonneg (ptN_nonneg _ _ _)]`. Conclude with `hle _`. Establish `hz' : ptN (modelWt (U (goodOf c σ)) G) P ⟨z.1, z.2.1⟩ = ptN (modelWt (U (goodOf c σ)) G) Q ⟨z.1, z.2.1⟩`.

Use `hPQ _ hz` as an intermediate fact. Simplify using `only [ptN, FD.Data.pnorm] at this ⊢`. Rewrite using `[this]`. Establish `e` using `key.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono (hfin P hP) hpet) 2) hB0)`. Rewrite using `[hz', ← ENNReal.ofReal_toReal (hfin P hP), ← ENNReal.ofReal_pow (ptN_nonneg _ _ _), ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hB0]`.

Conclude with `ENNReal.ofReal_le_ofReal e`.
-/
theorem bergOn_le_bergCusp {G : WTZ E} {σ : c.F →+* ℂ}
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (hspan : ∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2)
    (z : FPt (U (goodOf c σ)).X)
    (hz : (⟨z.1, z.2.1⟩ : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r) ∈ framesOn (U (goodOf c σ)) Z) :
    bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z ≤ bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ := by
  by_cases h : bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ = ⊤
  · exact h ▸ le_top
  have hB := (bergCusp_le_iff ENNReal.toReal_nonneg).1 (ENNReal.ofReal_toReal h).ge
  rw [← ENNReal.ofReal_toReal h]
  set B := (bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩).toReal
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  set μ := muOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z
  have hμ : μ Set.univ ≤ 1 := muPart_univ_le _ _ _
  have hfin := fun P (hP : P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G)) =>
    petE_ne_top (V (goodOf c σ)) (dict (goodOf c σ)) μ hμ hd hP
  refine (bergE_le_iff _ _ μ hfin z ENNReal.ofReal_ne_top).2 fun P hP => ?_
  obtain ⟨Q, hQ, hPQ⟩ := hspan P hP
  have key := ptN_sq_le_of_mem_span (V (goodOf c σ)) (dict (goodOf c σ)) μ hμ hd
    (denseRange_of_goodEmb (goodEmb_goodOf c σ)) (rdU (U (goodOf c σ))) (cuspOn U Z G)
    (fun f hf => (mem_cuspW.1 hf.1).2 _ (goodEmb_goodOf c σ)) z hB0 (fun f hf => by
      have e := hB f hf
      have hl := lieFacZ_pos (Dw := Dw) x G
      simp only [homN, petOn, petAt, mul_pow] at e
      exact le_of_mul_le_mul_left (e.trans_eq (by ring)) (pow_pos hl 2)) hQ
  have hle : ∀ w, ptN (modelWt (U (goodOf c σ)) G) Q w ≤ ptN (modelWt (U (goodOf c σ)) G) P w := fun w => by
    by_cases hw : w ∈ framesOn (U (goodOf c σ)) Z
    · simp only [ptN, FD.Data.pnorm, hPQ w hw, le_refl]
    · refine le_trans (le_of_eq ?_) (ptN_nonneg _ P w)
      simp only [ptN, FD.Data.pnorm, eq_zero_of_mem_span_cuspOn hQ hw, norm_zero, zero_mul]
  have hpet : petE (V (goodOf c σ)) (dict (goodOf c σ)) μ (modelWt (U (goodOf c σ)) G) Q ≤
      petE (V (goodOf c σ)) (dict (goodOf c σ)) μ (modelWt (U (goodOf c σ)) G) P :=
    eLpNorm_mono fun q => by
      rw [Real.norm_of_nonneg (ptN_nonneg _ _ _), Real.norm_of_nonneg (ptN_nonneg _ _ _)]
      exact hle _
  have hz' : ptN (modelWt (U (goodOf c σ)) G) P ⟨z.1, z.2.1⟩ = ptN (modelWt (U (goodOf c σ)) G) Q ⟨z.1, z.2.1⟩ := by
    have := hPQ _ hz
    simp only [ptN, FD.Data.pnorm] at this ⊢
    rw [this]
  have e := key.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono (hfin P hP) hpet) 2) hB0)
  rw [hz', ← ENNReal.ofReal_toReal (hfin P hP), ← ENNReal.ofReal_pow (ptN_nonneg _ _ _),
    ← ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← ENNReal.ofReal_mul hB0]
  exact ENNReal.ofReal_le_ofReal e

/- English proof (translation)
The claim follows from `le_antisymm (bergCusp_le_bergOn hd z) (bergOn_le_bergCusp hd hspan z hz)`.
-/
theorem bergCusp_eq_bergOn {G : WTZ E} {σ : c.F →+* ℂ}
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (hspan : ∀ P ∈ holSub (U (goodOf c σ)).X (modelWt (U (goodOf c σ)) G),
      ∃ Q ∈ Submodule.span ℂ (rdU (U (goodOf c σ)) '' (cuspOn U Z G : Set (Rul Xo c))),
        ∀ w ∈ framesOn (U (goodOf c σ)) Z, P w.1 w.2 = Q w.1 w.2)
    (z : FPt (U (goodOf c σ)).X)
    (hz : (⟨z.1, z.2.1⟩ : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r) ∈ framesOn (U (goodOf c σ)) Z) :
    bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ = bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z :=
  le_antisymm (bergCusp_le_bergOn hd z) (bergOn_le_bergCusp hd hspan z hz)

end Berg

end GlobalTheory.CompHS
