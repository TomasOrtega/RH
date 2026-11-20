import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainOfTransference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.NearSupremumBounds.Inputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.FourierJacobiDifferentiable
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmApproximationTransference
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HyperbolicFlagDataBasePoint

namespace GlobalTheory.FJDetect

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField Complex in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Use `set v : ι → ℂ := fun i => I * (a i : ℂ) with hv`. Establish `hD : ∀ s ∈ U, ∀ t : ι → ℝ, fderiv ℂ F s (fun i => (t i : ℂ)) = 0`. Introduce `s hs t`. Establish `hd : HasFDerivAt F (fderiv ℂ F s) s` using `(hF.differentiableAt (hU.mem_nhds hs)).hasFDerivAt`. Establish `hline : HasDerivAt (fun u : ℝ => s + (u : ℂ) • fun i => (t i : ℂ)) (fun i => (t i : ℂ)) 0`.

Establish `h0 : HasDerivAt (fun u : ℝ => (u : ℂ) • fun i => (t i : ℂ)) ((1 : ℂ) • fun i => (t i : ℂ)) 0`. Use `(hasDerivAt_id (0 : ℝ)).ofReal_comp.smul_const (fun i => (t i : ℂ))` as an intermediate fact. Simplify using `using this`. Simplify using `using h0.const_add s`. Establish `hd0 : HasFDerivAt F (fderiv ℂ F s) (s + ((0 : ℝ) : ℂ) • fun i => (t i : ℂ))`.

Simplify using `using hd`. Establish `h1` using `(hd0.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hline`. Establish `h2 : (fun u : ℝ => F (s + (u : ℂ) • fun i => (t i : ℂ))) = fun _ => F s`. Use function extensionality and compare the values at `u`. Use `hreal s hs (fun i => u * t i)` as an intermediate fact.

Establish `he : (s + (u : ℂ) • fun i => (t i : ℂ)) = s + fun i => ((u * t i : ℝ) : ℂ)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[he, this]`. Establish `h3 : HasDerivAt (fun u : ℝ => F (s + (u : ℂ) • fun i => (t i : ℂ))) (fderiv ℂ F s (fun i => (t i : ℂ))) 0`.

Simplify `h1` using `[Function.comp_def]`. Rewrite `h3` using `[h2]`. Conclude with `h3.unique (hasDerivAt_const _ _)`. Establish `hDv : ∀ s ∈ U, fderiv ℂ F s v = 0`. Introduce `s hs`.

Establish `: v = I • fun i => (a i : ℂ)` using `by funext i; simp [hv]`. Rewrite using `[this, map_smul, hD s hs a, smul_zero]`. Use `set g : ℝ → ℂ := fun u => F ((u : ℂ) • v) with hg`. Establish `hderiv : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → HasDerivAt g 0 u`. Introduce `u hu0 hu1`.

Establish `hs` using `hseg u hu0 hu1`. Establish `hd : HasFDerivAt F (fderiv ℂ F ((u : ℂ) • v)) ((u : ℂ) • v)` using `(hF.differentiableAt (hU.mem_nhds hs)).hasFDerivAt`. Establish `hl : HasDerivAt (fun w : ℝ => (w : ℂ) • v) v u`. Use `(hasDerivAt_id u).ofReal_comp.smul_const v` as an intermediate fact. Simplify using `using this`.

Establish `h4` using `(hd.restrictScalars ℝ).comp_hasDerivAt u hl`. Establish `h5 : ((fderiv ℂ F ((u : ℂ) • v)).restrictScalars ℝ) v = 0` using `hDv _ hs`. Rewrite `h4` using `[h5]`. Conclude with `h4`. Establish `hconst` using `constant_of_has_deriv_right_zero (f := g) (a := 0) (b := 1) (fun u hu => (hderiv u hu.1 hu.2).continuousAt.continuousWithinAt) (fun u hu => (hderiv u hu.1 hu.2.le).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩`.

Simplify `hconst` using `[hg]`.
-/
private lemma eq_at_imag_of_real_translation_invariant {ι : Type} [Fintype ι] (F : (ι → ℂ) → ℂ)
    (U : Set (ι → ℂ)) (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hreal : ∀ s ∈ U, ∀ t : ι → ℝ, F (s + fun i => (t i : ℂ)) = F s)
    (a : ι → ℝ) (hseg : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ((u : ℂ) • fun i => I * (a i : ℂ)) ∈ U) :
    F (fun i => I * (a i : ℂ)) = F 0 := by
  set v : ι → ℂ := fun i => I * (a i : ℂ) with hv
  have hD : ∀ s ∈ U, ∀ t : ι → ℝ, fderiv ℂ F s (fun i => (t i : ℂ)) = 0 := by
    intro s hs t
    have hd : HasFDerivAt F (fderiv ℂ F s) s :=
      (hF.differentiableAt (hU.mem_nhds hs)).hasFDerivAt
    have hline : HasDerivAt (fun u : ℝ => s + (u : ℂ) • fun i => (t i : ℂ))
        (fun i => (t i : ℂ)) 0 := by
      have h0 : HasDerivAt (fun u : ℝ => (u : ℂ) • fun i => (t i : ℂ))
          ((1 : ℂ) • fun i => (t i : ℂ)) 0 := by
        have := (hasDerivAt_id (0 : ℝ)).ofReal_comp.smul_const (fun i => (t i : ℂ))
        simpa using this
      simpa using h0.const_add s
    have hd0 : HasFDerivAt F (fderiv ℂ F s) (s + ((0 : ℝ) : ℂ) • fun i => (t i : ℂ)) := by
      simpa using hd
    have h1 := (hd0.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hline
    have h2 : (fun u : ℝ => F (s + (u : ℂ) • fun i => (t i : ℂ))) = fun _ => F s := by
      funext u
      have := hreal s hs (fun i => u * t i)
      have he : (s + (u : ℂ) • fun i => (t i : ℂ)) = s + fun i => ((u * t i : ℝ) : ℂ) := by
        funext i; simp
      rw [he, this]
    have h3 : HasDerivAt (fun u : ℝ => F (s + (u : ℂ) • fun i => (t i : ℂ)))
        (fderiv ℂ F s (fun i => (t i : ℂ))) 0 := by
      simpa [Function.comp_def] using h1
    rw [h2] at h3
    exact h3.unique (hasDerivAt_const _ _)
  have hDv : ∀ s ∈ U, fderiv ℂ F s v = 0 := by
    intro s hs
    have : v = I • fun i => (a i : ℂ) := by funext i; simp [hv]
    rw [this, map_smul, hD s hs a, smul_zero]
  set g : ℝ → ℂ := fun u => F ((u : ℂ) • v) with hg
  have hderiv : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → HasDerivAt g 0 u := by
    intro u hu0 hu1
    have hs := hseg u hu0 hu1
    have hd : HasFDerivAt F (fderiv ℂ F ((u : ℂ) • v)) ((u : ℂ) • v) :=
      (hF.differentiableAt (hU.mem_nhds hs)).hasFDerivAt
    have hl : HasDerivAt (fun w : ℝ => (w : ℂ) • v) v u := by
      have := (hasDerivAt_id u).ofReal_comp.smul_const v
      simpa using this
    have h4 := (hd.restrictScalars ℝ).comp_hasDerivAt u hl
    have h5 : ((fderiv ℂ F ((u : ℂ) • v)).restrictScalars ℝ) v = 0 := hDv _ hs
    rw [h5] at h4
    exact h4
  have hconst := constant_of_has_deriv_right_zero (f := g) (a := 0) (b := 1)
    (fun u hu => (hderiv u hu.1 hu.2).continuousAt.continuousWithinAt)
    (fun u hu => (hderiv u hu.1 hu.2.le).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simpa [hg] using hconst

open NumberField Complex in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hV : X.IsIsoV (X.embV ξ)` using `_root_.PI.FdFjNearSup.W.isIsoV_embV X hξ`. Establish `hM` using `fun s => _root_.ReciprocityTheory.ChartRestriction.G.FD.flowDomainCriterion_holds r X (X.embV ξ) hV x hx s`. Use `set tt : X.Ψ → ℝ := fun τ => X.ttV (X.embV ξ) x τ with htt`. Establish `htt_pos : ∀ τ, 0 < tt τ`. Introduce `τ`.

Establish `hc` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.d4l4_c_pos X τ`. Establish `hm` using `X.maj_pos hx τ (hV τ).2`. Simplify using `only [htt, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.ttV]`. Check the signs of the components of the expression. Use `set a : X.Ψ → ℝ := fun τ => 1 - tt τ with ha`.

Use `set U : Set (X.Ψ → ℂ) := {s | X.flow ξ s x ∈ X.dom} with hUdef`. Establish `hUeq : U = {s | ∀ τ, 0 < 1 + (s τ).im / tt τ}`. Use extensionality with `s`. Conclude with `(hM s).1`. Establish `hU : IsOpen U`.

Rewrite using `[hUeq]`. Simplify using `only [Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun τ => isOpen_lt continuous_const (by fun_prop)`. Use `set F : (X.Ψ → ℂ) → ℂ := fun s => X.fj la ξ ν P (X.flow ξ s x) * Complex.exp (-(4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ)) with hFdef`. Establish `hFd : DifferentiableOn ℂ F U`.

Use `DifferentiableOn.mul ?_ ?_` and prove the remaining obligations. Conclude with `(_root_.ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_diffOn X la P hP hξ ν).comp (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity.flow_differentiable X ξ x).differentiableOn (fun s hs => hs)`. Conclude with `Differentiable.differentiableOn (by fun_prop)`. Establish `hreal : ∀ s ∈ U, ∀ t : X.Ψ → ℝ, F (s + fun i => (t i : ℂ)) = F s`. Introduce `s hs t`.

Establish `hfl : X.flow ξ (s + fun i => (t i : ℂ)) x = X.flow ξ (fun i => (t i : ℂ)) (X.flow ξ s x)`. Rewrite using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.flow_flow X hξ.2.1, add_comm]`. Simplify using `only [hFdef, hfl, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj_flow_real X la ξ hξ ν P hP.1 hP.2 _ hs t]`. Rewrite using `[mul_comm (Complex.exp _) (X.fj la ξ ν P (X.flow ξ s x)), mul_assoc, ← Complex.exp_add]`. Use `congr 2`.

Simplify using `only [Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hseg : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ((u : ℂ) • fun i => I * (a i : ℂ)) ∈ U`. Introduce `u hu0 hu1`. Rewrite using `[hUeq]`.

Introduce `τ`. Establish `ht` using `htt_pos τ`. Establish `him : (((u : ℂ) • fun i => I * (a i : ℂ)) τ).im = u * a τ` using `by simp`. Rewrite using `[him]`. Establish `hq : 1 + u * a τ / tt τ = ((1 - u) * tt τ + u) / tt τ`.

Simplify using `only [ha]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hq]`. Apply `div_pos _ ht` to reduce the goal to its premises.

Break down `eq_or_lt_of_le hu0 with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `using ht`. Use the polynomial consequences of the given equalities and inequalities. Establish `hconst` using `eq_at_imag_of_real_translation_invariant F U hU hFd hreal a hseg`.

Use `set v : X.Ψ → ℂ := fun i => I * (a i : ℂ) with hvdef`. Establish `hvU : v ∈ U` using `by simpa using hseg 1 zero_le_one le_rfl`. Use `⟨X.flow ξ v x, ⟨hvU, fun τ => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h2` using `(hM v).2 hvU τ`. Establish `hv : (v τ).im = a τ` using `by simp [hvdef]`.

Rewrite `h2` using `[hv]`. Establish `h3 : X.ttV (X.embV ξ) (X.flowV (X.embV ξ) v x) τ = 1`. Rewrite using `[h2]`. Simplify using `[ha, htt]`. Simplify using `only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.ttV, one_div, inv_eq_one] at h3`.

Conclude with `h3`. Introduce `h0`. Establish `hF0 : F 0 = X.fj la ξ ν P x`. Use `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj_flow_real X la ξ hξ ν P hP.1 hP.2 x hx 0` as an intermediate fact. Simplify using `only [hFdef]`.

Establish `h' : X.flow ξ 0 x = X.flow ξ (fun _ => 0) x` using `rfl`. Rewrite using `[h']`. Simplify using `using this`. Establish `hFv : F v = 0`. Simplify using `only [hFdef]`.

Rewrite using `[h0, zero_mul]`. Rewrite `hFv` using `[hconst, hF0]`. Conclude with `hfx hFv`.
-/
private lemma exists_mem_D1set_fj_ne_zero {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hfx : X.fj la ξ ν P x ≠ 0) :
    ∃ y ∈ X.FramesOverBasis ξ, X.fj la ξ ν P y ≠ 0 := by
  have hV : X.IsIsoV (X.embV ξ) := _root_.PI.FdFjNearSup.W.isIsoV_embV X hξ
  have hM := fun s => _root_.ReciprocityTheory.ChartRestriction.G.FD.flowDomainCriterion_holds r X (X.embV ξ) hV x hx s
  set tt : X.Ψ → ℝ := fun τ => X.ttV (X.embV ξ) x τ with htt
  have htt_pos : ∀ τ, 0 < tt τ := by
    intro τ
    have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.d4l4_c_pos X τ
    have hm := X.maj_pos hx τ (hV τ).2
    simp only [htt, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.ttV]
    positivity
  set a : X.Ψ → ℝ := fun τ => 1 - tt τ with ha
  set U : Set (X.Ψ → ℂ) := {s | X.flow ξ s x ∈ X.dom} with hUdef
  have hUeq : U = {s | ∀ τ, 0 < 1 + (s τ).im / tt τ} := by
    ext s; exact (hM s).1
  have hU : IsOpen U := by
    rw [hUeq]
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun τ => isOpen_lt continuous_const (by fun_prop)
  set F : (X.Ψ → ℂ) → ℂ := fun s => X.fj la ξ ν P (X.flow ξ s x) *
      Complex.exp (-(4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ)) with hFdef
  have hFd : DifferentiableOn ℂ F U := by
    refine DifferentiableOn.mul ?_ ?_
    · exact (_root_.ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientFlow.fj_diffOn X la P hP hξ ν).comp (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity.flow_differentiable X ξ x).differentiableOn (fun s hs => hs)
    · exact Differentiable.differentiableOn (by fun_prop)
  have hreal : ∀ s ∈ U, ∀ t : X.Ψ → ℝ, F (s + fun i => (t i : ℂ)) = F s := by
    intro s hs t
    have hfl : X.flow ξ (s + fun i => (t i : ℂ)) x
        = X.flow ξ (fun i => (t i : ℂ)) (X.flow ξ s x) := by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs.flow_flow X hξ.2.1, add_comm]
    simp only [hFdef, hfl, _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj_flow_real X la ξ hξ ν P hP.1 hP.2 _ hs t]
    rw [mul_comm (Complex.exp _) (X.fj la ξ ν P (X.flow ξ s x)), mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  have hseg : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ((u : ℂ) • fun i => I * (a i : ℂ)) ∈ U := by
    intro u hu0 hu1
    rw [hUeq]
    intro τ
    have ht := htt_pos τ
    have him : (((u : ℂ) • fun i => I * (a i : ℂ)) τ).im = u * a τ := by simp
    rw [him]
    have hq : 1 + u * a τ / tt τ = ((1 - u) * tt τ + u) / tt τ := by
      simp only [ha]; field_simp; ring
    rw [hq]
    apply div_pos _ ht
    rcases eq_or_lt_of_le hu0 with h | h
    · subst h; simpa using ht
    · nlinarith
  have hconst := eq_at_imag_of_real_translation_invariant F U hU hFd hreal a hseg
  set v : X.Ψ → ℂ := fun i => I * (a i : ℂ) with hvdef
  have hvU : v ∈ U := by simpa using hseg 1 zero_le_one le_rfl
  refine ⟨X.flow ξ v x, ⟨hvU, fun τ => ?_⟩, ?_⟩
  · have h2 := (hM v).2 hvU τ
    have hv : (v τ).im = a τ := by simp [hvdef]
    rw [hv] at h2
    have h3 : X.ttV (X.embV ξ) (X.flowV (X.embV ξ) v x) τ = 1 := by
      rw [h2]; simp [ha, htt]
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.ttV, one_div, inv_eq_one] at h3
    exact h3
  · intro h0
    have hF0 : F 0 = X.fj la ξ ν P x := by
      have := _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj_flow_real X la ξ hξ ν P hP.1 hP.2 x hx 0
      simp only [hFdef]
      have h' : X.flow ξ 0 x = X.flow ξ (fun _ => 0) x := rfl
      rw [h']
      simpa using this
    have hFv : F v = 0 := by
      simp only [hFdef]
      rw [h0, zero_mul]
    rw [hconst, hF0] at hFv
    exact hfx hFv

open NumberField Complex in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Take `⟨C, hC⟩` from `hP.2`. Establish `hB : ∀ y ∈ X.dom, X.pnorm la (X.fj la ξ ν P) y ≤ C` using `fun y hy => _root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.fj_bound X la P C hC hξ ν hy`. Establish `hC0 : 0 ≤ C` using `(X.pointNorm_nonneg la _ x).trans (hB x hx)`. Establish `hle : ∀ y, X.hatN la (X.fj la ξ ν P) y ≤ C`. Introduce `y`.

Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.hatN`. Apply `Real.sSup_le _ hC0` to reduce the goal to its premises. Introduce and unpack `t ⟨x', hx', -, rfl⟩`. Conclude with `hB x' hx'`. Establish `hge : ∀ y ∈ X.dom, X.pnorm la (X.fj la ξ ν P) y ≤ X.hatN la (X.fj la ξ ν P) y`.

Introduce `y hy`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.hatN`. Apply `le_csSup` to reduce the goal to its premises. Use `⟨C, ?_⟩` and prove the remaining obligations. Introduce and unpack `t ⟨x', hx', -, rfl⟩`.

Conclude with `hB x' hx'`. Conclude with `⟨y, hy, fun τ => rfl, rfl⟩`. Take `⟨y, hy, hfy⟩` from `exists_mem_D1set_fj_ne_zero X la P ⟨hP.1, C, hC⟩ hξ ν hx hfx`. Use `set S := {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} with hS`. Establish `hSb : BddAbove S` using `⟨C, by rintro t ⟨y, -, rfl⟩; exact hle y⟩`.

Establish `hpos : 0 < X.hatN la (X.fj la ξ ν P) y`. Use `lt_of_lt_of_le ?_ (hge y hy.1)` and prove the remaining obligations. Rewrite using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq]`. Conclude with `mul_pos (norm_pos_iff.2 hfy) (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.nfac_pos X hy.1 la)`. Establish `hyS : X.hatN la (X.fj la ξ ν P) y ∈ S` using `⟨y, hy, rfl⟩`.

Establish `hM : 0 < sSup S` using `lt_of_lt_of_le hpos (le_csSup hSb hyS)`. Take `⟨t, ⟨z0, hz0, rfl⟩, ht⟩` from `exists_lt_of_lt_csSup ⟨_, hyS⟩ (half_lt_self hM)`. Conclude with `⟨z0, hz0, by linarith⟩`.
-/
private lemma exists_mem_D1set_sSup_hatN_lt_two_mul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) (ν : X.Ψ → ℝ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hfx : X.fj la ξ ν P x ≠ 0) :
    ∃ z0 ∈ X.FramesOverBasis ξ, sSup {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y}
      < 2 * X.hatN la (X.fj la ξ ν P) z0 := by
  obtain ⟨C, hC⟩ := hP.2
  have hB : ∀ y ∈ X.dom, X.pnorm la (X.fj la ξ ν P) y ≤ C :=
    fun y hy => _root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.fj_bound X la P C hC hξ ν hy
  have hC0 : 0 ≤ C := (X.pointNorm_nonneg la _ x).trans (hB x hx)
  have hle : ∀ y, X.hatN la (X.fj la ξ ν P) y ≤ C := by
    intro y
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.hatN
    apply Real.sSup_le _ hC0
    rintro t ⟨x', hx', -, rfl⟩
    exact hB x' hx'
  have hge : ∀ y ∈ X.dom, X.pnorm la (X.fj la ξ ν P) y ≤ X.hatN la (X.fj la ξ ν P) y := by
    intro y hy
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.hatN
    apply le_csSup
    · refine ⟨C, ?_⟩
      rintro t ⟨x', hx', -, rfl⟩
      exact hB x' hx'
    · exact ⟨y, hy, fun τ => rfl, rfl⟩
  obtain ⟨y, hy, hfy⟩ := exists_mem_D1set_fj_ne_zero X la P ⟨hP.1, C, hC⟩ hξ ν hx hfx
  set S := {t | ∃ y ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) y} with hS
  have hSb : BddAbove S := ⟨C, by rintro t ⟨y, -, rfl⟩; exact hle y⟩
  have hpos : 0 < X.hatN la (X.fj la ξ ν P) y := by
    refine lt_of_lt_of_le ?_ (hge y hy.1)
    rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq]
    exact mul_pos (norm_pos_iff.2 hfy) (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.nfac_pos X hy.1 la)
  have hyS : X.hatN la (X.fj la ξ ν P) y ∈ S := ⟨y, hy, rfl⟩
  have hM : 0 < sSup S := lt_of_lt_of_le hpos (le_csSup hSb hyS)
  obtain ⟨t, ⟨z0, hz0, rfl⟩, ht⟩ := exists_lt_of_lt_csSup ⟨_, hyS⟩ (half_lt_self hM)
  exact ⟨z0, hz0, by linarith⟩

open NumberField Complex in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Establish `hnot : ∃ ξ, X.IsIso ξ ∧ ∃ ν : X.Ψ → ℝ, ∑ τ, ν τ ≤ c1 ∧ ∃ x ∈ X.dom, X.fj la ξ ν P x ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hP' ⟨hP, fun ξ hξ ν hν x hx => h ξ hξ ν hν x hx⟩`. Take `⟨ξ, hξ, ν, hν, x, hx, hfx⟩` from `hnot`.

Establish `hbdd` using `hP.1`. Establish `hνpos : ∀ τ, 0 ≤ ν τ` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd _ _root_.ReciprocityTheory.ChartRestriction.G.FD.moderateCoefficientPositivity_holds hbdd hξ ν hx hfx`. Take `⟨z0, hz0, hsup⟩` from `exists_mem_D1set_sSup_hatN_lt_two_mul _ la P hbdd hξ ν hx hfx`. Establish `hD4 : _root_.ReciprocityTheory.ChartRestriction.G.FD.ShortVectorHypotheses X la P ξ ν c1 w z0` using `⟨hdom, hP, hξ, hc1, hν, ⟨x, hx, hfx⟩, hw, hspr, hχ, hz0, hsup⟩`. Use `⟨ξ, ν, hξ, hν, hνpos, ⟨z0, hD4⟩, ?_⟩` and prove the remaining obligations.

Conclude with `(_root_.fd_point_assembly _root_.ReciprocityTheory.ChartRestriction.G.FD.shortVectorBound _root_.ReciprocityTheory.ChartRestriction.G.FD.orthonormalFlagTranslate_holds _root_.ReciprocityTheory.ChartRestriction.G.FD.orthonormalChartNormControl_holds (_root_.fd_fj_near_sup _root_.R …`.
-/
theorem _root_.GlobalTheory.FJDetect.exists_fj_ne_zero_at_split_point' {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.DataX E r)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) (c1 w : ℝ)
    (hdom : X.IsDominant la) (hc1 : 0 < c1) (hw : 1 ≤ w) (hspr : (∑ τ, X.spread la τ) ≤ w)
    (hr : (r : ℝ) ≤ w)
    (hχ : ∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
      Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1)
    (hP : P ∈ X.SS la) (hP' : P ∉ X.SSgt la c1) :
    ∃ (ξ : Fin r → E) (ν : X.Ψ → ℝ), X.IsIso ξ ∧ ∑ τ, ν τ ≤ c1 ∧ (∀ τ, 0 ≤ ν τ) ∧
      (∃ z0, _root_.ReciprocityTheory.ChartRestriction.G.FD.ShortVectorHypotheses X la P ξ ν c1 w z0) ∧
      let ep0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.flowEpsilonBound X.g (_root_.ReciprocityTheory.ChartRestriction.G.FD.dE E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E) X.NA X.NC c1 w
      let rh := _root_.ReciprocityTheory.ChartRestriction.G.FD.d6rh c1 w
      let La := _root_.ReciprocityTheory.ChartRestriction.G.FD.d6La r X.p0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.dE E) ep0 rh
      let ms := _root_.ReciprocityTheory.ChartRestriction.G.FD.frameIndexBound r (_root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.dE E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rdE E) X.NA X.NC ep0
      ∀ n' : ℕ, 1000 * ms / rh ≤ n' →
      ∃ x ∈ X.dom, ∃ lam : Fin (r - 2) → Fin r → E,
        (∀ j, lam j ∈ X.L' ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) ξ = 0) ∧
        LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
        (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) →
          _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0) ∧
        (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 →
          (∀ τ : X.Ψ, 0 < (τ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re) ∧
          X.Jz x (X.ucomp x ξ (X.embV (lam j))) = I • X.ucomp x ξ (X.embV (lam j))) ∧
        (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) →
          (∀ τ : X.Ψ, (τ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re < 0) ∧
          X.Jz x (X.ucomp x ξ (X.embV (lam j))) = -(I • X.ucomp x ξ (X.embV (lam j)))) ∧
        (∀ j (τ : X.Ψ), ‖τ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2) ∧
        (∀ μ ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧
          (n' : ℂ) • X.aproj x ξ (X.embV μ) = X.embV (e • ξ)) ∧
        X.fj la ξ ν P x ≠ 0 := by
  have hnot : ∃ ξ, X.IsIso ξ ∧ ∃ ν : X.Ψ → ℝ, ∑ τ, ν τ ≤ c1 ∧
      ∃ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP' ⟨hP, fun ξ hξ ν hν x hx => h ξ hξ ν hν x hx⟩
  obtain ⟨ξ, hξ, ν, hν, x, hx, hfx⟩ := hnot
  have hbdd := hP.1
  have hνpos : ∀ τ, 0 ≤ ν τ := _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd _ _root_.ReciprocityTheory.ChartRestriction.G.FD.moderateCoefficientPositivity_holds hbdd hξ ν hx hfx
  obtain ⟨z0, hz0, hsup⟩ := exists_mem_D1set_sSup_hatN_lt_two_mul _ la P hbdd hξ ν hx hfx
  have hD4 : _root_.ReciprocityTheory.ChartRestriction.G.FD.ShortVectorHypotheses X la P ξ ν c1 w z0 :=
    ⟨hdom, hP, hξ, hc1, hν, ⟨x, hx, hfx⟩, hw, hspr, hχ, hz0, hsup⟩
  refine ⟨ξ, ν, hξ, hν, hνpos, ⟨z0, hD4⟩, ?_⟩
  exact (_root_.fd_point_assembly _root_.ReciprocityTheory.ChartRestriction.G.FD.shortVectorBound _root_.ReciprocityTheory.ChartRestriction.G.FD.orthonormalFlagTranslate_holds _root_.ReciprocityTheory.ChartRestriction.G.FD.orthonormalChartNormControl_holds (_root_.fd_fj_near_sup _root_.ReciprocityTheory.ChartRestriction.G.FD.holomorphic_periodicity_extension _root_.ReciprocityTheory.ChartRestriction.G.FD.m3bNorm_holds _root_.ReciprocityTheory.ChartRestriction.G.FD.moderateCoefficientPositivity_holds) _root_.ReciprocityTheory.ChartRestriction.G.FD.schwarzLemmaBall_holds
    (_root_.ReciprocityTheory.ChartRestriction.G.FD.orthonormalShortVectorBound_of _root_.ReciprocityTheory.ChartRestriction.G.FD.shortVectorBound _root_.GlobalTheory.CMTransference.cmApproximation_transference) _root_.ReciprocityTheory.ChartRestriction.G.FD.isotropicCoefficientSplitting_holds _root_.ReciprocityTheory.ChartRestriction.G.FD.noShortVectorLowerBound_holds
    (_root_.fd_unip_move _root_.ReciprocityTheory.ChartRestriction.G.FD.shortVectorBound _root_.ReciprocityTheory.ChartRestriction.G.FD.unitaryComplementMove _root_.ReciprocityTheory.ChartRestriction.G.FD.unipotent_majorant_bound _root_.ReciprocityTheory.ChartRestriction.G.FD.isotropicCoefficientSplitting_holds _root_.ReciprocityTheory.ChartRestriction.G.FD.noShortVectorLowerBound_holds)) r X la P ξ ν c1 w z0 hD4 hr

end GlobalTheory.FJDetect
