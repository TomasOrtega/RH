import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MinimumGrowthBounds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ModeDecay

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Distinguish the cases in `h : τ ∈ X.Ψ`. Conclude with `⟨⟨τ, h⟩⟩`. Conclude with `⟨⟨ComplexEmbedding.conjugate τ, not_not.mp (mt (X.cmType τ).mpr h)⟩⟩`.
-/
theorem _root_.GlobalTheory.ModeDecay.nonempty_cmType {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨ComplexEmbedding.conjugate τ, not_not.mp (mt (X.cmType τ).mpr h)⟩⟩

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `h` using `hx`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at h`. Simplify using `only [Set.mem_setOf_eq] at h`. Conclude with `(h τ).1`.
-/
private lemma det_mat_ne_zero_of_mem_dom {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) (τ : X.Ψ) : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 := by
  have h := hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at h
  simp only [Set.mem_setOf_eq] at h
  exact (h τ).1

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Rewrite using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_emb, hξ.2.1, map_zero]`.
-/
private lemma hermC_emb_self_eq_zero_of_isIso {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {ξ : Fin r → E}
    (hξ : X.IsIso ξ) (τ : X.Ψ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) = 0 := by
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC_emb, hξ.2.1, map_zero]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `h1` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_bounds (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (det_mat_ne_zero_of_mem_dom X hx τ)`. Establish `h2` using `h1 (fun j hj => _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of X hx τ j hj)`. Establish `hiso` using `hermC_emb_self_eq_zero_of_isIso X hξ τ`. Establish `h3` using `h2 (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ)`. Establish `h4` using `h3 hiso`.

Conclude with `(h4 i hi).1`.
-/
private lemma mN_nonneg {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ) (τ : X.Ψ) (i : ℕ) (hi : i ≤ r) :
    0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) i := by
  have h1 := _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_bounds (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (det_mat_ne_zero_of_mem_dom X hx τ)
  have h2 := h1 (fun j hj => _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of X hx τ j hj)
  have hiso := hermC_emb_self_eq_zero_of_isIso X hξ τ
  have h3 := h2 (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ)
  have h4 := h3 hiso
  exact (h4 i hi).1

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hflow : X.flow ξ s x = X.flowV (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) s x` using `rfl`. Establish `h` using `hx`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at h ⊢`. Simplify using `only [Set.mem_setOf_eq] at h ⊢`. Introduce `τ`.

Take `⟨hdet, hsg⟩` from `h τ`. Establish `hiso` using `hermC_emb_self_eq_zero_of_isIso X hξ τ`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.mat_flow, Matrix.det_mul]`. Establish `hm : X.flowMat ξ τ (s τ) = X.flowMatV (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ (s τ)` using `rfl`.

Establish `hd0` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.det_flowMat X (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ (s τ)`. Establish `hd1` using `hd0 hiso`. Rewrite using `[hm, hd1, one_mul]`. Conclude with `hdet`. Establish `h0` using `hsg i`.

Establish `hc0` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq X x τ i`. Establish `hc1` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq X (X.flow ξ s x) τ i`. Rewrite `h0` using `[hc0]`. Rewrite using `[hc1]`. Establish `hd` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_flow X hx (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ`.

Establish `hd2` using `hd hiso s i (Nat.lt_succ_iff.mp i.2)`. Rewrite `hd2` using `[← hflow]`. Rewrite using `[hd2]`. Establish `hH` using `mN_nonneg X hx hξ τ i (Nat.lt_succ_iff.mp i.2)`. Establish `hc` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ`.

Establish `hf : 0 < 1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) i`. Use `mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hc.le) (hs τ)) hH` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Complex.re_mul_ofReal, ← mul_assoc]`. Conclude with `mul_pos h0 hf`.
-/
private lemma flow_mem_dom_of_im_nonneg' {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ) (s : X.Ψ → ℂ)
    (hs : ∀ τ, 0 ≤ (s τ).im) : X.flow ξ s x ∈ X.dom := by
  have hflow : X.flow ξ s x = X.flowV (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) s x := rfl
  have h := hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG at h ⊢
  simp only [Set.mem_setOf_eq] at h ⊢
  intro τ
  obtain ⟨hdet, hsg⟩ := h τ
  have hiso := hermC_emb_self_eq_zero_of_isIso X hξ τ
  refine ⟨?_, fun i => ?_⟩
  · rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.mat_flow, Matrix.det_mul]
    have hm : X.flowMat ξ τ (s τ) = X.flowMatV (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ (s τ) := rfl
    have hd0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.det_flowMat X (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ (s τ)
    have hd1 := hd0 hiso
    rw [hm, hd1, one_mul]
    exact hdet
  · have h0 := hsg i
    have hc0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq X x τ i
    have hc1 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq X (X.flow ξ s x) τ i
    rw [hc0] at h0
    rw [hc1]
    have hd := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_flow X hx (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ
    have hd2 := hd hiso s i (Nat.lt_succ_iff.mp i.2)
    rw [← hflow] at hd2
    rw [hd2]
    have hH := mN_nonneg X hx hξ τ i (Nat.lt_succ_iff.mp i.2)
    have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ
    have hf : 0 < 1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) i := by
      have := mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hc.le) (hs τ)) hH
      linarith
    rw [Complex.re_mul_ofReal, ← mul_assoc]
    exact mul_pos h0 hf

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `h1` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_pos (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (det_mat_ne_zero_of_mem_dom X hx τ)`. Establish `h2` using `h1 (fun j hj => _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of X hx τ j hj)`. Establish `hiso` using `hermC_emb_self_eq_zero_of_isIso X hξ τ`. Establish `h3` using `h2 (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ)`. Establish `h4` using `h3 hiso`.

Establish `hne : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ ≠ 0` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero _ hξ.2.2`. Conclude with `h4 hne`.
-/
private lemma mN_p0_pos {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ) (τ : X.Ψ) :
    0 < _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) X.p0 := by
  have h1 := _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN_pos (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hG_of X τ) X.p0 X.p0_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (det_mat_ne_zero_of_mem_dom X hx τ)
  have h2 := h1 (fun j hj => _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.hsg_of X hx τ j hj)
  have hiso := hermC_emb_self_eq_zero_of_isIso X hξ τ
  have h3 := h2 (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ)
  have h4 := h3 hiso
  have hne : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ ≠ 0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.emb_ne_zero _ hξ.2.2
  exact h4 hne

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hiso` using `hermC_emb_self_eq_zero_of_isIso X hξ τ`. Establish `hflow : X.flow ξ s x = X.flowV (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) s x` using `rfl`. Establish `hH` using `mN_p0_pos X hx hξ τ`. Establish `hc` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ`. Establish `hf : 0 < 1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) X.p0`.

Use `mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hc.le) (hs τ)) hH.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1a` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_flow X hx (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ`. Establish `h1` using `h1a hiso s hf.ne'`. Establish `h2a` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_eq X hx (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ`.

Establish `h2` using `h2a hiso`. Rewrite `h1` using `[← hflow]`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt`. Rewrite using `[h1, h2]`. Clear the denominators using the available nonvanishing facts.
-/
private lemma tt_flow_eq_add_im {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ) (s : X.Ψ → ℂ)
    (hs : ∀ τ, 0 ≤ (s τ).im) (τ : X.Ψ) :
    X.tt ξ (X.flow ξ s x) τ = X.tt ξ x τ + (s τ).im := by
  have hiso := hermC_emb_self_eq_zero_of_isIso X hξ τ
  have hflow : X.flow ξ s x = X.flowV (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) s x := rfl
  have hH := mN_p0_pos X hx hξ τ
  have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ
  have hf : 0 < 1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) X.p0 := by
    have := mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hc.le) (hs τ)) hH.le
    linarith
  have h1a := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_flow X hx (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ
  have h1 := h1a hiso s hf.ne'
  have h2a := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.maj_eq X hx (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ
  have h2 := h2a hiso
  rw [← hflow] at h1
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt
  rw [h1, h2]
  field_simp

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hz` using `flow_mem_dom_of_im_nonneg' X hx hξ s hs`. Establish `hq` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.maj_two_sided X hx hξ s hz τ w`. Take `⟨ha, hlo, hhi⟩` from `hq`. Establish `hc` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ`. Establish `hm` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ)`.

Establish `hm0` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ w`. Use `set m := X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) with hm_def`. Use `set a := 1 + X.c τ * (s τ).im * m with ha_def`. Use `set d := 1 + X.c τ * |(s τ).re| * m with hd_def`. Establish `hcm : 0 ≤ X.c τ * m` using `mul_nonneg hc.le hm`.

Establish `ha1 : 1 ≤ a`. Establish `: 0 ≤ X.c τ * (s τ).im * m`. Rewrite using `[mul_right_comm]`. Conclude with `mul_nonneg hcm (hs τ)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hd1 : 1 ≤ d`. Establish `: 0 ≤ X.c τ * |(s τ).re| * m`. Rewrite using `[mul_right_comm]`. Conclude with `mul_nonneg hcm (abs_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hK0 : 0 ≤ K` using `hcm.trans (hK τ)`. Establish `hY0 : 0 ≤ Y` using `(hs τ).trans (hY τ)`. Establish `haK : a ≤ 1 + Y * K`. Establish `: X.c τ * (s τ).im * m ≤ Y * K`. Rewrite using `[mul_right_comm, mul_comm]`.

Conclude with `mul_le_mul (hY τ) (hK τ) hcm hY0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdK : d ≤ 1 + B * K`. Establish `: X.c τ * |(s τ).re| * m ≤ B * K`. Rewrite using `[mul_right_comm, mul_comm]`.

Conclude with `mul_le_mul (hB τ) (hK τ) hcm ((abs_nonneg _).trans (hB τ))`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hP : a * d ^ 2 ≤ (1 + Y * K) * (1 + B * K) ^ 2` using `mul_le_mul haK (pow_le_pow_left₀ (by linarith) hdK 2) (by positivity) (by linarith)`. Establish `hmin : min a a⁻¹ = a⁻¹` using `min_eq_right ((inv_le_one_of_one_le₀ ha1).trans ha1)`. Establish `hmax : max a a⁻¹ = a` using `max_eq_left ((inv_le_one_of_one_le₀ ha1).trans ha1)`.

Rewrite `hlo` using `[hmin]`. Rewrite `hhi` using `[hmax]`. Establish `ha0 : 0 < a` using `by linarith`. Establish `hd0 : 0 < d` using `by linarith`. Prove the components needed by the constructor for the conclusion.

Establish `e1 : a⁻¹ / d ^ 2 * X.maj x τ w = X.maj x τ w / (a * d ^ 2)`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Conclude with `hhi.trans (mul_le_mul_of_nonneg_right hP hm0)`.
-/
private lemma maj_flow_two_sided_bound {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ) (s : X.Ψ → ℂ) {Y B K : ℝ}
    (hs : ∀ τ, 0 ≤ (s τ).im) (hY : ∀ τ, (s τ).im ≤ Y) (hB : ∀ τ, |(s τ).re| ≤ B)
    (hK : ∀ τ, X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) ≤ K) (τ : X.Ψ) (w : Fin r → ℂ) :
    X.maj x τ w / ((1 + Y * K) * (1 + B * K) ^ 2) ≤ X.maj (X.flow ξ s x) τ w ∧
      X.maj (X.flow ξ s x) τ w ≤ (1 + Y * K) * (1 + B * K) ^ 2 * X.maj x τ w := by
  have hz := flow_mem_dom_of_im_nonneg' X hx hξ s hs
  have hq := _root_.ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.maj_two_sided X hx hξ s hz τ w
  obtain ⟨ha, hlo, hhi⟩ := hq
  have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ
  have hm := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ)
  have hm0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ w
  set m := X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) with hm_def
  set a := 1 + X.c τ * (s τ).im * m with ha_def
  set d := 1 + X.c τ * |(s τ).re| * m with hd_def
  have hcm : 0 ≤ X.c τ * m := mul_nonneg hc.le hm
  have ha1 : 1 ≤ a := by
    have : 0 ≤ X.c τ * (s τ).im * m := by
      rw [mul_right_comm]; exact mul_nonneg hcm (hs τ)
    linarith
  have hd1 : 1 ≤ d := by
    have : 0 ≤ X.c τ * |(s τ).re| * m := by
      rw [mul_right_comm]; exact mul_nonneg hcm (abs_nonneg _)
    linarith
  have hK0 : 0 ≤ K := hcm.trans (hK τ)
  have hY0 : 0 ≤ Y := (hs τ).trans (hY τ)
  have haK : a ≤ 1 + Y * K := by
    have : X.c τ * (s τ).im * m ≤ Y * K := by
      rw [mul_right_comm, mul_comm]
      exact mul_le_mul (hY τ) (hK τ) hcm hY0
    linarith
  have hdK : d ≤ 1 + B * K := by
    have : X.c τ * |(s τ).re| * m ≤ B * K := by
      rw [mul_right_comm, mul_comm]
      exact mul_le_mul (hB τ) (hK τ) hcm ((abs_nonneg _).trans (hB τ))
    linarith
  have hP : a * d ^ 2 ≤ (1 + Y * K) * (1 + B * K) ^ 2 :=
    mul_le_mul haK (pow_le_pow_left₀ (by linarith) hdK 2) (by positivity) (by linarith)
  have hmin : min a a⁻¹ = a⁻¹ := min_eq_right ((inv_le_one_of_one_le₀ ha1).trans ha1)
  have hmax : max a a⁻¹ = a := max_eq_left ((inv_le_one_of_one_le₀ ha1).trans ha1)
  rw [hmin] at hlo
  rw [hmax] at hhi
  have ha0 : 0 < a := by linarith
  have hd0 : 0 < d := by linarith
  constructor
  · have e1 : a⁻¹ / d ^ 2 * X.maj x τ w = X.maj x τ w / (a * d ^ 2) := by
      field_simp
    calc X.maj x τ w / ((1 + Y * K) * (1 + B * K) ^ 2)
        ≤ X.maj x τ w / (a * d ^ 2) := div_le_div_of_nonneg_left hm0 (by positivity) hP
      _ = a⁻¹ / d ^ 2 * X.maj x τ w := e1.symm
      _ ≤ _ := hlo
  · exact hhi.trans (mul_le_mul_of_nonneg_right hP hm0)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hz` using `flow_mem_dom_of_im_nonneg' X hx hξ s hs`. Use `set P := (1 + Y * K) * (1 + B * K) ^ 2 with hP_def`. Establish `hP1 : 1 ≤ P`. Establish `h1 : 1 ≤ 1 + Y * K` using `by nlinarith`. Establish `h2 : 1 ≤ (1 + B * K) ^ 2` using `one_le_pow₀ (by nlinarith)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hP0 : 0 < P` using `by linarith`. Establish `hb` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hz (k1 := 1 / P) (k2 := P) (by positivity) hP0 (fun τ w => by`. Rewrite using `[one_div_mul_eq_div]`. Conclude with `(maj_flow_two_sided_bound X hx hξ s hs hY hB hK τ w).1)`.

Use the proof step `(fun τ w => (maj_flow_two_sided_bound X hx hξ s hs hY hB hK τ w).2)`. Establish `hsq` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg X hx`. Establish `hlow : X.la1 x / P ≤ X.la1 (X.flow ξ s x)`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1 at hx1`.

Rewrite using `[Real.le_sqrt' (by positivity), div_pow, Real.sq_sqrt hsq]`. Combine the equalities or inequalities in the displayed calculation. Establish `hinv : 1 / X.la1 (X.flow ξ s x) ≤ P / X.la1 x`. Combine the equalities or inequalities in the displayed calculation. Establish `: P / X.la1 x = P * (1 / X.la1 x)` using `by ring`.

Use polynomial arithmetic with `[one_div_pos.mpr hx1]`.
-/
private lemma one_add_inv_la1_flow_le_mul {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ) (s : X.Ψ → ℂ) {Y B K : ℝ}
    (hs : ∀ τ, 0 ≤ (s τ).im) (hY : ∀ τ, (s τ).im ≤ Y) (hB : ∀ τ, |(s τ).re| ≤ B)
    (hK : ∀ τ, X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) ≤ K) (hK0 : 0 ≤ K) (hY0 : 0 ≤ Y)
    (hB0 : 0 ≤ B) (hx1 : 0 < X.la1 x) (hz1 : 0 < X.la1 (X.flow ξ s x)) :
    1 + 1 / X.la1 (X.flow ξ s x) ≤ (1 + Y * K) * (1 + B * K) ^ 2 * (1 + 1 / X.la1 x) := by
  have hz := flow_mem_dom_of_im_nonneg' X hx hξ s hs
  set P := (1 + Y * K) * (1 + B * K) ^ 2 with hP_def
  have hP1 : 1 ≤ P := by
    have h1 : 1 ≤ 1 + Y * K := by nlinarith
    have h2 : 1 ≤ (1 + B * K) ^ 2 := one_le_pow₀ (by nlinarith)
    nlinarith
  have hP0 : 0 < P := by linarith
  have hb := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_two_sided_bounds X hx hz (k1 := 1 / P) (k2 := P) (by positivity) hP0
    (fun τ w => by
      rw [one_div_mul_eq_div]
      exact (maj_flow_two_sided_bound X hx hξ s hs hY hB hK τ w).1)
    (fun τ w => (maj_flow_two_sided_bound X hx hξ s hs hY hB hK τ w).2)
  have hsq := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg X hx
  have hlow : X.la1 x / P ≤ X.la1 (X.flow ξ s x) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.la1 at hx1
    rw [Real.le_sqrt' (by positivity), div_pow, Real.sq_sqrt hsq]
    calc X.firstMinimumSq x / P ^ 2 ≤ X.firstMinimumSq x / P :=
          div_le_div_of_nonneg_left hsq hP0 (by nlinarith)
      _ = 1 / P * X.firstMinimumSq x := by ring
      _ ≤ _ := hb.1
  have hinv : 1 / X.la1 (X.flow ξ s x) ≤ P / X.la1 x := by
    calc 1 / X.la1 (X.flow ξ s x) ≤ 1 / (X.la1 x / P) :=
          one_div_le_one_div_of_le (by positivity) hlow
      _ = P / X.la1 x := one_div_div _ _
  have : P / X.la1 x = P * (1 / X.la1 x) := by ring
  nlinarith [one_div_pos.mpr hx1]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hiso` using `hermC_emb_self_eq_zero_of_isIso X hξ τ`. Establish `hflow : X.flow ξ s x = X.flowV (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) s x` using `rfl`. Establish `hc0` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq X x τ j`. Establish `hc1` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq X (X.flow ξ s x) τ j`. Establish `hd` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_flow X hx (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ`.

Establish `hd2` using `hd hiso s j (Nat.lt_succ_iff.mp j.2)`. Rewrite `hd2` using `[← hflow]`. Rewrite using `[hc0, hc1]`. Conclude with `hd2`.
-/
private lemma dmin_flow_eq_mul_one_add {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ) (s : X.Ψ → ℂ) (τ : X.Ψ)
    (j : Fin (r + 1)) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm (X.flow ξ s x) τ j = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ j *
      ↑(1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j) := by
  have hiso := hermC_emb_self_eq_zero_of_isIso X hξ τ
  have hflow : X.flow ξ s x = X.flowV (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) s x := rfl
  have hc0 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq X x τ j
  have hc1 := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_eq X (X.flow ξ s x) τ j
  have hd := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.dmin_flow X hx (fun τ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) τ
  have hd2 := hd hiso s j (Nat.lt_succ_iff.mp j.2)
  rw [← hflow] at hd2
  rw [hc0, hc1]
  exact hd2

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hQ0 : 0 < Q` using `by linarith`. Break down `le_or_gt 0 e with he | he` into its components or cases. Rewrite using `[abs_of_nonneg he, Real.rpow_neg hQ0.le, ← Real.inv_rpow hQ0.le]`. Conclude with `Real.rpow_le_rpow (inv_nonneg.mpr hQ0.le) hlo he`. Rewrite using `[abs_of_neg he, neg_neg]`.

Conclude with `Real.rpow_le_rpow_of_nonpos hq0 hhi he.le`.
-/
private lemma rpow_neg_abs_le_rpow_of_mem_Icc_inv {Q q e : ℝ} (hQ : 1 ≤ Q) (hq0 : 0 < q) (hlo : Q⁻¹ ≤ q)
    (hhi : q ≤ Q) : Q ^ (-|e|) ≤ q ^ e := by
  have hQ0 : 0 < Q := by linarith
  rcases le_or_gt 0 e with he | he
  · rw [abs_of_nonneg he, Real.rpow_neg hQ0.le, ← Real.inv_rpow hQ0.le]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hQ0.le) hlo he
  · rw [abs_of_neg he, neg_neg]
    exact Real.rpow_le_rpow_of_nonpos hq0 hhi he.le

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Use `set Q := 1 + Y * L with hQ_def`. Establish `hQ1 : 1 ≤ Q` using `by have := mul_nonneg hY0 hL0; linarith`. Establish `hQ0 : 0 < Q` using `by linarith`. Establish `hf : ∀ τ (j : Fin (r + 1)), 1 ≤ 1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j ∧ 1 + 2 * X.c τ * …`. Introduce `τ j`.

Establish `hH` using `mN_nonneg X hx hξ τ j (Nat.lt_succ_iff.mp j.2)`. Establish `hc` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ`. Establish `h2 : 0 ≤ 2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j` using `by positivity`. Establish `e : 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j = (s τ).im * (2 * X.c τ * _root_.ReciprocityTheory …` using `by ring`. Rewrite using `[e]`.

Conclude with `⟨by nlinarith [hs τ], by nlinarith [mul_le_mul (hY τ) (hL τ j) h2 hY0, hs τ]⟩`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac`. Rewrite using `[← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hQ0, ← Finset.prod_mul_distrib]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `τ _`.

Conclude with `mul_nonneg (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hQ0.le _)`. Introduce `τ _`. Rewrite using `[← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hQ0, ← Finset.prod_mul_distrib]`. Apply `Finset.prod_le_prod` to reduce the goal to its premises. Introduce `i _`.

Conclude with `mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hQ0.le _)`. Introduce `i _`. Rewrite using `[dmin_flow_eq_mul_one_add X hx hξ s τ i.succ, dmin_flow_eq_mul_one_add X hx hξ s τ i.castSucc]`. Take `⟨h1a, h1b⟩` from `hf τ i.succ`. Take `⟨h0a, h0b⟩` from `hf τ i.castSucc`.

Use `set f1 := 1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) ↑i.succ`. Use `set f0 := 1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) ↑i.castSucc`. Establish `hq0 : 0 < f1 / f0` using `by positivity`. Establish `e1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ * (f1 : ℂ) / (_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc * (f0 : ℂ)) = _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestric …`. Establish `: (f0 : ℂ) ≠ 0` using `by exact_mod_cast (show f0 ≠ 0 by positivity)`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, norm_mul, Complex.norm_of_nonneg hq0.le, Real.mul_rpow (norm_nonneg _) hq0.le]`. Apply `mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)` to reduce the goal to its premises. Apply `rpow_neg_abs_le_rpow_of_mem_Icc_inv hQ1 hq0` to reduce the goal to its premises.

Rewrite using `[le_div_iff₀ (by positivity)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma nfac_flow_ge_lemma_5 {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (s : X.Ψ → ℂ)
    {Y L : ℝ} (hs : ∀ τ, 0 ≤ (s τ).im) (hY : ∀ τ, (s τ).im ≤ Y) (hY0 : 0 ≤ Y) (hL0 : 0 ≤ L)
    (hL : ∀ τ (j : Fin (r + 1)),
      2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j ≤ L) :
    X.nfac la x * (1 + Y * L) ^ (-∑ τ, ∑ i : Fin r, |(-↑(la τ i) / 2 : ℝ)|) ≤
      X.nfac la (X.flow ξ s x) := by
  set Q := 1 + Y * L with hQ_def
  have hQ1 : 1 ≤ Q := by have := mul_nonneg hY0 hL0; linarith
  have hQ0 : 0 < Q := by linarith
  have hf : ∀ τ (j : Fin (r + 1)),
      1 ≤ 1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j ∧
      1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j ≤ Q := by
    intro τ j
    have hH := mN_nonneg X hx hξ τ j (Nat.lt_succ_iff.mp j.2)
    have hc := _root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ
    have h2 : 0 ≤ 2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j := by positivity
    have e : 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j =
        (s τ).im * (2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j) := by ring
    rw [e]
    exact ⟨by nlinarith [hs τ], by nlinarith [mul_le_mul (hY τ) (hL τ j) h2 hY0, hs τ]⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hQ0, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro τ _
    exact mul_nonneg (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg hQ0.le _)
  intro τ _
  rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hQ0, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro i _
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hQ0.le _)
  intro i _
  rw [dmin_flow_eq_mul_one_add X hx hξ s τ i.succ, dmin_flow_eq_mul_one_add X hx hξ s τ i.castSucc]
  obtain ⟨h1a, h1b⟩ := hf τ i.succ
  obtain ⟨h0a, h0b⟩ := hf τ i.castSucc
  set f1 := 1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) ↑i.succ
  set f0 := 1 + 2 * X.c τ * (s τ).im * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) ↑i.castSucc
  have hq0 : 0 < f1 / f0 := by positivity
  have e1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ * (f1 : ℂ) / (_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc * (f0 : ℂ)) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc * ((f1 / f0 : ℝ) : ℂ) := by
    have : (f0 : ℂ) ≠ 0 := by exact_mod_cast (show f0 ≠ 0 by positivity)
    push_cast
    field_simp
  rw [e1, norm_mul, Complex.norm_of_nonneg hq0.le, Real.mul_rpow (norm_nonneg _) hq0.le]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg _) _)
  apply rpow_neg_abs_le_rpow_of_mem_Icc_inv hQ1 hq0
  · rw [le_div_iff₀ (by positivity)]
    calc Q⁻¹ * f0 ≤ Q⁻¹ * Q := mul_le_mul_of_nonneg_left h0b (by positivity)
      _ = 1 := inv_mul_cancel₀ hQ0.ne'
      _ ≤ f1 := h1a
  · rw [div_le_iff₀ (by positivity)]
    nlinarith

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `hlim : Filter.Tendsto (fun y : ℝ => D * (1 + K) ^ A * (1 + L) ^ S * (y ^ (A + S) * Real.exp (-b * y))) Filter.atTop (𝓝 0)`. Simplify using `using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A + S) b hb).const_mul (D * (1 + K) ^ A * (1 + L) ^ S)`. Establish `hle : a ≤ 0`. Use `ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨2, fun y hy => (h y hy).trans ?_⟩)` and prove the remaining obligations. Establish `hy0 : 0 < y` using `by linarith`.

Establish `h1 : (1 + y * K) ^ A ≤ (1 + K) ^ A * y ^ A`. Rewrite using `[← Real.mul_rpow (by positivity) hy0.le]`. Conclude with `Real.rpow_le_rpow (by positivity) (by nlinarith) hA`. Establish `h2 : (1 + y * L) ^ S ≤ (1 + L) ^ S * y ^ S`. Rewrite using `[← Real.mul_rpow (by positivity) hy0.le]`.

Conclude with `Real.rpow_le_rpow (by positivity) (by nlinarith) hS`. Rewrite using `[Real.rpow_add hy0]`. Establish `he` using `(Real.exp_pos (-b * y)).le`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma eq_zero_of_le_poly_mul_exp_neg {a D K L A S b : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hA : 0 ≤ A) (hS : 0 ≤ S) (hb : 0 < b)
    (h : ∀ y : ℝ, 2 ≤ y → a ≤ D * (1 + y * K) ^ A * (1 + y * L) ^ S * Real.exp (-b * y)) :
    a = 0 := by
  have hlim : Filter.Tendsto
      (fun y : ℝ => D * (1 + K) ^ A * (1 + L) ^ S * (y ^ (A + S) * Real.exp (-b * y)))
      Filter.atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A + S) b hb).const_mul
      (D * (1 + K) ^ A * (1 + L) ^ S)
  have hle : a ≤ 0 := by
    refine ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨2, fun y hy => (h y hy).trans ?_⟩)
    have hy0 : 0 < y := by linarith
    have h1 : (1 + y * K) ^ A ≤ (1 + K) ^ A * y ^ A := by
      rw [← Real.mul_rpow (by positivity) hy0.le]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith) hA
    have h2 : (1 + y * L) ^ S ≤ (1 + L) ^ S * y ^ S := by
      rw [← Real.mul_rpow (by positivity) hy0.le]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith) hS
    rw [Real.rpow_add hy0]
    have he := (Real.exp_pos (-b * y)).le
    calc D * (1 + y * K) ^ A * (1 + y * L) ^ S * Real.exp (-b * y)
        ≤ D * ((1 + K) ^ A * y ^ A) * ((1 + L) ^ S * y ^ S) * Real.exp (-b * y) := by gcongr
      _ = _ := by ring
  linarith

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `H1 HGG r X la F a' hsec hgrowth ξ hξ ν hν x hx`. Take `⟨C, A, hA, hC⟩` from `hgrowth`. Take `⟨B, hB0, hB⟩` from `H1 r X la F hsec ξ hξ ν x hx`. Establish `hr : 0 < r` using `Nat.pos_of_ne_zero fun h => hξ.2.2 (funext fun i => absurd i.2 (by omega))`. Establish `hGG` using `HGG`.

Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration at hGG`. Take `⟨-, -, hpos⟩` from `hGG r X hr`. Use `haveI := _root_.GlobalTheory.ModeDecay.nonempty_cmType X`. Establish `hmaj0 : ∀ τ, 0 ≤ X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ)` using `fun τ => mul_nonneg (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ).le (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ _)`. Use `set K := ∑ τ, X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) with hK_def`.

Establish `hK : ∀ τ, X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) ≤ K` using `fun τ => Finset.single_le_sum (f := fun τ => X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ)) (fun τ _ => hmaj0 τ) (Finset.mem_univ τ)`. Establish `hK0 : 0 ≤ K` using `Finset.sum_nonneg fun τ _ => hmaj0 τ`. Establish `hH0 : ∀ τ (j : Fin (r + 1)), 0 ≤ 2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j` using `fun τ j => mul_nonneg (mul_nonneg zero_le_two (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ).le) (mN_nonneg X hx hξ τ j (Nat.lt_succ_iff.mp j.2))`. Use `set L := ∑ τ, ∑ j : Fin (r + 1), 2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j with hL_def`. Establish `hL : ∀ τ (j : Fin (r + 1)), 2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j ≤ L` using `fun τ j => (Finset.single_le_sum (f := fun j : Fin (r + 1) => 2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j) (f …`.

Establish `hL0 : 0 ≤ L` using `Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun j _ => hH0 τ j`. Establish `httx : ∀ τ, 0 ≤ X.tt ξ x τ` using `fun τ => by`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt`. Conclude with `one_div_nonneg.mpr (hmaj0 τ)`. Use `set τ0 : X.Ψ := Classical.arbitrary X.Ψ`.

Use `set T := X.tt ξ x τ0`. Use `set S := ∑ τ, ∑ i : Fin r, |(-↑(la τ i) / 2 : ℝ)| with hS_def`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => abs_nonneg _`. Establish `hN0 : 0 < X.nfac la x` using `_root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.nfac_pos X la hx`. Establish `hx1 : 0 < X.la1 x` using `hpos x hx`.

Use `set D := max C 0 * ((1 + B * K) ^ 2 * (1 + 1 / X.la1 x)) ^ A * Real.exp (4 * Real.pi * |a'| * T) / X.nfac la x with hD_def`. Establish `hD0 : 0 ≤ D`. Establish `h1 : 0 ≤ (1 + B * K) ^ 2 * (1 + 1 / X.la1 x)` using `mul_nonneg (sq_nonneg _) (add_nonneg zero_le_one (one_div_nonneg.mpr hx1.le))`. Conclude with `div_nonneg (mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg h1 _)) (Real.exp_pos _).le) hN0.le`. Establish `hbound : ∀ y : ℝ, 2 ≤ y → ∀ u : X.Ψ → ℝ, (∀ τ, |u τ| ≤ B) → ‖F (X.flow ξ (fun τ => (u τ : ℂ) + ((fun _ => y) τ : ℂ) * Complex.I) x)‖ ≤ D * (1 + y * K) ^ A * (1 + y * L) ^ S * Real.exp (-4 * Real.pi * a' * y)`.

Introduce `y hy u hu`. Use `set s : X.Ψ → ℂ := fun τ => (u τ : ℂ) + ((fun _ => y) τ : ℂ) * Complex.I with hs_def`. Establish `hsim : ∀ τ, (s τ).im = y` using `fun τ => by simp [hs_def]`. Establish `hsre : ∀ τ, (s τ).re = u τ` using `fun τ => by simp [hs_def]`. Establish `hy0 : 0 ≤ y` using `by linarith`.

Establish `hs0 : ∀ τ, 0 ≤ (s τ).im` using `fun τ => by rw [hsim]; exact hy0`. Establish `hsY : ∀ τ, (s τ).im ≤ y` using `fun τ => (hsim τ).le`. Establish `hsB : ∀ τ, |(s τ).re| ≤ B` using `fun τ => by rw [hsre]; exact hu τ`. Establish `hz` using `flow_mem_dom_of_im_nonneg' X hx hξ s hs0`. Establish `htt : ∀ τ, X.tt ξ (X.flow ξ s x) τ = X.tt ξ x τ + y` using `fun τ => by`.

Rewrite using `[tt_flow_eq_add_im X hx hξ s hs0 τ, hsim]`. Establish `htt2 : ∀ τ, 2 ≤ X.tt ξ (X.flow ξ s x) τ` using `fun τ => by`. Rewrite using `[htt]`. Combine the linear relations using `[httx τ]`. Establish `hinf1 : y ≤ ⨅ τ, X.tt ξ (X.flow ξ s x) τ` using `le_ciInf fun τ => by rw [htt]; linarith [httx τ]`.

Establish `hinf2 : ⨅ τ, X.tt ξ (X.flow ξ s x) τ ≤ T + y`. Use `ciInf_le (Finite.bddBelow_range fun τ => X.tt ξ (X.flow ξ s x) τ) τ0` as an intermediate fact. Rewrite `this` using `[htt]`. Conclude with `this`. Establish `key : -a' * (⨅ τ, X.tt ξ (X.flow ξ s x) τ) ≤ -a' * y + |a'| * T`.

Establish `e1` using `mul_le_mul_of_nonneg_right (neg_le_abs a') (sub_nonneg.2 hinf1)`. Establish `e2` using `mul_le_mul_of_nonneg_left (show (⨅ τ, X.tt ξ (X.flow ξ s x) τ) - y ≤ T by linarith) (abs_nonneg a')`. Use the polynomial consequences of the given equalities and inequalities. Establish `hexp : Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ (X.flow ξ s x) τ) ≤ Real.exp (-4 * Real.pi * a' * y) * Real.exp (4 * Real.pi * |a'| * T)`. Rewrite using `[← Real.exp_add]`.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 4 * Real.pi)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hz1 : 0 < X.la1 (X.flow ξ s x)` using `hpos _ hz`. Establish `hla` using `one_add_inv_la1_flow_le_mul X hx hξ s hs0 hsY hsB hK hK0 hy0 hB0 hx1 hz1`.

Establish `hpow : (1 + 1 / X.la1 (X.flow ξ s x)) ^ A ≤ ((1 + y * K) * (1 + B * K) ^ 2 * (1 + 1 / X.la1 x)) ^ A` using `Real.rpow_le_rpow (add_nonneg zero_le_one (one_div_nonneg.mpr hz1.le)) hla hA`. Establish `hnf` using `nfac_flow_ge_lemma_5 X hx hξ la s hs0 hsY hy0 hL0 hL`. Establish `hyL : 0 < 1 + y * L` using `by nlinarith`. Establish `hyK : 0 < 1 + y * K` using `by nlinarith`. Establish `hBK : 0 ≤ (1 + B * K) ^ 2 * (1 + 1 / X.la1 x)` using `mul_nonneg (sq_nonneg _) (add_nonneg zero_le_one (one_div_nonneg.mpr hx1.le))`.

Establish `hP0 : 0 ≤ (1 + y * K) * (1 + B * K) ^ 2 * (1 + 1 / X.la1 x)`. Rewrite using `[mul_assoc]`. Conclude with `mul_nonneg hyK.le hBK`. Establish `hQ0 : 0 < X.nfac la x * (1 + y * L) ^ (-S)` using `mul_pos hN0 (Real.rpow_pos_of_pos hyL _)`. Establish `hpn : ‖F (X.flow ξ s x)‖ * X.nfac la (X.flow ξ s x) ≤ max C 0 * ((1 + y * K) * (1 + B * K) ^ 2 * (1 + 1 / X.la1 x)) ^ A * (Real.exp (-4 * Real.pi * a' * y) * Real.exp (4 * Real.pi * |a'| * T))`.

Establish `h0` using `hC _ hz ξ hξ htt2`. Establish `hp : X.pnorm la F (X.flow ξ s x) = ‖F (X.flow ξ s x)‖ * X.nfac la (X.flow ξ s x)` using `rfl`. Rewrite using `[← hp]`. Use `h0.trans ?_` and prove the remaining obligations. Apply `mul_le_mul _ hexp (Real.exp_pos _).le (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hP0 _))` to reduce the goal to its premises.

Conclude with `mul_le_mul (le_max_left _ _) hpow (Real.rpow_nonneg (add_nonneg zero_le_one (one_div_nonneg.mpr hz1.le)) _) (le_max_right _ _)`. Establish `hFn : ‖F (X.flow ξ s x)‖ * (X.nfac la x * (1 + y * L) ^ (-S)) ≤ max C 0 * ((1 + y * K) * (1 + B * K) ^ 2 * (1 + 1 / X.la1 x)) ^ A * (Real.exp (-4 * Real.pi * a' * y) * Real.exp (4 * Real.pi * |a'| * T))` using `(mul_le_mul_of_nonneg_left hnf (norm_nonneg _)).trans hpn`. Rewrite `hFn` using `[← le_div_iff₀ hQ0]`. Use `hFn.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hD_def, Real.rpow_neg hyL.le, mul_assoc (1 + y * K), Real.mul_rpow hyK.le hBK]`.

Establish `: (0 : ℝ) < (1 + y * L) ^ S` using `Real.rpow_pos_of_pos hyL _`. Clear the denominators using the available nonvanishing facts. Establish `hfin : ∀ y : ℝ, 2 ≤ y → ‖X.fj la ξ ν F x‖ ≤ D * (1 + y * K) ^ A * (1 + y * L) ^ S * Real.exp (-(4 * Real.pi * (a' - ∑ τ, ν τ)) * y)`. Introduce `y hy`. Establish `h` using `hB (fun _ => y) _ (fun _ => by linarith) (hbound y hy)`.

Establish `e : ∑ τ, ν τ * (fun _ => y) τ = (∑ τ, ν τ) * y` using `by simp [Finset.sum_mul]`. Rewrite `h` using `[e]`. Establish `hexp : Real.exp (-(4 * Real.pi * (a' - ∑ τ, ν τ)) * y) = Real.exp (-4 * Real.pi * a' * y) * Real.exp (4 * Real.pi * (∑ τ, ν τ) * y)`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form.

Rewrite using `[hexp]`. Establish `hpos'` using `Real.exp_pos (-4 * Real.pi * (∑ τ, ν τ) * y)`. Establish `hinv : Real.exp (-4 * Real.pi * (∑ τ, ν τ) * y) * Real.exp (4 * Real.pi * (∑ τ, ν τ) * y) = 1`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form.

Conclude with `Real.exp_zero`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le` to reduce the goal to its premises. Establish `: -4 * Real.pi * (∑ τ, ν τ) * y = -4 * Real.pi * ((∑ τ, ν τ) * y)` using `by ring`. Rewrite using `[this]`.

Conclude with `h`. Use `_ = _ := by ring`. Establish `hb : 0 < 4 * Real.pi * (a' - ∑ τ, ν τ)`. Use `Real.pi_pos; have : 0 < a' - ∑ τ, ν τ := by linarith` as an intermediate fact. Check the signs of the components of the expression.

Conclude with `norm_eq_zero.mp (eq_zero_of_le_poly_mul_exp_neg (norm_nonneg _) hD0 hK0 hL0 hA hS0 hb hfin)`.
-/
theorem _root_.GlobalTheory.ModeDecay.fj_eq_zero_of_decay :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ), X.IsSec la F → ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, ∃ B : ℝ, 0 ≤ B ∧ ∀ (y : X.Ψ → ℝ) (M : ℝ), (∀ τ, 0 ≤ y τ) → (∀ u : X.Ψ → ℝ, (∀ τ, |u τ| ≤ B) → ‖F (X.flow ξ (fun τ => (u τ : ℂ) + (y τ : ℂ) * Complex.I) x)‖ ≤ M) → ‖X.fj la ξ ν F x‖ * Real.exp (-4 * Real.pi * ∑ τ, ν τ * y τ) ≤ M) → (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration (E := E)) → (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (F : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) (a' : ℝ), X.IsSec la F → (∃ C A : ℝ, 0 ≤ A ∧ ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, 2 ≤ X.tt ξ x τ) → X.pnorm la F x ≤ C * (1 + 1 / X.la1 x) ^ A * Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ x τ)) → ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∑ τ, ν τ < a' → ∀ x ∈ X.dom, X.fj la ξ ν F x = 0) := by
  intro H1 HGG r X la F a' hsec hgrowth ξ hξ ν hν x hx
  obtain ⟨C, A, hA, hC⟩ := hgrowth
  obtain ⟨B, hB0, hB⟩ := H1 r X la F hsec ξ hξ ν x hx
  have hr : 0 < r := Nat.pos_of_ne_zero fun h => hξ.2.2 (funext fun i => absurd i.2 (by omega))
  have hGG := HGG
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.LineBundleFirstBoundGlobalGeneration at hGG
  obtain ⟨-, -, hpos⟩ := hGG r X hr
  haveI := _root_.GlobalTheory.ModeDecay.nonempty_cmType X
  have hmaj0 : ∀ τ, 0 ≤ X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) := fun τ =>
    mul_nonneg (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ).le (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantConjugateTransfer.maj_nonneg X hx τ _)
  set K := ∑ τ, X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) with hK_def
  have hK : ∀ τ, X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) ≤ K := fun τ =>
    Finset.single_le_sum (f := fun τ => X.c τ * X.maj x τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ))
      (fun τ _ => hmaj0 τ) (Finset.mem_univ τ)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun τ _ => hmaj0 τ
  have hH0 : ∀ τ (j : Fin (r + 1)),
      0 ≤ 2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j := fun τ j =>
    mul_nonneg (mul_nonneg zero_le_two (_root_.ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms.c_pos X τ).le)
      (mN_nonneg X hx hξ τ j (Nat.lt_succ_iff.mp j.2))
  set L := ∑ τ, ∑ j : Fin (r + 1),
    2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j with hL_def
  have hL : ∀ τ (j : Fin (r + 1)),
      2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j ≤ L := fun τ j =>
    (Finset.single_le_sum (f := fun j : Fin (r + 1) =>
        2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j)
      (fun j _ => hH0 τ j) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun τ => ∑ j : Fin (r + 1),
        2 * X.c τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits.mN (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (↑τ) ξ) j)
      (fun τ _ => Finset.sum_nonneg fun j _ => hH0 τ j) (Finset.mem_univ τ))
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun j _ => hH0 τ j
  have httx : ∀ τ, 0 ≤ X.tt ξ x τ := fun τ => by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.tt
    exact one_div_nonneg.mpr (hmaj0 τ)
  set τ0 : X.Ψ := Classical.arbitrary X.Ψ
  set T := X.tt ξ x τ0
  set S := ∑ τ, ∑ i : Fin r, |(-↑(la τ i) / 2 : ℝ)| with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  have hN0 : 0 < X.nfac la x := _root_.ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.nfac_pos X la hx
  have hx1 : 0 < X.la1 x := hpos x hx
  set D := max C 0 * ((1 + B * K) ^ 2 * (1 + 1 / X.la1 x)) ^ A *
    Real.exp (4 * Real.pi * |a'| * T) / X.nfac la x with hD_def
  have hD0 : 0 ≤ D := by
    have h1 : 0 ≤ (1 + B * K) ^ 2 * (1 + 1 / X.la1 x) :=
      mul_nonneg (sq_nonneg _) (add_nonneg zero_le_one (one_div_nonneg.mpr hx1.le))
    exact div_nonneg (mul_nonneg (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg h1 _))
      (Real.exp_pos _).le) hN0.le
  have hbound : ∀ y : ℝ, 2 ≤ y → ∀ u : X.Ψ → ℝ, (∀ τ, |u τ| ≤ B) →
      ‖F (X.flow ξ (fun τ => (u τ : ℂ) + ((fun _ => y) τ : ℂ) * Complex.I) x)‖ ≤
        D * (1 + y * K) ^ A * (1 + y * L) ^ S * Real.exp (-4 * Real.pi * a' * y) := by
    intro y hy u hu
    set s : X.Ψ → ℂ := fun τ => (u τ : ℂ) + ((fun _ => y) τ : ℂ) * Complex.I with hs_def
    have hsim : ∀ τ, (s τ).im = y := fun τ => by simp [hs_def]
    have hsre : ∀ τ, (s τ).re = u τ := fun τ => by simp [hs_def]
    have hy0 : 0 ≤ y := by linarith
    have hs0 : ∀ τ, 0 ≤ (s τ).im := fun τ => by rw [hsim]; exact hy0
    have hsY : ∀ τ, (s τ).im ≤ y := fun τ => (hsim τ).le
    have hsB : ∀ τ, |(s τ).re| ≤ B := fun τ => by rw [hsre]; exact hu τ
    have hz := flow_mem_dom_of_im_nonneg' X hx hξ s hs0
    have htt : ∀ τ, X.tt ξ (X.flow ξ s x) τ = X.tt ξ x τ + y := fun τ => by
      rw [tt_flow_eq_add_im X hx hξ s hs0 τ, hsim]
    have htt2 : ∀ τ, 2 ≤ X.tt ξ (X.flow ξ s x) τ := fun τ => by
      rw [htt]; linarith [httx τ]
    have hinf1 : y ≤ ⨅ τ, X.tt ξ (X.flow ξ s x) τ :=
      le_ciInf fun τ => by rw [htt]; linarith [httx τ]
    have hinf2 : ⨅ τ, X.tt ξ (X.flow ξ s x) τ ≤ T + y := by
      have := ciInf_le (Finite.bddBelow_range fun τ => X.tt ξ (X.flow ξ s x) τ) τ0
      rw [htt] at this
      exact this
    have key : -a' * (⨅ τ, X.tt ξ (X.flow ξ s x) τ) ≤ -a' * y + |a'| * T := by
      have e1 := mul_le_mul_of_nonneg_right (neg_le_abs a') (sub_nonneg.2 hinf1)
      have e2 := mul_le_mul_of_nonneg_left (show (⨅ τ, X.tt ξ (X.flow ξ s x) τ) - y ≤ T by linarith)
        (abs_nonneg a')
      nlinarith
    have hexp : Real.exp (-4 * Real.pi * a' * ⨅ τ, X.tt ξ (X.flow ξ s x) τ) ≤
        Real.exp (-4 * Real.pi * a' * y) * Real.exp (4 * Real.pi * |a'| * T) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 4 * Real.pi)
      nlinarith
    have hz1 : 0 < X.la1 (X.flow ξ s x) := hpos _ hz
    have hla := one_add_inv_la1_flow_le_mul X hx hξ s hs0 hsY hsB hK hK0 hy0 hB0 hx1 hz1
    have hpow : (1 + 1 / X.la1 (X.flow ξ s x)) ^ A ≤
        ((1 + y * K) * (1 + B * K) ^ 2 * (1 + 1 / X.la1 x)) ^ A :=
      Real.rpow_le_rpow (add_nonneg zero_le_one (one_div_nonneg.mpr hz1.le)) hla hA
    have hnf := nfac_flow_ge_lemma_5 X hx hξ la s hs0 hsY hy0 hL0 hL
    have hyL : 0 < 1 + y * L := by nlinarith
    have hyK : 0 < 1 + y * K := by nlinarith
    have hBK : 0 ≤ (1 + B * K) ^ 2 * (1 + 1 / X.la1 x) :=
      mul_nonneg (sq_nonneg _) (add_nonneg zero_le_one (one_div_nonneg.mpr hx1.le))
    have hP0 : 0 ≤ (1 + y * K) * (1 + B * K) ^ 2 * (1 + 1 / X.la1 x) := by
      rw [mul_assoc]; exact mul_nonneg hyK.le hBK
    have hQ0 : 0 < X.nfac la x * (1 + y * L) ^ (-S) := mul_pos hN0 (Real.rpow_pos_of_pos hyL _)
    have hpn : ‖F (X.flow ξ s x)‖ * X.nfac la (X.flow ξ s x) ≤
        max C 0 * ((1 + y * K) * (1 + B * K) ^ 2 * (1 + 1 / X.la1 x)) ^ A *
          (Real.exp (-4 * Real.pi * a' * y) * Real.exp (4 * Real.pi * |a'| * T)) := by
      have h0 := hC _ hz ξ hξ htt2
      have hp : X.pnorm la F (X.flow ξ s x) = ‖F (X.flow ξ s x)‖ * X.nfac la (X.flow ξ s x) := rfl
      rw [← hp]
      refine h0.trans ?_
      apply mul_le_mul _ hexp (Real.exp_pos _).le
        (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hP0 _))
      exact mul_le_mul (le_max_left _ _) hpow
        (Real.rpow_nonneg (add_nonneg zero_le_one (one_div_nonneg.mpr hz1.le)) _) (le_max_right _ _)
    have hFn : ‖F (X.flow ξ s x)‖ * (X.nfac la x * (1 + y * L) ^ (-S)) ≤
        max C 0 * ((1 + y * K) * (1 + B * K) ^ 2 * (1 + 1 / X.la1 x)) ^ A *
          (Real.exp (-4 * Real.pi * a' * y) * Real.exp (4 * Real.pi * |a'| * T)) :=
      (mul_le_mul_of_nonneg_left hnf (norm_nonneg _)).trans hpn
    rw [← le_div_iff₀ hQ0] at hFn
    refine hFn.trans (le_of_eq ?_)
    rw [hD_def, Real.rpow_neg hyL.le, mul_assoc (1 + y * K), Real.mul_rpow hyK.le hBK]
    have : (0 : ℝ) < (1 + y * L) ^ S := Real.rpow_pos_of_pos hyL _
    field_simp
  have hfin : ∀ y : ℝ, 2 ≤ y → ‖X.fj la ξ ν F x‖ ≤
      D * (1 + y * K) ^ A * (1 + y * L) ^ S * Real.exp (-(4 * Real.pi * (a' - ∑ τ, ν τ)) * y) := by
    intro y hy
    have h := hB (fun _ => y) _ (fun _ => by linarith) (hbound y hy)
    have e : ∑ τ, ν τ * (fun _ => y) τ = (∑ τ, ν τ) * y := by simp [Finset.sum_mul]
    rw [e] at h
    have hexp : Real.exp (-(4 * Real.pi * (a' - ∑ τ, ν τ)) * y) =
        Real.exp (-4 * Real.pi * a' * y) * Real.exp (4 * Real.pi * (∑ τ, ν τ) * y) := by
      rw [← Real.exp_add]; ring_nf
    rw [hexp]
    have hpos' := Real.exp_pos (-4 * Real.pi * (∑ τ, ν τ) * y)
    have hinv : Real.exp (-4 * Real.pi * (∑ τ, ν τ) * y) * Real.exp (4 * Real.pi * (∑ τ, ν τ) * y) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    calc ‖X.fj la ξ ν F x‖ = ‖X.fj la ξ ν F x‖ * Real.exp (-4 * Real.pi * (∑ τ, ν τ) * y) *
          Real.exp (4 * Real.pi * (∑ τ, ν τ) * y) := by rw [mul_assoc, hinv, mul_one]
      _ ≤ D * (1 + y * K) ^ A * (1 + y * L) ^ S * Real.exp (-4 * Real.pi * a' * y) *
          Real.exp (4 * Real.pi * (∑ τ, ν τ) * y) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have : -4 * Real.pi * (∑ τ, ν τ) * y = -4 * Real.pi * ((∑ τ, ν τ) * y) := by ring
        rw [this]; exact h
      _ = _ := by ring
  have hb : 0 < 4 * Real.pi * (a' - ∑ τ, ν τ) := by
    have := Real.pi_pos; have : 0 < a' - ∑ τ, ν τ := by linarith
    positivity
  exact norm_eq_zero.mp (eq_zero_of_le_poly_mul_exp_neg (norm_nonneg _) hD0 hK0 hL0 hA hS0 hb hfin)

end GlobalTheory.ModeDecay
