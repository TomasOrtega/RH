import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

namespace GlobalTheory.CompanionTheory.EisTestFun

variable {k : Type} [Field k] [NumberField k]

/- English proof (translation)
Establish `h : ((ofFinite b : IdeleGroup k) : AdeleRing (𝓞 k) k).1 = (1 : AdeleRing (𝓞 k) k).1` using `rfl`. Unfold `infiniteModule`. Use `Finset.prod_eq_one fun w _ => ?_` and prove the remaining obligations. Rewrite using `[h, adele_fst_one_apply, norm_one, one_pow]`.
-/
theorem infiniteModule_ofFinite (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    infiniteModule (ofFinite b) = 1 := by
  have h : ((ofFinite b : IdeleGroup k) : AdeleRing (𝓞 k) k).1 = (1 : AdeleRing (𝓞 k) k).1 := rfl
  unfold infiniteModule
  refine Finset.prod_eq_one fun w _ => ?_
  rw [h, adele_fst_one_apply, norm_one, one_pow]

/- English proof (translation)
Rewrite using `[ideleModule_apply, infiniteModule_ofFinite, one_mul]`.
-/
theorem ideleModule_ofFinite (b : (FiniteAdeleRing (𝓞 k) k)ˣ) :
    (ideleModule k (ofFinite b) : ℝ) = finiteModule (ofFinite b) := by
  rw [ideleModule_apply, infiniteModule_ofFinite, one_mul]

/- English proof (translation)
Take `⟨hlc, hcs⟩` from `hg`. Use `⟨hlc.comp_continuous (continuous_pi fun _ => continuous_id), ?_⟩` and prove the remaining obligations. Conclude with `hcs.comp_homeomorph (Homeomorph.funUnique Unit (FiniteAdeleRing (𝓞 k) k)).symm`.
-/
theorem line_lc_cs {g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ}
    (hg : g ∈ GJMatrix.finiteSchwartzBruhatPi k) :
    IsLocallyConstant (fun t : FiniteAdeleRing (𝓞 k) k => g fun _ => t) ∧
      HasCompactSupport (fun t : FiniteAdeleRing (𝓞 k) k => g fun _ => t) := by
  obtain ⟨hlc, hcs⟩ := hg
  refine ⟨hlc.comp_continuous (continuous_pi fun _ => continuous_id), ?_⟩
  exact hcs.comp_homeomorph (Homeomorph.funUnique Unit (FiniteAdeleRing (𝓞 k) k)).symm

/- English proof (translation)
Introduce `K _ _ g hg hnn h1 x hx`. Use `haveI := isHaarMeasure_finiteIdeleMeasure K`. Take `⟨hlc, hcs⟩` from `line_lc_cs hg`. Take `⟨L, hL⟩` from `exists_subset_idealFiniteAdeles hcs.isCompact`. Take `⟨B, hB⟩` from `hlc.continuous.bounded_above_of_compact_support hcs`.

Set `G : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ` to `fun b => (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)).re`. Set `F : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ` to `fun b => G b * finiteZetaBound L x b`. Establish `hG0 : ∀ b, 0 ≤ G b`. Introduce `b`. Take `⟨r, hr, hgr⟩` from `hnn (b : FiniteAdeleRing (𝓞 K) K)`.

Simplify using `only [G, hgr, Complex.ofReal_re]`. Conclude with `hr`. Establish `hGc : Continuous G` using `Complex.continuous_re.comp (hlc.continuous.comp Units.continuous_val)`. Establish `hGB : ∀ b, ‖G b‖ ≤ B`. Introduce `b`.

Rewrite using `[Real.norm_eq_abs]`. Conclude with `(Complex.abs_re_le_norm _).trans (hB _)`. Establish `hint : Integrable F (finiteIdeleMeasure K)` using `(integrable_finiteZetaBound L hx).bdd_mul hGc.aestronglyMeasurable (Filter.Eventually.of_forall hGB)`. Establish `hF0 : 0 ≤ F` using `fun b => mul_nonneg (hG0 b) (finiteZetaBound_nonneg L x b)`. Establish `hzero : ∀ b : (FiniteAdeleRing (𝓞 K) K)ˣ, (b : FiniteAdeleRing (𝓞 K) K) ∉ idealFiniteAdeles L → (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = 0`.

Introduce `b hb`. Assume the negation of the conclusion as `hne`. Conclude with `hb (hL (subset_tsupport _ hne))`. Establish `heq : ∀ b : (FiniteAdeleRing (𝓞 K) K)ˣ, (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) * ((1 : HeckeCharacter K).toIdele (ofFinite b) : ℂ) * ((ideleModule K (ofFinite b) : ℝ) : ℂ) ^ (x : ℂ) = ((F b : ℝ) : ℂ)`. Introduce `b`.

Establish `hc : ((1 : HeckeCharacter K).toIdele (ofFinite b) : ℂ) = 1`. Rewrite using `[HeckeCharacter.toIdele_apply]`. Both sides reduce to the same expression. Rewrite using `[hc, mul_one, ideleModule_ofFinite]`. Simplify using `only [F, G, finiteZetaBound]`.

Use `split_ifs with hb`. Take `⟨r, hr, hgr⟩` from `hnn (b : FiniteAdeleRing (𝓞 K) K)`. Rewrite using `[hgr, Complex.ofReal_re, Complex.ofReal_mul, Complex.ofReal_cpow (finiteModule_pos _).le]`. Rewrite using `[hzero b hb]`. Simplify using the standard rewrite rules.

Establish `hI : zFin g 1 (x : ℂ) = ((∫ b, F b ∂finiteIdeleMeasure K : ℝ) : ℂ)`. Unfold `zFin`. Conclude with `(integral_congr_ae (Filter.Eventually.of_forall heq)).trans integral_complex_ofReal`. Set `U : Set (FiniteAdeleRing (𝓞 K) K)ˣ` to `{b | (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = g fun _ => 1}`. Establish `hUo : IsOpen U` using `(hlc.comp_continuous Units.continuous_val).isOpen_fiber _`.

Establish `h1U : (1 : (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ U` using `by show (g fun _ => ((1 : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)) = g fun _ => 1`. Rewrite using `[Units.val_one]`. Take `⟨r, hr, hgr⟩` from `hnn 1`. Establish `hr0 : 0 < r`. Use `lt_of_le_of_ne hr ?_` and prove the remaining obligations.

Introduce and unpack `rfl`. Conclude with `h1 (by rw [hgr, Complex.ofReal_zero])`. Establish `hUsub : U ⊆ Function.support F`. Introduce `b hb`. Establish `hgb : (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = r` using `(show _ = _ from hb).trans hgr`.

Establish `hmem : (b : FiniteAdeleRing (𝓞 K) K) ∈ idealFiniteAdeles L`. Assume the negation of the conclusion as `hn`. Establish `h0` using `hzero b hn`. Rewrite `h0` using `[hgb]`. Conclude with `hr0.ne' (by exact_mod_cast h0)`.

Rewrite using `[Function.mem_support]`. Simplify using `only [F, G, finiteZetaBound, if_pos hmem, hgb, Complex.ofReal_re]`. Conclude with `(mul_pos hr0 (Real.rpow_pos_of_pos (finiteModule_pos _) _)).ne'`. Establish `hpos : 0 < finiteIdeleMeasure K (Function.support F)` using `(hUo.measure_pos _ ⟨1, h1U⟩).trans_le (measure_mono hUsub)`. Rewrite using `[hI, Complex.ofReal_ne_zero]`.

Conclude with `((integral_pos_iff_support_of_nonneg hF0 hint).2 hpos).ne'`.
-/
theorem zFinPos : ZFinPos := by
  intro K _ _ g hg hnn h1 x hx
  haveI := isHaarMeasure_finiteIdeleMeasure K
  obtain ⟨hlc, hcs⟩ := line_lc_cs hg
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles hcs.isCompact
  obtain ⟨B, hB⟩ := hlc.continuous.bounded_above_of_compact_support hcs
  let G : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ := fun b => (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)).re
  let F : (FiniteAdeleRing (𝓞 K) K)ˣ → ℝ := fun b => G b * finiteZetaBound L x b
  have hG0 : ∀ b, 0 ≤ G b := by
    intro b
    obtain ⟨r, hr, hgr⟩ := hnn (b : FiniteAdeleRing (𝓞 K) K)
    simp only [G, hgr, Complex.ofReal_re]
    exact hr
  have hGc : Continuous G :=
    Complex.continuous_re.comp (hlc.continuous.comp Units.continuous_val)
  have hGB : ∀ b, ‖G b‖ ≤ B := by
    intro b
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (hB _)
  have hint : Integrable F (finiteIdeleMeasure K) :=
    (integrable_finiteZetaBound L hx).bdd_mul hGc.aestronglyMeasurable
      (Filter.Eventually.of_forall hGB)
  have hF0 : 0 ≤ F := fun b => mul_nonneg (hG0 b) (finiteZetaBound_nonneg L x b)
  have hzero : ∀ b : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (b : FiniteAdeleRing (𝓞 K) K) ∉ idealFiniteAdeles L →
        (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = 0 := by
    intro b hb
    by_contra hne
    exact hb (hL (subset_tsupport _ hne))
  have heq : ∀ b : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) * ((1 : HeckeCharacter K).toIdele (ofFinite b) : ℂ) *
        ((ideleModule K (ofFinite b) : ℝ) : ℂ) ^ (x : ℂ) = ((F b : ℝ) : ℂ) := by
    intro b
    have hc : ((1 : HeckeCharacter K).toIdele (ofFinite b) : ℂ) = 1 := by
      rw [HeckeCharacter.toIdele_apply]
      rfl
    rw [hc, mul_one, ideleModule_ofFinite]
    simp only [F, G, finiteZetaBound]
    split_ifs with hb
    · obtain ⟨r, hr, hgr⟩ := hnn (b : FiniteAdeleRing (𝓞 K) K)
      rw [hgr, Complex.ofReal_re, Complex.ofReal_mul,
        Complex.ofReal_cpow (finiteModule_pos _).le]
    · rw [hzero b hb]
      simp
  have hI : zFin g 1 (x : ℂ) = ((∫ b, F b ∂finiteIdeleMeasure K : ℝ) : ℂ) := by
    unfold zFin
    exact (integral_congr_ae (Filter.Eventually.of_forall heq)).trans integral_complex_ofReal
  let U : Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
    {b | (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = g fun _ => 1}
  have hUo : IsOpen U := (hlc.comp_continuous Units.continuous_val).isOpen_fiber _
  have h1U : (1 : (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ U := by
    show (g fun _ => ((1 : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)) = g fun _ => 1
    rw [Units.val_one]
  obtain ⟨r, hr, hgr⟩ := hnn 1
  have hr0 : 0 < r := by
    refine lt_of_le_of_ne hr ?_
    rintro rfl
    exact h1 (by rw [hgr, Complex.ofReal_zero])
  have hUsub : U ⊆ Function.support F := by
    intro b hb
    have hgb : (g fun _ => (b : FiniteAdeleRing (𝓞 K) K)) = r := (show _ = _ from hb).trans hgr
    have hmem : (b : FiniteAdeleRing (𝓞 K) K) ∈ idealFiniteAdeles L := by
      by_contra hn
      have h0 := hzero b hn
      rw [hgb] at h0
      exact hr0.ne' (by exact_mod_cast h0)
    rw [Function.mem_support]
    simp only [F, G, finiteZetaBound, if_pos hmem, hgb, Complex.ofReal_re]
    exact (mul_pos hr0 (Real.rpow_pos_of_pos (finiteModule_pos _) _)).ne'
  have hpos : 0 < finiteIdeleMeasure K (Function.support F) :=
    (hUo.measure_pos _ ⟨1, h1U⟩).trans_le (measure_mono hUsub)
  rw [hI, Complex.ofReal_ne_zero]
  exact ((integral_pos_iff_support_of_nonneg hF0 hint).2 hpos).ne'

end GlobalTheory.CompanionTheory.EisTestFun
