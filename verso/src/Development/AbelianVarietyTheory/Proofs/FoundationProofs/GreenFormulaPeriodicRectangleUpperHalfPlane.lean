import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory

open scoped Interval

/- English proof (translation)
Introduce `G D T a b hT ha hab hG hD hper`. Set `φL : ℝ × ℝ →L[ℝ] ℂ` to `(ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (1 : ℂ) + (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Complex.I`. Establish `hφ : ∀ p : ℝ × ℝ, φL p = (p.2 : ℂ) + (p.1 : ℂ) * Complex.I`. Introduce `p`. Simplify using `[φL, Complex.real_smul]`.

Establish `him : ∀ p : ℝ × ℝ, (φL p).im = p.1`. Introduce `p`. Simplify using `[hφ]`. Establish `hder : ∀ s : ℂ, 0 < s.im → HasFDerivAt G (fderiv ℝ G s) s ∧ fderiv ℝ G s Complex.I - Complex.I * fderiv ℝ G s 1 = D s`. Introduce `s hs`.

Take `⟨L, hL, hLD⟩` from `hG s hs`. Rewrite using `[hL.fderiv]`. Conclude with `⟨hL, hLD⟩`. Establish `hRpos : ∀ p ∈ [[a, b]] ×ˢ [[(0:ℝ), T]], 0 < (φL p).im`. Introduce `p hp`.

Rewrite using `[him]`. Establish `h1` using `hp.1`. Rewrite `h1` using `[Set.uIcc_of_le hab]`. Conclude with `lt_of_lt_of_le ha h1.1`. Establish `hGc : ContinuousOn G {s : ℂ | 0 < s.im}` using `fun s hs => ((hder s hs).1.continuousAt).continuousWithinAt`.

Establish `hfc : ContinuousOn (fun p => G (φL p)) ([[a, b]] ×ˢ [[(0:ℝ), T]])` using `hGc.comp φL.continuous.continuousOn (fun p hp => hRpos p hp)`. Establish `hsub : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min (0:ℝ) T) (max 0 T), x ∈ [[a, b]] ×ˢ [[(0:ℝ), T]]` using `fun x hx => ⟨Set.Ioo_subset_Icc_self hx.1, Set.Ioo_subset_Icc_self hx.2⟩`. Establish `hdf : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min (0:ℝ) T) (max 0 T), HasFDerivAt (fun p => G (φL p)) ((fderiv ℝ G (φL x)).comp φL) x` using `fun x hx => (hder _ (hRpos x (hsub x hx))).1.comp x φL.hasFDerivAt`. Establish `hpt : ∀ p : ℝ × ℝ, 0 < p.1 → (fderiv ℝ G (φL p)).comp φL (1, 0) + ((-Complex.I) • (fderiv ℝ G (φL p)).comp φL) (0, 1) = D (φL p)`. Introduce `p hp`.

Establish `h` using `(hder (φL p) (by rw [him]; exact hp)).2`. Rewrite using `[← h]`. Simplify using `only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, hφ, smul_eq_mul]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish `hi : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (fderiv ℝ G (φL p)).comp φL (1, 0) + ((-Complex.I) • (fderiv ℝ G (φL p)).comp φL) (0, 1)) ([[a, b]] ×ˢ [[(0:ℝ), T]])`. Establish `hc : ContinuousOn (fun p => D (φL p)) ([[a, b]] ×ˢ [[(0:ℝ), T]])` using `hD.comp φL.continuous.continuousOn (fun p hp => hRpos p hp)`. Use `(hc.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun ?_ (measurableSet_uIcc.prod measurableSet_uIcc)` and prove the remaining obligations. Introduce `p hp`. Use `hRpos p hp` as an intermediate fact.

Rewrite `this` using `[him]`. Conclude with `(hpt p this).symm`. Establish `key` using `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt (fun p => G (φL p)) (fun p => (-Complex.I) • G (φL p)) (fun p => (fderiv ℝ G (φL p)).comp φL) (fun p => (-Complex.I) • (fderiv ℝ G (φL p)).comp φL) a 0 b T hfc (by exact hfc.const_smul (-Complex.I)) hdf (fun x hx => by exact …`. Establish `hL : (∫ y in a..b, ∫ x in (0:ℝ)..T, (fderiv ℝ G (φL (y, x))).comp φL (1, 0) + ((-Complex.I) • (fderiv ℝ G (φL (y, x))).comp φL) (0, 1)) = ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I)`. Use `intervalIntegral.integral_congr (fun y hy => ?_)` and prove the remaining obligations.

Use `intervalIntegral.integral_congr (fun x _ => ?_)` and prove the remaining obligations. Establish `hy' : 0 < y`. Rewrite `hy` using `[Set.uIcc_of_le hab]`. Conclude with `lt_of_lt_of_le ha hy.1`. Apply the tactic sequence `try simp only`.

Rewrite using `[hpt (y, x) hy', hφ]`. Establish `hg : (∫ y in a..b, (-Complex.I) • G (φL (y, T))) = ∫ y in a..b, (-Complex.I) • G (φL (y, 0))`. Use `intervalIntegral.integral_congr (fun y hy => ?_)` and prove the remaining obligations. Establish `hy' : 0 < y`. Rewrite `hy` using `[Set.uIcc_of_le hab]`.

Conclude with `lt_of_lt_of_le ha hy.1`. Apply the tactic sequence `try simp only`. Establish `: φL (y, T) = φL (y, 0) + (T : ℂ)` using `by rw [hφ, hφ]; push_cast; ring`. Rewrite using `[this, hper _ (by rw [him]; exact hy')]`. Rewrite `key` using `[hL, hg, sub_self, zero_add]`.

Rewrite using `[key]`. Simplify using `only [hφ]`.
-/
theorem green_periodic_rectangle : ∀ (G D : ℂ → ℂ) (T a b : ℝ), 0 < T → 0 < a → a ≤ b →
    (∀ s : ℂ, 0 < s.im → ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt G L s ∧ L Complex.I - Complex.I * L 1 = D s) →
    ContinuousOn D {s : ℂ | 0 < s.im} → (∀ s : ℂ, 0 < s.im → G (s + T) = G s) →
    (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (b : ℂ) * Complex.I)) -
      (∫ x in (0 : ℝ)..T, G ((x : ℂ) + (a : ℂ) * Complex.I)) =
      ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I) := by
  intro G D T a b hT ha hab hG hD hper
  let φL : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (1 : ℂ) +
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight Complex.I
  have hφ : ∀ p : ℝ × ℝ, φL p = (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
    intro p; simp [φL, Complex.real_smul]
  have him : ∀ p : ℝ × ℝ, (φL p).im = p.1 := by
    intro p; simp [hφ]
  have hder : ∀ s : ℂ, 0 < s.im → HasFDerivAt G (fderiv ℝ G s) s ∧
      fderiv ℝ G s Complex.I - Complex.I * fderiv ℝ G s 1 = D s := by
    intro s hs
    obtain ⟨L, hL, hLD⟩ := hG s hs
    rw [hL.fderiv]; exact ⟨hL, hLD⟩
  have hRpos : ∀ p ∈ [[a, b]] ×ˢ [[(0:ℝ), T]], 0 < (φL p).im := by
    intro p hp
    rw [him]
    have h1 := hp.1
    rw [Set.uIcc_of_le hab] at h1
    exact lt_of_lt_of_le ha h1.1
  have hGc : ContinuousOn G {s : ℂ | 0 < s.im} := fun s hs =>
    ((hder s hs).1.continuousAt).continuousWithinAt
  have hfc : ContinuousOn (fun p => G (φL p)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) :=
    hGc.comp φL.continuous.continuousOn (fun p hp => hRpos p hp)
  have hsub : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min (0:ℝ) T) (max 0 T),
      x ∈ [[a, b]] ×ˢ [[(0:ℝ), T]] := fun x hx =>
    ⟨Set.Ioo_subset_Icc_self hx.1, Set.Ioo_subset_Icc_self hx.2⟩
  have hdf : ∀ x ∈ Set.Ioo (min a b) (max a b) ×ˢ Set.Ioo (min (0:ℝ) T) (max 0 T),
      HasFDerivAt (fun p => G (φL p)) ((fderiv ℝ G (φL x)).comp φL) x := fun x hx =>
    (hder _ (hRpos x (hsub x hx))).1.comp x φL.hasFDerivAt
  have hpt : ∀ p : ℝ × ℝ, 0 < p.1 →
      (fderiv ℝ G (φL p)).comp φL (1, 0) + ((-Complex.I) • (fderiv ℝ G (φL p)).comp φL) (0, 1)
        = D (φL p) := by
    intro p hp
    have h := (hder (φL p) (by rw [him]; exact hp)).2
    rw [← h]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, hφ, smul_eq_mul]
    simp
    ring
  have hi : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => (fderiv ℝ G (φL p)).comp φL (1, 0) +
        ((-Complex.I) • (fderiv ℝ G (φL p)).comp φL) (0, 1)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) := by
    have hc : ContinuousOn (fun p => D (φL p)) ([[a, b]] ×ˢ [[(0:ℝ), T]]) :=
      hD.comp φL.continuous.continuousOn (fun p hp => hRpos p hp)
    refine (hc.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).congr_fun ?_
      (measurableSet_uIcc.prod measurableSet_uIcc)
    intro p hp
    have := hRpos p hp
    rw [him] at this
    exact (hpt p this).symm
  have key := MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
    (fun p => G (φL p)) (fun p => (-Complex.I) • G (φL p))
    (fun p => (fderiv ℝ G (φL p)).comp φL) (fun p => (-Complex.I) • (fderiv ℝ G (φL p)).comp φL)
    a 0 b T hfc (by exact hfc.const_smul (-Complex.I)) hdf (fun x hx => by exact (hdf x hx).const_smul (-Complex.I)) hi
  have hL : (∫ y in a..b, ∫ x in (0:ℝ)..T,
      (fderiv ℝ G (φL (y, x))).comp φL (1, 0) +
        ((-Complex.I) • (fderiv ℝ G (φL (y, x))).comp φL) (0, 1)) =
      ∫ y in a..b, ∫ x in (0 : ℝ)..T, D ((x : ℂ) + (y : ℂ) * Complex.I) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    have hy' : 0 < y := by
      rw [Set.uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1
    try simp only
    rw [hpt (y, x) hy', hφ]
  have hg : (∫ y in a..b, (-Complex.I) • G (φL (y, T))) =
      ∫ y in a..b, (-Complex.I) • G (φL (y, 0)) := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    have hy' : 0 < y := by
      rw [Set.uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1
    try simp only
    have : φL (y, T) = φL (y, 0) + (T : ℂ) := by rw [hφ, hφ]; push_cast; ring
    rw [this, hper _ (by rw [him]; exact hy')]
  rw [hL, hg, sub_self, zero_add] at key
  rw [key]
  simp only [hφ]

end GlobalTheory
