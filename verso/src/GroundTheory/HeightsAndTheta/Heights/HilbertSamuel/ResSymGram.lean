import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResSymMeasure
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResSym

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.AnForm.M
open scoped ENNReal ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

/- English proof (translation)
Rewrite using `[secFun_smul hb, secFun_smul hb', wgt, wgt, m.smul, map_mul, map_pow]`. Establish `hc' : (‖c‖ : ℂ) ≠ 0` using `by simpa using hc`. Establish `hk : starRingEnd ℂ c ^ n * c ^ n = (‖c‖ : ℂ) ^ (2 * n)`. Rewrite using `[← mul_pow, Complex.conj_mul', ← pow_mul]`. Use `push_cast`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hk, mul_inv_cancel₀ (pow_ne_zero _ hc'), one_mul]`.
-/
theorem gramFun_smul {m : ConeMetric ℂ (Ix κ)} {n : ℕ} {b b' : MvPolynomial (Ix κ) ℚ}
    (hb : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f)
    (hb' : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b' = map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : Ix κ → ℂ) (hc : c ≠ 0) :
    starRingEnd ℂ (secFun b (c • z)) * secFun b' (c • z) * (wgt m n (c • z) : ℂ) =
      starRingEnd ℂ (secFun b z) * secFun b' z * (wgt m n z : ℂ) := by
  rw [secFun_smul hb, secFun_smul hb', wgt, wgt, m.smul, map_mul, map_pow]
  have hc' : (‖c‖ : ℂ) ≠ 0 := by simpa using hc
  have hk : starRingEnd ℂ c ^ n * c ^ n = (‖c‖ : ℂ) ^ (2 * n) := by
    rw [← mul_pow, Complex.conj_mul', ← pow_mul]
  push_cast
  calc _ = (starRingEnd ℂ c ^ n * c ^ n) * ((‖c‖ : ℂ) ^ (2 * n))⁻¹ *
          (starRingEnd ℂ (secFun b z) * secFun b' z * ((m.ρ z : ℂ) ^ (2 * n))⁻¹) := by ring
    _ = _ := by
        rw [hk, mul_inv_cancel₀ (pow_ne_zero _ hc'), one_mul]

/- English proof (translation)
Establish `hρ : ContinuousOn m.ρ {0}ᶜ` using `continuousOn_rho hm`. Use `(((continuous_secFun _).continuousOn.star).mul (continuous_secFun _).continuousOn).mul (Complex.continuous_ofReal.comp_continuousOn ((hρ.pow _).inv₀ fun z hz => ?_))` and prove the remaining obligations. Conclude with `pow_ne_zero _ (m.pos z hz).ne'`.
-/
theorem continuousOn_gramFun {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) (n : ℕ)
    (b b' : MvPolynomial (Ix κ) ℚ) :
    ContinuousOn (fun z => starRingEnd ℂ (secFun b z) * secFun b' z * (wgt m n z : ℂ)) {0}ᶜ := by
  have hρ : ContinuousOn m.ρ {0}ᶜ := continuousOn_rho hm
  refine (((continuous_secFun _).continuousOn.star).mul (continuous_secFun _).continuousOn).mul
    (Complex.continuous_ofReal.comp_continuousOn ((hρ.pow _).inv₀ fun z hz => ?_))
  exact pow_ne_zero _ (m.pos z hz).ne'

/- English proof (translation)
Use `set h : (Ix κ → ℂ) → ℂ := fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ) with hh`. Establish `hcont : ContinuousOn h {0}ᶜ` using `continuousOn_gramFun d.smooth n (b i) (b j)`. Establish `hsm : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → h (c • z) = h z` using `fun c z hc => gramFun_smul (hb i) (hb j) c z hc`. Take `⟨C, hC⟩` from `(isCompact_sphere (0 : Ix κ → ℂ) 1).exists_bound_of_continuousOn (hcont.mono fun z hz => by`. Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff]`.

Introduce and unpack `rfl`. Simplify using `at hz)`. Establish `hbd : ∀ z, ‖h z‖ ≤ max C ‖h 0‖`. Introduce `z`. Distinguish the cases in `hz : z = 0`.

Rewrite using `[hz]`. Conclude with `le_max_right _ _`. Establish `hz' : (‖z‖ : ℂ) ≠ 0` using `by simpa using hz`. Establish `hu : ((‖z‖ : ℂ)⁻¹ • z) ∈ Metric.sphere (0 : Ix κ → ℂ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]`.

Establish `: z = (‖z‖ : ℂ) • ((‖z‖ : ℂ)⁻¹ • z)` using `by rw [smul_smul, mul_inv_cancel₀ hz', one_smul]`. Rewrite using `[this, hsm _ _ hz']`. Conclude with `(hC _ hu).trans (le_max_left _ _)`. Conclude with `Integrable.of_bound (measurable_of_continuousOn_compl_singleton 0 hcont).aestronglyMeasurable _ (Filter.Eventually.of_forall hbd)`.
-/
theorem integrable_gram (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (i j : Fin r) :
    Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ))
      (symMeasure d) := by
  set h : (Ix κ → ℂ) → ℂ := fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ)
    with hh
  have hcont : ContinuousOn h {0}ᶜ := continuousOn_gramFun d.smooth n (b i) (b j)
  have hsm : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → h (c • z) = h z := fun c z hc =>
    gramFun_smul (hb i) (hb j) c z hc
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Ix κ → ℂ) 1).exists_bound_of_continuousOn
    (hcont.mono fun z hz => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      simp at hz)
  have hbd : ∀ z, ‖h z‖ ≤ max C ‖h 0‖ := by
    intro z
    by_cases hz : z = 0
    · rw [hz]; exact le_max_right _ _
    · have hz' : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
      have hu : ((‖z‖ : ℂ)⁻¹ • z) ∈ Metric.sphere (0 : Ix κ → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
      have : z = (‖z‖ : ℂ) • ((‖z‖ : ℂ)⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hz', one_smul]
      rw [this, hsm _ _ hz']
      exact (hC _ hu).trans (le_max_left _ _)
  exact Integrable.of_bound (measurable_of_continuousOn_compl_singleton 0 hcont).aestronglyMeasurable
    _ (Filter.Eventually.of_forall hbd)

/- English proof (translation)
Use `⟨fun k => ?_, hz.2⟩` and prove the remaining obligations. Take `⟨p, hp⟩` from `Function.ne_iff.mp hz.1`. Conclude with `⟨p.2, by cases k; exact hp⟩`.
-/
theorem mem_mcPts_of_pts {x : Ix κ → Ω} {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ x) := by
  refine ⟨fun k => ?_, hz.2⟩
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hz.1
  exact ⟨p.2, by cases k; exact hp⟩

/- English proof (translation)
Take `⟨S, hS, hJ⟩` from `d.R.homog`. Establish `: ¬ S ⊆ coordIdeal ℤ d.x` using `fun hsub => d.R.nondeg (by`. Rewrite using `[hJ]`. Conclude with `Ideal.span_le.mpr hsub)`. Take `⟨g, hgS, hgP⟩` from `Set.not_subset.mp this`.

Take `⟨a, ha⟩` from `hS g hgS`. Establish `hhom : g.IsHomogeneous (a ())`. Introduce `m hm`. Establish `h` using `ha m (mem_support_iff.mpr hm) ()`. Simplify using `only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]`.

Rewrite using `[Finsupp.sum_fintype _ _ (fun _ => rfl)]`. Simplify `h` using `[Fintype.sum_sigma]`. Use `⟨g, a (), ?_, hhom, fun h0 => hgP (mem_coordIdeal_of_isHomogeneous ℤ d.x hhom h0)⟩` and prove the remaining obligations. Rewrite using `[hJ]`. Conclude with `Ideal.subset_span hgS`.
-/
theorem exists_form_J (d : HSMDatum D Ω κ) :
    ∃ (g : MvPolynomial (Ix κ) ℤ) (N : ℕ), g ∈ d.J ∧ g.IsHomogeneous N ∧ aeval d.x g ≠ 0 := by
  obtain ⟨S, hS, hJ⟩ := d.R.homog
  have : ¬ S ⊆ coordIdeal ℤ d.x := fun hsub => d.R.nondeg (by
    rw [hJ]; exact Ideal.span_le.mpr hsub)
  obtain ⟨g, hgS, hgP⟩ := Set.not_subset.mp this
  obtain ⟨a, ha⟩ := hS g hgS
  have hhom : g.IsHomogeneous (a ()) := by
    intro m hm
    have h := ha m (mem_support_iff.mpr hm) ()
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simpa [Fintype.sum_sigma] using h
  refine ⟨g, a (), ?_, hhom, fun h0 => hgP (mem_coordIdeal_of_isHomogeneous ℤ d.x hhom h0)⟩
  rw [hJ]
  exact Ideal.subset_span hgS

/- English proof (translation)
Establish `hint` using `integrable_gram d hb.1`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos (bGram_isHermitian _ _ _) fun c hc => ?_` and prove the remaining obligations. Rewrite using `[dot_bGram _ _ _ hint c, Complex.zero_lt_real]`. Use `set h : (Ix κ → ℂ) → ℝ := fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt d.m n z with hh`. Establish `hnn : ∀ z, 0 ≤ h z` using `fun z => mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg z) _))`.

Establish `hcont : ContinuousOn h {0}ᶜ` using `continuousOn_normSq d.smooth b c`. Establish `hdeg : ∀ (a : ℂ) z, a ≠ 0 → h (a • z) = h z` using `fun a z ha => isDegZero_normSq hb.1 c a z ha`. Express the relevant statement in the definitionally equal form `0 < ∫ z, h z ∂(symMeasure d)`. Rewrite using `[integral_symMeasure d hcont hdeg, smul_eq_mul]`. Establish `hA : 0 ≤ ∫ y, h (resPt d y) ∂d.dV` using `integral_nonneg fun y => hnn _`.

Establish `hB : 0 ≤ ∫ y, h (conjPt (resPt d y)) ∂d.dV` using `integral_nonneg fun y => hnn _`. Assume the negation of the conclusion as `hle`. Establish `hA0 : ∫ y, h (resPt d y) ∂d.dV = 0` using `by push Not at hle`. Use the polynomial consequences of the given equalities and inequalities. Use `d.vol.1` as an intermediate fact.

Establish `hc1` using `continuous_degZero_resPt d hcont hdeg`. Establish `hi1 : Integrable (fun y => h (resPt d y)) d.dV` using `integrableOn_univ.1 (hc1.continuousOn.integrableOn_compact isCompact_univ)`. Establish `hae` using `(integral_eq_zero_iff_of_nonneg (fun y => hnn _) hi1).mp hA0`. Establish `hv : ∀ y, h (resPt d y) = 0`. Introduce `y₀`.

Assume the negation of the conclusion as `hy₀`. Establish `hO : IsOpen {y | h (resPt d y) ≠ 0}` using `isOpen_ne_fun hc1 continuous_const`. Establish `hpos` using `dV_pos_of_isOpen d hO ⟨y₀, hy₀⟩`. Conclude with `hpos.ne' (ae_iff.mp hae)`. Use `set F : (Ix κ → ℂ) → ℂ := fun z => ∑ i, c i * secFun (b i) z with hF`.

Establish `hFv : ∀ y, F (resPt d y) = 0`. Introduce `y`. Establish `h1` using `hv y`. Establish `hw : 0 < wgt d.m n (resPt d y)` using `inv_pos.mpr (pow_pos (d.m.pos _ (resPt_mem_pts d y).1) _)`. Establish `h2 : ‖F (resPt d y)‖ ^ 2 = 0`.

Break down `mul_eq_zero.mp h1 with h' | h'` into its components or cases. Conclude with `h'`. Conclude with `absurd h' hw.ne'`. Conclude with `norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)`. Establish `hFpts : ∀ z ∈ pts (coordIdeal ℤ d.x), z ∉ mcPts (ι` using `GlobalTheory κ) d.J → F z = 0 := by`.

Introduce `z hz hzJ`. Take `⟨y, hy⟩` from `d.R.surj z (mem_mcPts_of_pts hz) hzJ`. Take `⟨a, ha, he⟩` from `sameOrbit_eq_smul hy`. Establish `h1 : ∑ i, c i * secFun (b i) (a • z) = 0`. Use `hFv y` as an intermediate fact.

Express the relevant statement in the definitionally equal form `∑ i, c i * secFun (b i) (d.R.lift y y) = 0 at this`. Rewrite `this` using `[he]`. Then use the resulting hypothesis. Rewrite `h1` using `[sum_secFun_smul hb.1 c a z]`. Conclude with `(mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ ha)`. Establish `hX : Nonempty d.R.X`.

Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[not_nonempty_iff]`. Establish `h1 : d.dV Set.univ = 1` using `measure_univ`. Rewrite `h1` using `[Set.univ_eq_empty_iff.mpr hne, measure_empty]`. Conclude with `zero_ne_one h1`.

Take `⟨y₀⟩` from `hX`. Establish `hF0 : F 0 = 0`. Establish `h1` using `sum_secFun_smul hb.1 c 0 (resPt d y₀)`. Rewrite `h1` using `[zero_smul]`. Express the relevant statement in the definitionally equal form `F 0 = _ at h1`.

Establish `h2` using `hFv y₀`. Express the relevant statement in the definitionally equal form `∑ i, c i * secFun (b i) (resPt d y₀) = 0 at h2`. Rewrite using `[h1, h2, mul_zero]`. Take `⟨g, N, hgJ, -, hgx⟩` from `exists_form_J d`. Use `set b' : Fin r → MvPolynomial (Ix κ) ℚ := fun k => b k * map (Int.castRingHom ℚ) g with hb'`.

Establish `hli : LinearIndependent ℚ fun k => aeval d.x (b' k)`. Establish `hs` using `linIndep_rat_of_isSecBasis hb`. Rewrite `hs`, the goal using `[linearIndependent_iff']`. Introduce `s w hsum i hi`. Use `hs s w ?_ i hi` and prove the remaining obligations.

Establish `h1 : (∑ i ∈ s, w i • aeval d.x (b i)) * aeval d.x g = 0`. Rewrite using `[Finset.sum_mul, ← hsum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc]`. Simplify using `only [hb', map_mul, aeval_map_intQ]`.

Conclude with `(mul_eq_zero.mp h1).resolve_right hgx`. Use `hc (coeff_eq_zero_of_vanish hli fun z hz => ?_)` and prove the remaining obligations. Establish `hsum : ∑ k, c k * secFun (b' k) z = F z * eval z (map (Int.castRingHom ℂ) g)`. Rewrite using `[hF, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [hb', secFun, map_mul]`. Rewrite using `[show (map (algebraMap ℚ ℂ)) ((map (Int.castRingHom ℚ)) g) = map (Int.castRingHom ℂ) g by`. Rewrite using `[MvPolynomial.map_map]`. Use `congr 1`. Apply the tactic sequence `try exact RingHom.ext_int _ _]`.

Apply the tactic sequence `try ring`. Rewrite using `[hsum]`. Distinguish the cases in `hz0 : z = 0`. Rewrite using `[hz0, hF0, zero_mul]`. Establish `hzp : z ∈ pts (coordIdeal ℤ d.x)` using `⟨hz0, hz⟩`.

Distinguish the cases in `hzJ : z ∈ mcPts (ι := GlobalTheory κ) d.J`. Rewrite using `[hzJ.2 g hgJ, mul_zero]`. Rewrite using `[hFpts z hzp hzJ, zero_mul]`.
-/
theorem posDef_gram (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis d.x n b) : (bGram (symMeasure d) (fun k => secFun (b k)) (wgt d.m n)).PosDef := by
  classical
  have hint := integrable_gram d hb.1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (bGram_isHermitian _ _ _) fun c hc => ?_
  rw [dot_bGram _ _ _ hint c, Complex.zero_lt_real]
  set h : (Ix κ → ℂ) → ℝ := fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt d.m n z with hh
  have hnn : ∀ z, 0 ≤ h z := fun z =>
    mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg z) _))
  have hcont : ContinuousOn h {0}ᶜ := continuousOn_normSq d.smooth b c
  have hdeg : ∀ (a : ℂ) z, a ≠ 0 → h (a • z) = h z := fun a z ha => isDegZero_normSq hb.1 c a z ha
  change 0 < ∫ z, h z ∂(symMeasure d)
  rw [integral_symMeasure d hcont hdeg, smul_eq_mul]
  have hA : 0 ≤ ∫ y, h (resPt d y) ∂d.dV := integral_nonneg fun y => hnn _
  have hB : 0 ≤ ∫ y, h (conjPt (resPt d y)) ∂d.dV := integral_nonneg fun y => hnn _
  by_contra hle
  have hA0 : ∫ y, h (resPt d y) ∂d.dV = 0 := by
    push Not at hle
    nlinarith

  have := d.vol.1
  have hc1 := continuous_degZero_resPt d hcont hdeg
  have hi1 : Integrable (fun y => h (resPt d y)) d.dV :=
    integrableOn_univ.1 (hc1.continuousOn.integrableOn_compact isCompact_univ)
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => hnn _) hi1).mp hA0
  have hv : ∀ y, h (resPt d y) = 0 := by
    intro y₀
    by_contra hy₀
    have hO : IsOpen {y | h (resPt d y) ≠ 0} := isOpen_ne_fun hc1 continuous_const
    have hpos := dV_pos_of_isOpen d hO ⟨y₀, hy₀⟩
    exact hpos.ne' (ae_iff.mp hae)
  set F : (Ix κ → ℂ) → ℂ := fun z => ∑ i, c i * secFun (b i) z with hF
  have hFv : ∀ y, F (resPt d y) = 0 := by
    intro y
    have h1 := hv y
    have hw : 0 < wgt d.m n (resPt d y) := inv_pos.mpr (pow_pos (d.m.pos _ (resPt_mem_pts d y).1) _)
    have h2 : ‖F (resPt d y)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h' | h'
      · exact h'
      · exact absurd h' hw.ne'
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)

  have hFpts : ∀ z ∈ pts (coordIdeal ℤ d.x), z ∉ mcPts (ι := GlobalTheory κ) d.J → F z = 0 := by
    intro z hz hzJ
    obtain ⟨y, hy⟩ := d.R.surj z (mem_mcPts_of_pts hz) hzJ
    obtain ⟨a, ha, he⟩ := sameOrbit_eq_smul hy
    have h1 : ∑ i, c i * secFun (b i) (a • z) = 0 := by
      have := hFv y
      change ∑ i, c i * secFun (b i) (d.R.lift y y) = 0 at this
      rwa [he] at this
    rw [sum_secFun_smul hb.1 c a z] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ ha)
  have hX : Nonempty d.R.X := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 : d.dV Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr hne, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨y₀⟩ := hX
  have hF0 : F 0 = 0 := by
    have h1 := sum_secFun_smul hb.1 c 0 (resPt d y₀)
    rw [zero_smul] at h1
    change F 0 = _ at h1
    have h2 := hFv y₀
    change ∑ i, c i * secFun (b i) (resPt d y₀) = 0 at h2
    rw [h1, h2, mul_zero]

  obtain ⟨g, N, hgJ, -, hgx⟩ := exists_form_J d
  set b' : Fin r → MvPolynomial (Ix κ) ℚ := fun k => b k * map (Int.castRingHom ℚ) g with hb'
  have hli : LinearIndependent ℚ fun k => aeval d.x (b' k) := by
    have hs := linIndep_rat_of_isSecBasis hb
    rw [linearIndependent_iff'] at hs ⊢
    intro s w hsum i hi
    refine hs s w ?_ i hi
    have h1 : (∑ i ∈ s, w i • aeval d.x (b i)) * aeval d.x g = 0 := by
      rw [Finset.sum_mul, ← hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_mul_assoc]
      simp only [hb', map_mul, aeval_map_intQ]
    exact (mul_eq_zero.mp h1).resolve_right hgx
  refine hc (coeff_eq_zero_of_vanish hli fun z hz => ?_)
  have hsum : ∑ k, c k * secFun (b' k) z = F z * eval z (map (Int.castRingHom ℂ) g) := by
    rw [hF, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hb', secFun, map_mul]
    rw [show (map (algebraMap ℚ ℂ)) ((map (Int.castRingHom ℚ)) g) = map (Int.castRingHom ℂ) g by
      rw [MvPolynomial.map_map]; congr 1; try exact RingHom.ext_int _ _]
    try ring
  rw [hsum]
  by_cases hz0 : z = 0
  · rw [hz0, hF0, zero_mul]
  · have hzp : z ∈ pts (coordIdeal ℤ d.x) := ⟨hz0, hz⟩
    by_cases hzJ : z ∈ mcPts (ι := GlobalTheory κ) d.J
    · rw [hzJ.2 g hgJ, mul_zero]
    · rw [hFpts z hzp hzJ, zero_mul]

/- English proof (translation)
Take `⟨C, hC⟩` from `hR D Ω κ d`. Use `⟨2 * C ^ 2, fun n r b hn hb c z hz => ?_⟩` and prove the remaining obligations. Use `set f : MvPolynomial (Ix κ) ℂ := ∑ k, MvPolynomial.C (c k) * map (algebraMap ℚ ℂ) (b k) with hf`. Establish `hfh : f.IsHomogeneous n`. Use `MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_` and prove the remaining obligations.

Take `⟨g, hg, hgb⟩` from `hb.1 k`. Rewrite using `[hgb, MvPolynomial.map_map]`. Conclude with `(hg.map _).C_mul _`. Use `set h : (Ix κ → ℂ) → ℝ := fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt d.m n z with hh`. Establish `hnn : ∀ z, 0 ≤ h z` using `fun z => mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg z) _))`.

Establish `hcont : ContinuousOn h {0}ᶜ` using `continuousOn_normSq d.smooth b c`. Establish `hdeg : ∀ (a : ℂ) z, a ≠ 0 → h (a • z) = h z` using `fun a z ha => isDegZero_normSq hb.1 c a z ha`. Establish `hevf : ∀ w, eval w f = ∑ i, c i * secFun (b i) w`. Introduce `w`. Simplify using `[hf, secFun, map_sum]`.

Establish `hpt : ∀ w : Ix κ → ℂ, w ≠ 0 → ptNorm d.m (RingHom.id ℂ) n f w ^ 2 = h w`. Introduce `w hw`. Establish `hρ : 0 < d.m.ρ w` using `d.m.pos w hw`. Rewrite using `[ptNorm, MvPolynomial.map_id, hevf]`. Simplify using `only [hh, wgt]`.

Rewrite using `[div_pow, ← pow_mul, mul_comm n 2, div_eq_mul_inv]`. Establish `hL : resolutionVolumeL2Complex d n f ^ 2 ≤ 2 * bNormSq (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c`. Establish `hI : 0 ≤ ∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV` using `integral_nonneg fun y => sq_nonneg _`. Rewrite using `[resolutionVolumeL2Complex, Real.sq_sqrt hI]`. Establish `he : (fun y => ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) = fun y => h (resPt d y)`.

Use function extensionality and compare the values at `y`. Conclude with `hpt _ (resPt_mem_pts d y).1`. Establish `hbn : bNormSq (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c = ∫ z, h z ∂(symMeasure d)` using `rfl`. Rewrite using `[he, hbn, integral_symMeasure d hcont hdeg, smul_eq_mul]`. Establish `hB : 0 ≤ ∫ y, h (conjPt (resPt d y)) ∂d.dV` using `integral_nonneg fun y => hnn _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `hC n hn f hfh z hz`. Establish `h0 : 0 ≤ ptNorm d.m (RingHom.id ℂ) n f z` using `div_nonneg (norm_nonneg _) (pow_nonneg (d.m.nonneg z) _)`. Establish `h2` using `pow_le_pow_left₀ h0 h1 2`. Rewrite `h2` using `[hpt z hz.1]`.

Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `hpow : ((n : ℝ) ^ ((D : ℝ) / 2)) ^ 2 = (n : ℝ) ^ D`. Rewrite using `[← Real.rpow_mul_natCast hn0, show (D : ℝ) / 2 * ((2 : ℕ) : ℝ) = (D : ℝ) by push_cast; ring, Real.rpow_natCast]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sup_le_gram (hR : ResolutionSupBound.Statement) (d : HSMDatum D Ω κ) :
    ∃ K : ℝ, ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), 1 ≤ n → IsSecBasis d.x n b →
      ∀ (c : Fin r → ℂ), ∀ z ∈ pts (coordIdeal ℤ d.x),
        ‖∑ k, c k * secFun (b k) z‖ ^ 2 * wgt d.m n z ≤
          K * (n : ℝ) ^ D * bNormSq (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c := by
  classical
  obtain ⟨C, hC⟩ := hR D Ω κ d
  refine ⟨2 * C ^ 2, fun n r b hn hb c z hz => ?_⟩
  set f : MvPolynomial (Ix κ) ℂ := ∑ k, MvPolynomial.C (c k) * map (algebraMap ℚ ℂ) (b k) with hf
  have hfh : f.IsHomogeneous n := by
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
    obtain ⟨g, hg, hgb⟩ := hb.1 k
    rw [hgb, MvPolynomial.map_map]
    exact (hg.map _).C_mul _
  set h : (Ix κ → ℂ) → ℝ := fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt d.m n z with hh
  have hnn : ∀ z, 0 ≤ h z := fun z =>
    mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg z) _))
  have hcont : ContinuousOn h {0}ᶜ := continuousOn_normSq d.smooth b c
  have hdeg : ∀ (a : ℂ) z, a ≠ 0 → h (a • z) = h z := fun a z ha => isDegZero_normSq hb.1 c a z ha
  have hevf : ∀ w, eval w f = ∑ i, c i * secFun (b i) w := by
    intro w
    simp [hf, secFun, map_sum]
  have hpt : ∀ w : Ix κ → ℂ, w ≠ 0 → ptNorm d.m (RingHom.id ℂ) n f w ^ 2 = h w := by
    intro w hw
    have hρ : 0 < d.m.ρ w := d.m.pos w hw
    rw [ptNorm, MvPolynomial.map_id, hevf]
    simp only [hh, wgt]
    rw [div_pow, ← pow_mul, mul_comm n 2, div_eq_mul_inv]

  have hL : resolutionVolumeL2Complex d n f ^ 2 ≤ 2 * bNormSq (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c := by
    have hI : 0 ≤ ∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV :=
      integral_nonneg fun y => sq_nonneg _
    rw [resolutionVolumeL2Complex, Real.sq_sqrt hI]
    have he : (fun y => ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) = fun y => h (resPt d y) := by
      funext y
      exact hpt _ (resPt_mem_pts d y).1
    have hbn : bNormSq (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c = ∫ z, h z ∂(symMeasure d) := rfl
    rw [he, hbn, integral_symMeasure d hcont hdeg, smul_eq_mul]
    have hB : 0 ≤ ∫ y, h (conjPt (resPt d y)) ∂d.dV := integral_nonneg fun y => hnn _
    linarith
  have h1 := hC n hn f hfh z hz
  have h0 : 0 ≤ ptNorm d.m (RingHom.id ℂ) n f z :=
    div_nonneg (norm_nonneg _) (pow_nonneg (d.m.nonneg z) _)
  have h2 := pow_le_pow_left₀ h0 h1 2
  rw [hpt z hz.1] at h2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpow : ((n : ℝ) ^ ((D : ℝ) / 2)) ^ 2 = (n : ℝ) ^ D := by
    rw [← Real.rpow_mul_natCast hn0, show (D : ℝ) / 2 * ((2 : ℕ) : ℝ) = (D : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  calc h z ≤ (C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f) ^ 2 := h2
    _ = C ^ 2 * (n : ℝ) ^ D * resolutionVolumeL2Complex d n f ^ 2 := by rw [mul_pow, mul_pow, hpow]
    _ ≤ C ^ 2 * (n : ℝ) ^ D * (2 * bNormSq (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by ring

/- English proof (translation)
Simplify using `only [pairVal, secFun, wgt, map_mul, Complex.conj_conj, Complex.conj_ofReal, div_eq_mul_inv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pairVal_eq_conj (m : ConeMetric ℂ (Ix κ)) (n : ℕ) (b b' : MvPolynomial (Ix κ) ℚ) (z : Ix κ → ℂ) :
    pairVal m n b b' z = starRingEnd ℂ (starRingEnd ℂ (secFun b z) * secFun b' z * (wgt m n z : ℂ)) := by
  simp only [pairVal, secFun, wgt, map_mul, Complex.conj_conj, Complex.conj_ofReal, div_eq_mul_inv]
  push_cast
  ring

/- English proof (translation)
Establish `hG : bGram (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) = Complex.ofRealHom.mapMatrix (resGram d n b)`. Use extensionality with `k l`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe]`. Establish `hreal` using `conj_bGram d.conjInv (map_conjPt_symMeasure d) n b k l`. Rewrite using `[← Complex.conj_eq_iff_re.mp hreal]`.

Use `congr 1`. Simplify using `only [bGram, Matrix.of_apply, resGram]`. Rewrite using `[integral_symMeasure d (continuousOn_gramFun d.smooth n (b k) (b l)) (fun c z hc => gramFun_smul (hb k) (hb l) c z hc)]`. Simplify using `only [pairVal_eq_conj]`. Rewrite using `[integral_conj, integral_conj, Complex.conj_re, Complex.conj_re, Complex.real_smul, Complex.re_ofReal_mul, Complex.add_re]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hG, ← RingHom.map_det, Complex.ofRealHom_eq_coe, Complex.ofReal_re]`.
-/
theorem det_resGram (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f) :
    (resGram d n b).det = (bGram (symMeasure d) (fun k => secFun (b k)) (wgt d.m n)).det.re := by
  have hG : bGram (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) =
      Complex.ofRealHom.mapMatrix (resGram d n b) := by
    ext k l
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe]
    have hreal := conj_bGram d.conjInv (map_conjPt_symMeasure d) n b k l
    rw [← Complex.conj_eq_iff_re.mp hreal]
    congr 1
    simp only [bGram, Matrix.of_apply, resGram]
    rw [integral_symMeasure d (continuousOn_gramFun d.smooth n (b k) (b l))
      (fun c z hc => gramFun_smul (hb k) (hb l) c z hc)]
    simp only [pairVal_eq_conj]
    rw [integral_conj, integral_conj, Complex.conj_re, Complex.conj_re, Complex.real_smul,
      Complex.re_ofReal_mul, Complex.add_re]
    ring
  rw [hG, ← RingHom.map_det, Complex.ofRealHom_eq_coe, Complex.ofReal_re]

/- English proof (translation)
Unfold `resChi`. Rewrite using `[dif_pos h, det_resGram d h.choose_spec.1]`.
-/
theorem resChi_eq (d : HSMDatum D Ω κ) (n : ℕ)
    (h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2) :
    resChi d n = -(1 / 2) * Real.log
      (bGram (symMeasure d) (fun k => secFun (h.choose.2 k)) (wgt d.m n)).det.re := by
  unfold resChi
  rw [dif_pos h, det_resGram d h.choose_spec.1]

end

end ResSym

end GroundTheory.Heights₂.Heights.HilbertSamuel
