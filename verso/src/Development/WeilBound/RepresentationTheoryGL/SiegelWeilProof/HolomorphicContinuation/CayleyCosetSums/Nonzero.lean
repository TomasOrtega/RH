import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IsCompactKSet

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def psi (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (u : GR n) : ℂ :=
  ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u) ∂μK

/- English proof (translation)
Establish `hF : Continuous (Function.uncurry fun (u : GR n) (k : KR n) => (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u))` using `by show Continuous fun p : GR n × KR n => (F0 m 0 e (p.2 : GR n))⁻¹ * F0 m 0 e ((p.2 : GR n) * p.1)`. Use `Continuous.mul ?_ ?_` and prove the remaining obligations. Conclude with `((Vac.continuous_weight_factor detU1 m 0 e).comp (continuous_subtype_val.comp continuous_snd)).inv₀ fun p => Vac.spherical_section_ne_zero detU1 m 0 e _`. Conclude with `(Vac.continuous_weight_factor detU1 m 0 e).comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)`. Use `continuous_parametric_integral_of_continuous (μ := μK) hF isCompact_univ` as an intermediate fact.

Establish `e : psi m e μK = fun u => ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u) ∂μK` using `rfl`. Rewrite using `[e]`. Simplify `this` using `[Measure.restrict_univ]`.
-/
theorem psi_continuous (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [IsFiniteMeasure μK] : Continuous (psi m e μK) := by
  have hF : Continuous (Function.uncurry fun (u : GR n) (k : KR n) =>
      (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u)) := by
    show Continuous fun p : GR n × KR n => (F0 m 0 e (p.2 : GR n))⁻¹ * F0 m 0 e ((p.2 : GR n) * p.1)
    refine Continuous.mul ?_ ?_
    · exact ((Vac.continuous_weight_factor detU1 m 0 e).comp (continuous_subtype_val.comp continuous_snd)).inv₀
        fun p => Vac.spherical_section_ne_zero detU1 m 0 e _
    · exact (Vac.continuous_weight_factor detU1 m 0 e).comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)
  have := continuous_parametric_integral_of_continuous (μ := μK) hF isCompact_univ
  have e : psi m e μK = fun u => ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e ((k : GR n) * u) ∂μK := rfl
  rw [e]
  simpa [Measure.restrict_univ] using this

/- English proof (translation)
Unfold `psi`. Simplify using `only [mul_one]`. Establish `h : ∀ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e (k : GR n) = 1` using `fun k => inv_mul_cancel₀ (Vac.spherical_section_ne_zero detU1 _ _ _ _)`. Simplify using `only [h]`. Rewrite using `[integral_const]`.

Simplify using `[Measure.real]`.
-/
theorem psi_one (m : ℕ) (e : ℤ) (μK : Measure (KR n)) : psi m e μK 1 = (μK Set.univ).toReal := by
  unfold psi
  simp only [mul_one]
  have h : ∀ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * F0 m 0 e (k : GR n) = 1 := fun k =>
    inv_mul_cancel₀ (Vac.spherical_section_ne_zero detU1 _ _ _ _)
  simp only [h]
  rw [integral_const]
  simp [Measure.real]

/- English proof (translation)
Establish `hk : (mR (k : GR n))ᴴ * mR (k : GR n) = 1` using `(show InK (mR (k : GR n)) from k.2).2`. Establish `h1 : mR (k : GR n) * mR ((k : GR n)⁻¹) = 1`. Rewrite using `[← mR_mul, mul_inv_cancel]`. Simplify using `[mR]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h1, Matrix.mul_one]`. Use `_ = mR ((k : GR n)⁻¹) := by rw [← Matrix.mul_assoc, hk, Matrix.one_mul]`.
-/
private theorem mR_conjTranspose_eq_mR_inv_of_KR (k : KR n) : (mR (k : GR n))ᴴ = mR ((k : GR n)⁻¹) := by
  have hk : (mR (k : GR n))ᴴ * mR (k : GR n) = 1 := (show InK (mR (k : GR n)) from k.2).2
  have h1 : mR (k : GR n) * mR ((k : GR n)⁻¹) = 1 := by
    rw [← mR_mul, mul_inv_cancel]
    simp [mR]
  calc (mR (k : GR n))ᴴ = (mR (k : GR n))ᴴ * (mR (k : GR n) * mR ((k : GR n)⁻¹)) := by
        rw [h1, Matrix.mul_one]
    _ = mR ((k : GR n)⁻¹) := by rw [← Matrix.mul_assoc, hk, Matrix.one_mul]

/- English proof (translation)
Establish `hF` using `Vac.continuous_weight_factor (n := n) detU1 m 0 e`. Establish `hFne : ∀ g, F0 (n` using `n) m 0 e g ≠ 0 := fun g => Vac.spherical_section_ne_zero detU1 m 0 e g`. Establish `hCc : IsCompact (mR ⁻¹' (tsupport β))` using `isCompact_preimage_mR hβs.isCompact`. Establish `hk : Continuous (fun p : GR n × KR n => ((p.2 : GR n)))` using `continuous_subtype_val.comp continuous_snd`. Set `A : GR n × KR n → ℂ` to `fun p => F0 m 0 e p.1 * ((F0 m 0 e (p.2 : GR n))⁻¹ * (β (mR ((p.2 : GR n)⁻¹ * p.1)) : ℂ))`.

Set `B : GR n × KR n → ℂ` to `fun p => (β (mR p.1) : ℂ) * ((F0 m 0 e (p.2 : GR n))⁻¹ * F0 m 0 e ((p.2 : GR n) * p.1))`. Establish `hAc : Continuous A`. Use `(hF.comp continuous_fst).mul (((hF.comp hk).inv₀ fun p => hFne _).mul ?_)` and prove the remaining obligations. Conclude with `Complex.continuous_ofReal.comp (hβc.comp (continuous_mR.comp (hk.inv.mul continuous_fst)))`. Establish `hBc : Continuous B`.

Use `(Complex.continuous_ofReal.comp (hβc.comp (continuous_mR.comp continuous_fst))).mul (((hF.comp hk).inv₀ fun p => hFne _).mul (hF.comp (hk.mul continuous_fst)))` and prove the remaining obligations. Establish `hAs : HasCompactSupport A`. Use `HasCompactSupport.intro ((((isCompact_univ (X := KR n)).prod hCc).image ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)).prod (isCompact_univ (X := KR n))) ?_` and prove the remaining obligations. Introduce `p hp`. Establish `hz : β (mR ((p.2 : GR n)⁻¹ * p.1)) = 0`.

Assume the negation of the conclusion as `hne`. Apply `hp` to reduce the goal to its premises. Use `⟨⟨⟨p.2, (p.2 : GR n)⁻¹ * p.1⟩, ⟨Set.mem_univ _, subset_tsupport _ hne⟩, ?_⟩, Set.mem_univ _⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[A, hz]`.

Establish `hBs : HasCompactSupport B`. Use `HasCompactSupport.intro (hCc.prod (isCompact_univ (X := KR n))) ?_` and prove the remaining obligations. Introduce `p hp`. Establish `hz : β (mR p.1) = 0`. Assume the negation of the conclusion as `hne`.

Conclude with `hp ⟨subset_tsupport _ hne, Set.mem_univ _⟩`. Simplify using `[B, hz]`. Establish `hAi : Integrable A (ν.prod μK)` using `hAc.integrable_of_hasCompactSupport hAs`. Establish `hBi : Integrable B (ν.prod μK)` using `hBc.integrable_of_hasCompactSupport hBs`. Combine the equalities or inequalities in the displayed calculation.

Unfold `cw`. Use `congr 1`. Use extensionality with `u`. Unfold `phi tw`. Rewrite using `[Complex.cpow_zero, mul_one, ← integral_const_mul]`.

Use `congr 1`. Use extensionality with `k`. Simplify using `only [A]`. Rewrite using `[mR_conjTranspose_eq_mR_inv_of_KR, ← mR_mul]`. Use `_ = ∫ k, ∫ u, A (u, k) ∂ν ∂μK := integral_integral_swap hAi`.

Use `_ = ∫ k, ∫ v, A ((k : GR n) * v, k) ∂ν ∂μK := by`. Use `congr 1`. Use extensionality with `k`. Conclude with `(integral_mul_left_eq_self (fun u => A (u, k)) (k : GR n)).symm`. Use `_ = ∫ k, ∫ v, B (v, k) ∂ν ∂μK := by`.

Use `congr 1`. Use extensionality with `k`. Use `congr 1`. Use extensionality with `v`. Simplify using `only [A, B]`.

Rewrite using `[inv_mul_cancel_left]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ∫ v, ∫ k, B (v, k) ∂μK ∂ν := (integral_integral_swap hBi).symm`. Use `_ = ∫ u : GR n, (β (mR u) : ℂ) * psi m e μK u ∂ν := by`. Use `congr 1`.

Use extensionality with `v`. Simplify using `only [B, psi]`. Rewrite using `[integral_const_mul]`.
-/
theorem cw_zero (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure]
    {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β) :
    cw m e ν μK β 0 = ∫ u : GR n, (β (mR u) : ℂ) * psi m e μK u ∂ν := by
  have hF := Vac.continuous_weight_factor (n := n) detU1 m 0 e
  have hFne : ∀ g, F0 (n := n) m 0 e g ≠ 0 := fun g => Vac.spherical_section_ne_zero detU1 m 0 e g
  have hCc : IsCompact (mR ⁻¹' (tsupport β)) := isCompact_preimage_mR hβs.isCompact
  have hk : Continuous (fun p : GR n × KR n => ((p.2 : GR n))) :=
    continuous_subtype_val.comp continuous_snd
  let A : GR n × KR n → ℂ := fun p =>
    F0 m 0 e p.1 * ((F0 m 0 e (p.2 : GR n))⁻¹ * (β (mR ((p.2 : GR n)⁻¹ * p.1)) : ℂ))
  let B : GR n × KR n → ℂ := fun p =>
    (β (mR p.1) : ℂ) * ((F0 m 0 e (p.2 : GR n))⁻¹ * F0 m 0 e ((p.2 : GR n) * p.1))
  have hAc : Continuous A := by
    refine (hF.comp continuous_fst).mul (((hF.comp hk).inv₀ fun p => hFne _).mul ?_)
    exact Complex.continuous_ofReal.comp
      (hβc.comp (continuous_mR.comp (hk.inv.mul continuous_fst)))
  have hBc : Continuous B := by
    refine (Complex.continuous_ofReal.comp (hβc.comp (continuous_mR.comp continuous_fst))).mul
      (((hF.comp hk).inv₀ fun p => hFne _).mul (hF.comp (hk.mul continuous_fst)))
  have hAs : HasCompactSupport A := by
    refine HasCompactSupport.intro
      ((((isCompact_univ (X := KR n)).prod hCc).image
        ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)).prod
        (isCompact_univ (X := KR n))) ?_
    intro p hp
    have hz : β (mR ((p.2 : GR n)⁻¹ * p.1)) = 0 := by
      by_contra hne
      apply hp
      refine ⟨⟨⟨p.2, (p.2 : GR n)⁻¹ * p.1⟩, ⟨Set.mem_univ _, subset_tsupport _ hne⟩, ?_⟩, Set.mem_univ _⟩
      simp
    simp [A, hz]
  have hBs : HasCompactSupport B := by
    refine HasCompactSupport.intro (hCc.prod (isCompact_univ (X := KR n))) ?_
    intro p hp
    have hz : β (mR p.1) = 0 := by
      by_contra hne
      exact hp ⟨subset_tsupport _ hne, Set.mem_univ _⟩
    simp [B, hz]
  have hAi : Integrable A (ν.prod μK) := hAc.integrable_of_hasCompactSupport hAs
  have hBi : Integrable B (ν.prod μK) := hBc.integrable_of_hasCompactSupport hBs
  calc cw m e ν μK β 0 = ∫ u, ∫ k, A (u, k) ∂μK ∂ν := by
        unfold cw
        congr 1
        ext u
        unfold phi tw
        rw [Complex.cpow_zero, mul_one, ← integral_const_mul]
        congr 1
        ext k
        simp only [A]
        rw [mR_conjTranspose_eq_mR_inv_of_KR, ← mR_mul]
    _ = ∫ k, ∫ u, A (u, k) ∂ν ∂μK := integral_integral_swap hAi
    _ = ∫ k, ∫ v, A ((k : GR n) * v, k) ∂ν ∂μK := by
        congr 1
        ext k
        exact (integral_mul_left_eq_self (fun u => A (u, k)) (k : GR n)).symm
    _ = ∫ k, ∫ v, B (v, k) ∂ν ∂μK := by
        congr 1
        ext k
        congr 1
        ext v
        simp only [A, B]
        rw [inv_mul_cancel_left]
        ring
    _ = ∫ v, ∫ k, B (v, k) ∂μK ∂ν := (integral_integral_swap hBi).symm
    _ = ∫ u : GR n, (β (mR u) : ℂ) * psi m e μK u ∂ν := by
        congr 1
        ext v
        simp only [B, psi]
        rw [integral_const_mul]

/- English proof (translation)
Establish `hpc : Continuous (psi m e μK)` using `psi_continuous m e μK`. Establish `h1 : mR (1 : GR n) = 1` using `by simp [mR]`. Establish `hp1 : 0 < (psi m e μK 1).re`. Rewrite using `[psi_one, Complex.ofReal_re]`. Conclude with `ENNReal.toReal_pos (isOpen_univ.measure_ne_zero μK Set.univ_nonempty) (measure_ne_top _ _)`.

Establish `hO : IsOpen {u : GR n | 0 < (psi m e μK u).re}` using `isOpen_lt continuous_const (Complex.continuous_re.comp hpc)`. Take `⟨O, hOo, hOeq⟩` from `isClosedEmbedding_mR.isInducing.isOpen_iff.mp hO`. Establish `h1O : (1 : M2 n) ∈ O`. Establish `h : (1 : GR n) ∈ mR ⁻¹' O`. Rewrite using `[hOeq]`.

Conclude with `hp1`. Simplify `h` using `[h1]`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.mp hOo 1 h1O`. Set `b : ContDiffBump (1 : M2 n)` to `⟨r / 2, r, by positivity, by linarith⟩`. Use `⟨⇑b, b.contDiff, b.hasCompactSupport, ?_⟩` and prove the remaining obligations.

Rewrite using `[cw_zero m e ν μK b.continuous b.hasCompactSupport]`. Use `set g : GR n → ℂ := fun u => (b (mR u) : ℂ) * psi m e μK u with hg`. Establish `hgs : HasCompactSupport g`. Establish `h` using `(b.hasCompactSupport.comp_isClosedEmbedding isClosedEmbedding_mR).comp_left (g := Complex.ofReal) Complex.ofReal_zero`. Conclude with `h.mul_right`.

Establish `hgc : Continuous g` using `(Complex.continuous_ofReal.comp (b.continuous.comp continuous_mR)).mul hpc`. Establish `hre : ∀ u, (g u).re = b (mR u) * (psi m e μK u).re` using `fun u => Complex.re_ofReal_mul _ _`. Establish `hpos : 0 < ∫ u, (g u).re ∂ν`. Use `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (Complex.continuous_re.comp hgc) (hgs.comp_left Complex.zero_re) ?_ ?_` and prove the remaining obligations. Introduce `u show 0 ≤ (g u).re`.

Rewrite using `[hre]`. Distinguish the cases in `hu : b (mR u) = 0`. Simplify using `[hu]`. Establish `hmem : mR u ∈ Metric.ball (1 : M2 n) r`. Establish `hs : mR u ∈ Function.support b` using `hu`.

Rewrite `hs` using `[b.support_eq]`. Then use the resulting hypothesis. Establish `hu' : u ∈ mR ⁻¹' O` using `hball hmem`. Rewrite `hu'` using `[hOeq]`. Conclude with `mul_nonneg b.nonneg (le_of_lt hu')`. Use `show (g 1).re ≠ 0`.

Rewrite using `[hre, h1, b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]`. Conclude with `ne_of_gt hp1`. Introduce `h`. Establish `hz : (∫ u, g u ∂ν).re = 0`. Rewrite using `[h]`.

Simplify using the standard rewrite rules. Establish `hgi : Integrable g ν` using `hgc.integrable_of_hasCompactSupport hgs`. Establish `hint` using `integral_re hgi`. Simplify using `only [RCLike.re_to_complex] at hint`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_bump (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure] :
    ∃ β : M2 n → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ cw m e ν μK β 0 ≠ 0 := by
  have hpc : Continuous (psi m e μK) := psi_continuous m e μK
  have h1 : mR (1 : GR n) = 1 := by simp [mR]
  have hp1 : 0 < (psi m e μK 1).re := by
    rw [psi_one, Complex.ofReal_re]
    exact ENNReal.toReal_pos (isOpen_univ.measure_ne_zero μK Set.univ_nonempty) (measure_ne_top _ _)
  have hO : IsOpen {u : GR n | 0 < (psi m e μK u).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp hpc)
  obtain ⟨O, hOo, hOeq⟩ := isClosedEmbedding_mR.isInducing.isOpen_iff.mp hO
  have h1O : (1 : M2 n) ∈ O := by
    have h : (1 : GR n) ∈ mR ⁻¹' O := by
      rw [hOeq]
      exact hp1
    simpa [h1] using h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hOo 1 h1O
  let b : ContDiffBump (1 : M2 n) := ⟨r / 2, r, by positivity, by linarith⟩
  refine ⟨⇑b, b.contDiff, b.hasCompactSupport, ?_⟩
  rw [cw_zero m e ν μK b.continuous b.hasCompactSupport]
  set g : GR n → ℂ := fun u => (b (mR u) : ℂ) * psi m e μK u with hg
  have hgs : HasCompactSupport g := by
    have h := (b.hasCompactSupport.comp_isClosedEmbedding isClosedEmbedding_mR).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
    exact h.mul_right
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.comp (b.continuous.comp continuous_mR)).mul hpc
  have hre : ∀ u, (g u).re = b (mR u) * (psi m e μK u).re := fun u => Complex.re_ofReal_mul _ _
  have hpos : 0 < ∫ u, (g u).re ∂ν := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp hgc) (hgs.comp_left Complex.zero_re) ?_ ?_
    · intro u
      show 0 ≤ (g u).re
      rw [hre]
      by_cases hu : b (mR u) = 0
      · simp [hu]
      · have hmem : mR u ∈ Metric.ball (1 : M2 n) r := by
          have hs : mR u ∈ Function.support b := hu
          rwa [b.support_eq] at hs
        have hu' : u ∈ mR ⁻¹' O := hball hmem
        rw [hOeq] at hu'
        exact mul_nonneg b.nonneg (le_of_lt hu')
    · show (g 1).re ≠ 0
      rw [hre, h1, b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]
      exact ne_of_gt hp1
  intro h
  have hz : (∫ u, g u ∂ν).re = 0 := by
    rw [h]
    simp
  have hgi : Integrable g ν := hgc.integrable_of_hasCompactSupport hgs
  have hint := integral_re hgi
  simp only [RCLike.re_to_complex] at hint
  linarith

end PositivityTheory.Rg.Sw.HSt.Conv
