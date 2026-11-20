import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.XiExistsOfBesselXiIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNorm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCTx2

/- English proof (translation)
Establish `hc : ContinuousOn F (GV k r)` using `P.B7.jc_cont hF`. Establish `hJ : AEStronglyMeasurable (fun q => JF D F (gq D q)) (volume.restrict (Qset D))`. Establish `h0` using `P.B7.jc_aesm_J D hc (1, 1)`. Establish `e : (fun q => Jtau D (1, 1) F (gq D q)) = fun q => JF D F (gq D q)`. Use function extensionality and compare the values at `fun q => P.bessel_function_trivial_index k r Wp Wq D F (gq D q)`.

Rewrite `h0` using `[e]`. Then use the resulting hypothesis. Use `set f : (Fin r → ℂ) × ℂ → ℝ := fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖hsVec (JF D F (gq D q))‖ ^ 2 with hf`. Establish `hf0 : ∀ q, 0 ≤ f q` using `fun q => mul_nonneg (bcWeight_nonneg' _ _ q) (sq_nonneg _)`. Establish `hzero : ∀ q, q ∉ Qset D → f q = 0`. Introduce `q hq`.

Establish `hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0` using `P.BetaSesquilinearity.wt_eq_zero D hq`. Simplify using `[hf, hw]`. Establish `hfm : AEStronglyMeasurable f volume`. Establish `hind : Set.indicator (Qset D) f = f`. Use function extensionality and compare the values at `q`.

Distinguish the cases in `hq : q ∈ Qset D`. Simplify using `[hq]`. Simplify using `[hq, hzero q hq]`. Rewrite using `[← hind, aestronglyMeasurable_indicator_iff (P.BetaSesquilinearity.Qset_measurable D)]`. Establish `hw : Measurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q)` using `P.BetaSesquilinearity.wt_measurable D`.

Conclude with `hw.aestronglyMeasurable.mul ((P.BetaSesquilinearity.hsVec_cont.comp_aestronglyMeasurable hJ).norm.pow 2)`. Establish `hinner : ∀ q, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) * inner ℂ (hsVec (JF D F (gq D q))) (hsVec (JF D F (gq D q))) = ((f q : ℝ) : ℂ)`. Introduce `q`. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Simplify using `[hf]`.

Use `show (∫ p, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') p : ℝ) : ℂ) * inner ℂ (hsVec (JF D F (gq D p))) (hsVec (JF D F (gq D p)))) = (((∫⁻ p, ENNReal.ofReal (f p)).toReal : ℝ) : ℂ)`. Simplify using `only [hinner]`. Rewrite using `[integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm]`.
-/
theorem beta_self_eq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) {A : ℝ} (hF : InCC A 4 F) :
    beta D F F = (((B.normSq D F).toReal : ℝ) : ℂ) := by
  have hc : ContinuousOn F (GV k r) := P.B7.jc_cont hF
  have hJ : AEStronglyMeasurable (fun q => JF D F (gq D q)) (volume.restrict (Qset D)) := by
    have h0 := P.B7.jc_aesm_J D hc (1, 1)
    have e : (fun q => Jtau D (1, 1) F (gq D q)) = fun q => JF D F (gq D q) :=
      funext fun q => P.bessel_function_trivial_index k r Wp Wq D F (gq D q)
    rwa [e] at h0
  set f : (Fin r → ℂ) × ℂ → ℝ := fun q =>
    bcWeight k r (Tz k r D.z) (Tz k r D.z') q * ‖hsVec (JF D F (gq D q))‖ ^ 2 with hf
  have hf0 : ∀ q, 0 ≤ f q := fun q => mul_nonneg (bcWeight_nonneg' _ _ q) (sq_nonneg _)
  have hzero : ∀ q, q ∉ Qset D → f q = 0 := by
    intro q hq
    have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 := P.BetaSesquilinearity.wt_eq_zero D hq
    simp [hf, hw]
  have hfm : AEStronglyMeasurable f volume := by
    have hind : Set.indicator (Qset D) f = f := by
      funext q
      by_cases hq : q ∈ Qset D
      · simp [hq]
      · simp [hq, hzero q hq]
    rw [← hind, aestronglyMeasurable_indicator_iff (P.BetaSesquilinearity.Qset_measurable D)]
    have hw : Measurable (fun q => bcWeight k r (Tz k r D.z) (Tz k r D.z') q) := P.BetaSesquilinearity.wt_measurable D
    exact hw.aestronglyMeasurable.mul ((P.BetaSesquilinearity.hsVec_cont.comp_aestronglyMeasurable hJ).norm.pow 2)
  have hinner : ∀ q, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) *
      inner ℂ (hsVec (JF D F (gq D q))) (hsVec (JF D F (gq D q))) = ((f q : ℝ) : ℂ) := by
    intro q
    rw [inner_self_eq_norm_sq_to_K]
    simp [hf]
  show (∫ p, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') p : ℝ) : ℂ) *
      inner ℂ (hsVec (JF D F (gq D p))) (hsVec (JF D F (gq D p)))) =
    (((∫⁻ p, ENNReal.ofReal (f p)).toReal : ℝ) : ℂ)
  simp only [hinner]
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm]

end GlobalTheory.BesselNorm

namespace GlobalTheory.BesselNorm

/- English proof (translation)
Introduce `hX k r Wp _ _ _ _ Wq _ _ _ _ D`. Take `⟨c, hc0, -, hB1, hB2, -⟩` from `(P.lemma_b_from_xi hX).2 k r Wp Wq D (B.AB k r) le_rfl`. Use `⟨(c : ℝ), by exact_mod_cast hc0, fun A F hA hF => ?_⟩` and prove the remaining obligations. Establish `hF0 : B.InCC (B.AB k r) 5 F` using `P.BetaSesquilinearity.sInCC_mono hA le_rfl hF`. Take `⟨c0, hc0F⟩` from `id hF0`.

Take `⟨C, hC⟩` from `hB1`. Establish `h4` using `P.BetaSesquilinearity.CCle_mono_m (show 4 ≤ 5 by norm_num) hc0F`. Establish `hfin : B.normSq D F ≠ ⊤` using `(hC F F c0 c0 hF0 hF0 h4 h4).1`. Establish `hβ` using `hB2 F F hF0 hF0`. Establish `h1` using `beta_self_eq D F (P.BetaSesquilinearity.InCC_mono (show 4 ≤ 5 by norm_num) hF0)`.

Establish `hre : (B.normSq D F).toReal = (B.beta D F F).re`. Rewrite using `[h1, Complex.ofReal_re]`. Rewrite using `[← ENNReal.ofReal_toReal hfin, hre, hβ]`.
-/
theorem normSq_eq_betaInf_of_xi : B.XiExists → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 5 F → B.normSq D F = ENNReal.ofReal (c * B.betaInf D F F).re := by
  intro hX k r Wp _ _ _ _ Wq _ _ _ _ D
  obtain ⟨c, hc0, -, hB1, hB2, -⟩ := (P.lemma_b_from_xi hX).2 k r Wp Wq D (B.AB k r) le_rfl
  refine ⟨(c : ℝ), by exact_mod_cast hc0, fun A F hA hF => ?_⟩
  have hF0 : B.InCC (B.AB k r) 5 F := P.BetaSesquilinearity.sInCC_mono hA le_rfl hF
  obtain ⟨c0, hc0F⟩ := id hF0
  obtain ⟨C, hC⟩ := hB1
  have h4 := P.BetaSesquilinearity.CCle_mono_m (show 4 ≤ 5 by norm_num) hc0F
  have hfin : B.normSq D F ≠ ⊤ := (hC F F c0 c0 hF0 hF0 h4 h4).1
  have hβ := hB2 F F hF0 hF0
  have h1 := beta_self_eq D F (P.BetaSesquilinearity.InCC_mono (show 4 ≤ 5 by norm_num) hF0)
  have hre : (B.normSq D F).toReal = (B.beta D F F).re := by
    rw [h1, Complex.ofReal_re]
  rw [← ENNReal.ofReal_toReal hfin, hre, hβ]

/- English proof (translation)
The claim follows from `normSq_eq_betaInf_of_xi P.exists_auxiliary_xi`.
-/
theorem normSq_eq_betaInf : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)), B.AB k r ≤ A → B.InCC A 5 F → B.normSq D F = ENNReal.ofReal (c * B.betaInf D F F).re := normSq_eq_betaInf_of_xi P.exists_auxiliary_xi

end GlobalTheory.BesselNorm
