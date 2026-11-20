import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBesselMapRankOneFactorisationTranslateSpanStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelProjectorOnLineStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralHsNormSqMatrixCoeffLeFormalDegreeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqAmpJAndBesselEqDoubleIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNonzeroFixedOfSquareIntegrableBesselStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SchurNorm

/- English proof (translation)
Establish `h : hsInner (t • A) (t • A) = ((‖t‖ ^ 2 : ℝ) : ℂ) * hsInner A A`. Simplify using `only [hsInner, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite using `[hsNormSq, h, Complex.re_ofReal_mul, hsNormSq]`.
-/
theorem hsNormSq_smul {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℂ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = ‖t‖ ^ 2 * hsNormSq A := by
  have h : hsInner (t • A) (t • A) = ((‖t‖ ^ 2 : ℝ) : ℂ) * hsInner A A := by
    simp only [hsInner, Finset.mul_sum, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsNormSq, h, Complex.re_ofReal_mul, hsNormSq]

/- English proof (translation)
Unfold `ampJ`. Rewrite using `[Complex.ofReal_one, inv_one, one_smul, mul_smul, ← integral_smul (t * star t')]`. Use `congr 1`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [show ∀ᵐ x ∂μ, Matrix.of x ∈ GG k r from hμ.2.2.1] with x hx`.

Rewrite using `[h _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hγ hx), h' _ hx]`. Use extensionality with `η`. Simplify using `only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.smul_apply, inner_smul_left, smul_smul, Complex.star_def]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ampJ_of_smul {k r : ℕ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {μ : Measure (Mt k r)} (hμ : IsHaarOn (GG k r) μ)
    (c : ℝ) (t t' : ℂ) {Φ Ψ : Mat k r → Wp} {Φ' Ψ' : Mat k r → Wq} (h : ∀ g ∈ GG k r, Φ g = t • Ψ g)
    (h' : ∀ g ∈ GG k r, Φ' g = t' • Ψ' g) {γ : Mat k r} (hγ : γ ∈ GG k r) :
    ampJ μ c Φ Φ' γ = ((c : ℂ)⁻¹ * (t * star t')) • ampJ μ 1 Ψ Ψ' γ := by
  unfold ampJ
  rw [Complex.ofReal_one, inv_one, one_smul, mul_smul, ← integral_smul (t * star t')]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [show ∀ᵐ x ∂μ, Matrix.of x ∈ GG k r from hμ.2.2.1] with x hx
  rw [h _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hγ hx), h' _ hx]
  ext η
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.smul_apply,
    inner_smul_left, smul_smul, Complex.star_def]
  congr 1
  ring

/- English proof (translation)
Use `set w : H := ((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀ with hw`. Establish `hn : ((‖v₀‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hv`. Establish `hvw : v₀ = ((‖v₀‖ : ℝ) : ℂ) • w` using `by rw [hw, smul_smul, mul_inv_cancel₀ hn, one_smul]`. Take `⟨hStd, hsm⟩` from `hS`. Establish `hU : IsURepOn (GG k r) σ` using `hStd.2.1`.

Establish `hw1 : ‖w‖ = 1` using `hStd.2.2.2.1`. Establish `hw1' : ‖w‖₊ = 1` using `NNReal.eq hw1`. Establish `hG : IsHaarOn (GG k r) μG` using `hStd.2.2.2.2.1`. Establish `hd : 0 < d` using `hStd.2.2.2.2.2.1.1`. Take `⟨-, -, hle, hact, hinf⟩` from `GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hU`.

Establish `hgw : ∀ g ∈ GG k r, σ g w ∈ smoothVecs (k` using `k) (r := r) σ := (hact w hsm).1`. Use `haveI : Nontrivial Wp := hz.2.2`. Establish `hdim : (0 : ℝ) < Module.finrank ℂ Wp` using `by exact_mod_cast Module.finrank_pos`. Establish `hn0 : ((‖v₀‖₊ : ℝ≥0∞)) ^ 2 ≠ 0` using `pow_ne_zero _ (by simpa using hv)`. Establish `hnt : ((‖v₀‖₊ : ℝ≥0∞)) ^ 2 ≠ ⊤` using `ENNReal.pow_ne_top ENNReal.coe_ne_top`.

Establish `hLw : l2SG νS (fun g => B (σ g w)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀))`. Rewrite using `[h1 w hsm, hw1']`. Simplify using the standard rewrite rules. Establish `hnv : NonVan z (psiGen k r z c) σ π w μG νS`. Use `GlobalTheory.T.exists_nonzero_fixed_of_squareIntegrable_bessel k r σ w a d μG μS νS z c π B ⟨hStd, hsm⟩ hz.1 hq hB ?_ ?_ ?_` and prove the remaining obligations.

Introduce `h`. Rewrite `hLw` using `[h, zero_mul, h0]`. Conclude with `(ENNReal.ofReal_pos.2 (mul_pos hc hdim)).ne hLw`. Introduce `h`. Rewrite `hLw` using `[h, ENNReal.top_mul hn0, h0]`.

Conclude with `ENNReal.ofReal_ne_top hLw.symm`. Introduce `v hv'`. Use `(ENNReal.mul_left_inj hn0 hnt).1 ?_` and prove the remaining obligations. Rewrite using `[h1 v hv', ← hLw]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨l, hl⟩` from `GlobalTheory.T.exists_besselMap_rankOne_factorisation_translateSpan k r σ w a μG d z c π μS hStd hz.1 hsm hm νS hq hnv`. Use `⟨l, hl, ?_⟩` and prove the remaining obligations. Establish `hs : ∃ s : ℂ, ∀ x ∈ smoothVecs (k` using `k) (r := r) σ, B x = s • l x := by`. Take `⟨s, hs | hs⟩` from `hm B l hB hl.1`. Conclude with `⟨s, hs⟩`.

Take `⟨u, hu, hu0⟩` from `hl.2.1`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Conclude with `hu0 ((hs u ((hinf hsm).1 u (hle hu))).trans (zero_smul _ _))`. Conclude with `⟨s⁻¹, fun x hx => by rw [hs x hx, smul_smul, inv_mul_cancel₀ hs0, one_smul]⟩`.

Take `⟨s, hs⟩` from `hs`. Establish `key : ∀ g ∈ GG k r, B (σ g v₀) = (((‖v₀‖ : ℝ) : ℂ) * s) • l (σ g w)`. Introduce `g hg`. Establish `e : σ g v₀ = ((‖v₀‖ : ℝ) : ℂ) • σ g w` using `by rw [← map_smul, ← hvw]`. Rewrite using `[e, hB.2.1 _ _ (hgw g hg), hs _ (hgw g hg), smul_smul]`.

Use `⟨_, ?_, key⟩` and prove the remaining obligations. Generalize the expression as in `((‖v₀‖ : ℝ) : ℂ) * s = t at key`. Establish `hone : (1 : Mat k r) ∈ GG k r` using `by simp [UH]`. Establish `hwD : w ∈ DD σ w`. Use `mem_DD σ w hone` as an intermediate fact.

Rewrite `this` using `[hU.1.1]`. Then use the resulting hypothesis. Establish `hlw` using `(GlobalTheory.T.besselModel_projector_on_line k r σ w a μG d z c π μS hStd hz.1 νS hq l hl).1 w hwD`. Establish `hμS : IsHaarOn (Sset k r z) μS` using `hz.1.2.2.2.1`. Establish `hae` using `Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hμS.2.1 (measure_mono_null (by`. Introduce and unpack `x hx ⟨h, hh, m, hm', e⟩`.

Conclude with `hx (e ▸ Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hm'.1)) hμS.2.2.1) hq`. Establish `e : l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (‖t‖ ^ 2) * l2SG νS (fun x => l (σ x w))`. Unfold `l2SG`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hae] with x hx`. Rewrite using `[key _ hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`. Both sides reduce to the same expression. Rewrite `e` using `[h0, hlw, hw1, ← ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]`. Rewrite using `[e]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem exists_isEll_smul (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp]
    (σ : Mat k r → (H →L[ℂ] H)) (v₀ : H) (a d c₀ : ℝ) (μG μS νS : Measure (Mt k r))
    (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (B : H → Wp) (hv : v₀ ≠ 0)
    (hS : StdSm σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀) a μG d) (hz : SideIrr z π μS) (hq : IsQuotMeas μG μS νS)
    (hm : MultOne z (psiGen k r z c) σ π) (hB : IsBesselMapSm z (psiGen k r z c) σ π B) (hc : 0 < c₀)
    (h0 : l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wp))
    (h1 : ∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 =
      l2SG νS (fun g => B (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) :
    ∃ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀)) l ∧
      ∃ t : ℂ, ‖t‖ ^ 2 = c₀ * Module.finrank ℂ Wp * d ∧
        ∀ g ∈ GG k r, B (σ g v₀) = t • l (σ g (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀)) := by
  set w : H := ((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀ with hw
  have hn : ((‖v₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hv
  have hvw : v₀ = ((‖v₀‖ : ℝ) : ℂ) • w := by rw [hw, smul_smul, mul_inv_cancel₀ hn, one_smul]
  obtain ⟨hStd, hsm⟩ := hS
  have hU : IsURepOn (GG k r) σ := hStd.2.1
  have hw1 : ‖w‖ = 1 := hStd.2.2.2.1
  have hw1' : ‖w‖₊ = 1 := NNReal.eq hw1
  have hG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  obtain ⟨-, -, hle, hact, hinf⟩ := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hU
  have hgw : ∀ g ∈ GG k r, σ g w ∈ smoothVecs (k := k) (r := r) σ := (hact w hsm).1
  haveI : Nontrivial Wp := hz.2.2
  have hdim : (0 : ℝ) < Module.finrank ℂ Wp := by exact_mod_cast Module.finrank_pos
  have hn0 : ((‖v₀‖₊ : ℝ≥0∞)) ^ 2 ≠ 0 := pow_ne_zero _ (by simpa using hv)
  have hnt : ((‖v₀‖₊ : ℝ≥0∞)) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hLw : l2SG νS (fun g => B (σ g w)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀)) := by
    rw [h1 w hsm, hw1']; simp
  have hnv : NonVan z (psiGen k r z c) σ π w μG νS := by
    refine GlobalTheory.T.exists_nonzero_fixed_of_squareIntegrable_bessel k r σ w a d μG μS νS z c π B ⟨hStd, hsm⟩ hz.1 hq hB ?_ ?_ ?_
    · intro h
      rw [h, zero_mul, h0] at hLw
      exact (ENNReal.ofReal_pos.2 (mul_pos hc hdim)).ne hLw
    · intro h
      rw [h, ENNReal.top_mul hn0, h0] at hLw
      exact ENNReal.ofReal_ne_top hLw.symm
    · intro v hv'
      refine (ENNReal.mul_left_inj hn0 hnt).1 ?_
      rw [h1 v hv', ← hLw]; ring
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_besselMap_rankOne_factorisation_translateSpan k r σ w a μG d z c π μS hStd hz.1 hsm hm νS hq hnv
  refine ⟨l, hl, ?_⟩
  have hs : ∃ s : ℂ, ∀ x ∈ smoothVecs (k := k) (r := r) σ, B x = s • l x := by
    obtain ⟨s, hs | hs⟩ := hm B l hB hl.1
    · exact ⟨s, hs⟩
    · obtain ⟨u, hu, hu0⟩ := hl.2.1
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact hu0 ((hs u ((hinf hsm).1 u (hle hu))).trans (zero_smul _ _))
      exact ⟨s⁻¹, fun x hx => by rw [hs x hx, smul_smul, inv_mul_cancel₀ hs0, one_smul]⟩
  obtain ⟨s, hs⟩ := hs
  have key : ∀ g ∈ GG k r, B (σ g v₀) = (((‖v₀‖ : ℝ) : ℂ) * s) • l (σ g w) := by
    intro g hg
    have e : σ g v₀ = ((‖v₀‖ : ℝ) : ℂ) • σ g w := by rw [← map_smul, ← hvw]
    rw [e, hB.2.1 _ _ (hgw g hg), hs _ (hgw g hg), smul_smul]
  refine ⟨_, ?_, key⟩
  generalize ((‖v₀‖ : ℝ) : ℂ) * s = t at key
  have hone : (1 : Mat k r) ∈ GG k r := by simp [UH]
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hone
    rwa [hU.1.1] at this
  have hlw := (GlobalTheory.T.besselModel_projector_on_line k r σ w a μG d z c π μS hStd hz.1 νS hq l hl).1 w hwD
  have hμS : IsHaarOn (Sset k r z) μS := hz.1.2.2.2.1
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hμS.2.1 (measure_mono_null (by
    rintro x hx ⟨h, hh, m, hm', e⟩
    exact hx (e ▸ Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hh.1 hm'.1)) hμS.2.2.1) hq
  have e : l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (‖t‖ ^ 2) * l2SG νS (fun x => l (σ x w)) := by
    unfold l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [key _ hx, nnnorm_smul, ENNReal.coe_mul, mul_pow, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  rw [h0, hlw, hw1, ← ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at e
  rw [e]; field_simp

/- English proof (translation)
Introduce `k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ v₀ a d c₀ μG μS μS' νS νS' ν z z' c c' π π' B B' hv hS hz hz' hq hq' hm hm' hB hB' hc h0 h0' h1 h1' hν`. Take `⟨l, hl, t, ht, key⟩` from `exists_isEll_smul k r σ v₀ a d c₀ μG μS νS z c π B hv hS hz hq hm hB hc h0 h1`. Take `⟨l', hl', t', ht', key'⟩` from `exists_isEll_smul k r σ v₀ a d c₀ μG μS' νS' z' c' π' B' hv hS hz' hq' hm' hB' hc h0' h1'`. Use `set w : H := ((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀ with hw`. Establish `hG : IsHaarOn (GG k r) μG` using `hS.1.2.2.2.2.1`.

Establish `hd : 0 < d` using `hS.1.2.2.2.2.2.1.1`. Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `h5` using `GlobalTheory.T.lintegral_hsNormSq_matrixCoeff_le_formalDegree k r σ w a μG d z c π μS z' c' π' μS' hS.1 hz.1 hz'.1 ν hν l l' hl hl'`. Establish `hJ` using `(GlobalTheory.T.amplitude_eq_ampJ_and_bessel_eq_doubleIntegral k r (H := H) (Wp := Wp) (Wq := Wq)).1 μG (fun x => l (σ x w)) (fun x => l' (σ x w)) hG`. Establish `hD : (0 : ℝ) ≤ (Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq` using `by positivity`.

Rewrite using `[div_eq_mul_inv, ENNReal.ofReal_mul hD]`. Use `le_trans (le_of_eq ?_) (mul_le_mul_right h5 _)` and prove the remaining obligations. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [show ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z' from hν.2.1] with γ hγ`.

Rewrite using `[ampJ_of_smul hG c₀ t t' (Ψ := fun x => l (σ x w)) (Ψ' := fun x => l' (σ x w)) key key' hγ.1, ← hJ _ hγ.1, ← ENNReal.ofReal_mul hD, hsNormSq_smul, hsNormSq_smul]`. Use `congr 1`. Rewrite using `[norm_mul, norm_mul, norm_star, norm_inv, mul_pow, mul_pow, ht, ht', Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hd.le]`. Clear the denominators using the available nonvanishing facts.
-/
theorem lintegral_hsNormSq_ampJ_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (v₀ : H) (a d c₀ : ℝ) (μG μS μS' νS νS' ν : Measure (Mt k r)) (z z' : (Fin (2 * r + k + 1) → ℂ)) (c c' : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (B : H → Wp) (B' : H → Wq), v₀ ≠ 0 → StdSm σ (((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀) a μG d → SideIrr z π μS → SideIrr z' π' μS' → IsQuotMeas μG μS νS → IsQuotMeas μG μS' νS' → MultOne z (psiGen k r z c) σ π → MultOne z' (psiGen k r z' c') σ π' → IsBesselMapSm z (psiGen k r z c) σ π B → IsBesselMapSm z' (psiGen k r z' c') σ π' B' → 0 < c₀ → l2SG νS (fun g => B (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wp) → l2SG νS' (fun g => B' (σ g v₀)) = ENNReal.ofReal (c₀ * Module.finrank ℂ Wq) → (∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS (fun g => B (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → (∀ v ∈ smoothVecs σ, l2SG νS' (fun g => B' (σ g v)) * (‖v₀‖₊ : ℝ≥0∞) ^ 2 = l2SG νS' (fun g => B' (σ g v₀)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → IsDis (Greg k r z z') μG μS μS' ν → ∫⁻ γ, ENNReal.ofReal (hsNormSq (ampJ μG c₀ (fun g => B (σ g v₀)) (fun g => B' (σ g v₀)) (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal ((Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq / d) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ v₀ a d c₀ μG μS μS' νS νS' ν z z' c c' π π' B B' hv hS hz hz' hq hq'
    hm hm' hB hB' hc h0 h0' h1 h1' hν
  obtain ⟨l, hl, t, ht, key⟩ := exists_isEll_smul k r σ v₀ a d c₀ μG μS νS z c π B hv hS hz hq hm hB hc h0 h1
  obtain ⟨l', hl', t', ht', key'⟩ :=
    exists_isEll_smul k r σ v₀ a d c₀ μG μS' νS' z' c' π' B' hv hS hz' hq' hm' hB' hc h0' h1'
  set w : H := ((‖v₀‖ : ℝ) : ℂ)⁻¹ • v₀ with hw
  have hG : IsHaarOn (GG k r) μG := hS.1.2.2.2.2.1
  have hd : 0 < d := hS.1.2.2.2.2.2.1.1
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have h5 := GlobalTheory.T.lintegral_hsNormSq_matrixCoeff_le_formalDegree k r σ w a μG d z c π μS z' c' π' μS' hS.1 hz.1 hz'.1 ν hν l l' hl hl'
  have hJ := (GlobalTheory.T.amplitude_eq_ampJ_and_bessel_eq_doubleIntegral k r (H := H) (Wp := Wp) (Wq := Wq)).1 μG (fun x => l (σ x w)) (fun x => l' (σ x w)) hG
  have hD : (0 : ℝ) ≤ (Module.finrank ℂ Wp : ℝ) * Module.finrank ℂ Wq := by positivity
  rw [div_eq_mul_inv, ENNReal.ofReal_mul hD]
  refine le_trans (le_of_eq ?_) (mul_le_mul_right h5 _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [show ∀ᵐ γ ∂ν, Matrix.of γ ∈ Greg k r z z' from hν.2.1] with γ hγ
  rw [ampJ_of_smul hG c₀ t t' (Ψ := fun x => l (σ x w)) (Ψ' := fun x => l' (σ x w)) key key' hγ.1,
    ← hJ _ hγ.1, ← ENNReal.ofReal_mul hD, hsNormSq_smul, hsNormSq_smul]
  congr 1
  rw [norm_mul, norm_mul, norm_star, norm_inv, mul_pow, mul_pow, ht, ht', Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hc.le, Real.norm_of_nonneg hd.le]
  field_simp

end GlobalTheory.Amp.SchurNorm
