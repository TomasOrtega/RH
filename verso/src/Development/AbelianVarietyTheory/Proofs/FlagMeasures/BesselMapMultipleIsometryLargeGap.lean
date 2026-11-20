import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableEmbeddingLmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapExistsFunctionalStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.GapCoefficientDerivativeBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MomentPieriNumericsOfSizeHyps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstantsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapsProportionalDiscreteSeriesLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFiniteBesselPeriodNeZeroGapStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselSchurGap

/- English proof (translation)
Introduce `hy k r ε μG hμ`. Establish `hHC : HCFdegG` using `hy.2.2.2.2.2.2`. Distinguish the cases in `hQ : ∃ Q, PI.UpqRep.IsCayleyU k r ε Q`. Use `swap`. Use `⟨1, one_pos, fun mu R hR => absurd ?_ hQ⟩` and prove the remaining obligations.

Take `⟨Q, hQ, -⟩` from `hR.2`. Conclude with `⟨Q, hQ⟩`. Take `⟨c, hc, hF⟩` from `hHC k r ε hQ`. Take `⟨Q, hQ⟩` from `hQ`. Establish `hP : IsUnit Q.det` using `(Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1`.

Establish `hH : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r` using `hQ.1.2`. Take `⟨a, ha0, hat, ha⟩` from `GlobalTheory.BesselDegree.haar_eq_smul hP hH μG hμ`. Establish `hapos : 0 < a.toReal` using `ENNReal.toReal_pos ha0 hat`. Establish `hme : MeasurableEmbedding (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q)` using `(Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) Formalism.REAL.isClosedEmbeddingMatrix hP).measurableEmbedding`. Use `⟨c / a.toReal, div_pos hc hapos, fun mu R hR => ?_⟩` and prove the remaining obligations.

Establish `hDS` using `(GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R (GlobalTheory.isDS_of_isDG hR) Q hQ`. Take `⟨hd, hS⟩` from `hF mu R.H _ hR.gap hR.hc hDS`. Establish `hd' : 0 < c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu`. Rewrite using `[div_mul_eq_mul_div]`. Conclude with `div_pos hd hapos`.

Establish `key : ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧ ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c / a.toReal * Formalism.Q …`. Introduce `v w v' w'`. Take `⟨h1, h2⟩` from `hS v w v' w'`. Rewrite using `[ha]`. Prove the components needed by the constructor for the conclusion.

Use `Integrable.smul_measure ?_ hat` and prove the remaining obligations. Rewrite using `[hme.integrable_map_iff]`. Conclude with `h1`. Rewrite using `[integral_smul_measure, hme.integral_map]`. Establish `h3 : ∫ g, ⟪w, R.σ (Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q g)) v⟫_ℂ * star ⟪w', R.σ (Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q g)) v'⟫_ℂ ∂(Formalism.REAL.muG ε) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterm …` using `h2`.

Rewrite using `[h3, div_mul_eq_mul_div, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨fun w hw => Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq hd' key hw, key⟩`.
-/
theorem schur_fdeg_gap : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)),
    PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → ∃ c : ℝ, 0 < c ∧ ∀ (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r),
    R.IsDG ε mu → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = c * Formalism.QuantumDeterminants.fdegHC mu) ∧
    ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG =
        ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
  intro hy k r ε μG hμ
  have hHC : HCFdegG := hy.2.2.2.2.2.2
  by_cases hQ : ∃ Q, PI.UpqRep.IsCayleyU k r ε Q
  swap
  · refine ⟨1, one_pos, fun mu R hR => absurd ?_ hQ⟩
    obtain ⟨Q, hQ, -⟩ := hR.2
    exact ⟨Q, hQ⟩
  obtain ⟨c, hc, hF⟩ := hHC k r ε hQ
  obtain ⟨Q, hQ⟩ := hQ
  have hP : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hH : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  obtain ⟨a, ha0, hat, ha⟩ := GlobalTheory.BesselDegree.haar_eq_smul hP hH μG hμ
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hme : MeasurableEmbedding (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q) :=
    (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_closedEmbedding (ε := ε) Formalism.REAL.isClosedEmbeddingMatrix hP).measurableEmbedding
  refine ⟨c / a.toReal, div_pos hc hapos, fun mu R hR => ?_⟩
  have hDS := (GlobalTheory.CayleyChoice.cayley_exists_and_any k r).2 ε mu R (GlobalTheory.isDS_of_isDG hR) Q hQ
  obtain ⟨hd, hS⟩ := hF mu R.H _ hR.gap hR.hc hDS
  have hd' : 0 < c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu := by
    rw [div_mul_eq_mul_div]; exact div_pos hd hapos
  have key : ∀ v w v' w' : R.H, Integrable (fun x : Formalism.QuantumDeterminants.Mt k r =>
      ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, R.σ (Matrix.of x) v⟫_ℂ * star ⟪w', R.σ (Matrix.of x) v'⟫_ℂ ∂μG =
        ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c / a.toReal * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := by
    intro v w v' w'
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [ha]
    constructor
    · refine Integrable.smul_measure ?_ hat
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, R.σ (Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q g)) v⟫_ℂ *
          star ⟪w', R.σ (Matrix.of (Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi ε Q g)) v'⟫_ℂ
          ∂(Formalism.REAL.muG ε) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((c * Formalism.QuantumDeterminants.fdegHC mu : ℝ) : ℂ) := h2
      rw [h3, div_mul_eq_mul_div, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  exact ⟨fun w hw => Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq hd' key hw, key⟩

/- English proof (translation)
Establish `hDG : R.IsDG ε mu` using `⟨hDS.1, hDS.2, h, hgap, hok⟩`. Take `⟨t, htG, htN, htz, -⟩` from `GlobalTheory.TorusScale.exists_torus_scale k r c hc`. Take `⟨-, htW, htψ⟩` from `htz z hS.1`. Take `⟨hS', hR⟩` from `GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne hH k r Wp z π u c μW μN μG νq t htG htN htW htψ hS`. Take `⟨hmul, hone, hinn, hsm, hTK, -, hKT, -, hcont⟩` from `GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r ε mu R hDS`.

Establish `hU : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) R.σ`. Use `⟨⟨?_, ?_⟩, fun g hg v => ?_, hcont⟩` and prove the remaining obligations. Use extensionality with `v`. Simplify using `using hone v`. Introduce `a ha b hb`.

Use extensionality with `v`. Simplify using `using hmul a ha b hb v`. Use `hinn g hg v v` as an intermediate fact. Rewrite `this` using `[inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]`. Establish `h2 : ‖R.σ g v‖ ^ 2 = ‖v‖ ^ 2` using `by exact_mod_cast this`.

Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2`. Establish `hB'` using `((hR R hU).1 B).1 hB`. Take `⟨htu, htinv, -⟩` from `PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r t htG`. Establish `hdet : IsUnit t.det` using `(Matrix.isUnit_iff_isUnit_det t).mp htu`. Establish `hae : ∀ {μN νq : Measure (Mt k r)}, SideG k r z π u μW μN μG νq → ∀ᵐ x ∂νq, Matrix.of x ∈ UH (Hpk k r)` using `fun hS => by`.

Take `⟨-, -, -, -, hW, hN, hG, hq⟩` from `hS`. Take `⟨hS0, hS1⟩` from `Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN`. Conclude with `Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hS0 hS1 hq`. Establish `hmove : ∀ v, PI.BesselPeriodGGP.l2SG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) (fun g => B (R.σ t (R.σ g v))) = PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v))` using `fun v => by`. Unfold `PI.BesselPeriodGGP.l2SG`.

Rewrite using `[(GlobalTheory.BesselSchur.measurableEmbedding_lmul hdet).lintegral_map]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae hS] with x hx`. Establish `e : R.σ t (R.σ (t⁻¹ * Matrix.of x) v) = R.σ (Matrix.of x) v`. Rewrite using `[← hmul t htG _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul htinv hx), ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]`.

Conclude with `congrArg (fun y => ((‖B y‖₊ : ℝ≥0∞)) ^ 2) e`. Take `⟨l, hl⟩` from `Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r ε mu h R Wp z π u _ _ _ _ hDG hgap hok hS'`. Take `⟨v₁, hv₁, hlv⟩` from `GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r ε mu h R Wp z π u _ _ _ _ _ l w hDS hgap hok hS' hB' hw (by rw [hmove]; exact h0) (by rw [hmove]; exact h1) hl`. Take `⟨c₀, hc₀, hfd⟩` from `schur_fdeg_gap hH.1 k r ε μG hS.2.2.2.2.2.2.1`. Establish `hdd : 0 < c₀ * Formalism.QuantumDeterminants.fdegHC mu` using `mul_pos hc₀ (GlobalTheory.BesselSchur.fdegHC_pos hDS.1.1)`.

Establish `hv₁s : v₁ ∈ R.sm` using `hTK _ (hKT _ hv₁)`. Establish `hiso` using `Gp91.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH.1 k r ε mu h R Wp z π u _ _ _ _ l _ hDG hgap hok hS' hl (hfd mu R hDG).1 ⟨v₁, hv₁s, hlv⟩`. Take `⟨hb, hiso⟩` from `hiso`. Take `⟨a, ha⟩` from `GlobalTheory.T.besselMaps_proportional_discreteSeries_largeGap hH k r ε mu R Wp z π u _ _ _ _ _ _ hDG hS' hb ⟨v₁, hv₁s, smul_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hdd).ne') hlv⟩ hB'`. Use `⟨(‖a‖₊ : ℝ≥0∞) ^ 2, fun v hv => ?_⟩` and prove the remaining obligations.

Establish `e : ((‖v‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2)`. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]`. Both sides reduce to the same expression. Rewrite using `[← hmove, e, ← hiso v hv]`. Unfold `PI.BesselPeriodGGP.l2SG`.

Rewrite using `[← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae hS'] with x hx`. Rewrite using `[ha _ (hsm _ hx v hv), nnnorm_smul, ENNReal.coe_mul, mul_pow]`.
-/
theorem exists_mass_eq (hH : GlobalTheory.GapIn.Hyp) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ}
    {μW μN μG νq : Measure (Mt k r)} {B : R.H → Wp} {w : R.H} (hc : c ≠ 0) (hDS : R.IsDS ε mu)
    (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hS : SideG k r z π u μW μN μG νq)
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B) (hw : R.KFin w)
    (h0 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ 0)
    (h1 : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) ≠ ⊤) :
    ∃ a : ℝ≥0∞, ∀ v ∈ R.sm, PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) = a * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have hDG : R.IsDG ε mu := ⟨hDS.1, hDS.2, h, hgap, hok⟩
  obtain ⟨t, htG, htN, htz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, htW, htψ⟩ := htz z hS.1
  obtain ⟨hS', hR⟩ := GlobalTheory.T.isBesselMap_conj_iff_and_besselFn_eq_rankOne hH k r Wp z π u c μW μN μG νq t htG htN htW htψ hS
  obtain ⟨hmul, hone, hinn, hsm, hTK, -, hKT, -, hcont⟩ :=
    GlobalTheory.rep_basic_of_isDS hH.1.1.2.2.1 k r ε mu R hDS
  have hU : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) R.σ := by
    refine ⟨⟨?_, ?_⟩, fun g hg v => ?_, hcont⟩
    · ext v; simpa using hone v
    · intro a ha b hb; ext v; simpa using hmul a ha b hb v
    · have := hinn g hg v v
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
      have h2 : ‖R.σ g v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast this
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  have hB' := ((hR R hU).1 B).1 hB
  obtain ⟨htu, htinv, -⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r t htG
  have hdet : IsUnit t.det := (Matrix.isUnit_iff_isUnit_det t).mp htu
  have hae : ∀ {μN νq : Measure (Mt k r)}, SideG k r z π u μW μN μG νq →
      ∀ᵐ x ∂νq, Matrix.of x ∈ UH (Hpk k r) := fun hS => by
    obtain ⟨-, -, -, -, hW, hN, hG, hq⟩ := hS
    obtain ⟨hS0, hS1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    exact Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hS0 hS1 hq
  have hmove : ∀ v, PI.BesselPeriodGGP.l2SG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j)
      (fun g => B (R.σ t (R.σ g v))) = PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g v)) := fun v => by
    unfold PI.BesselPeriodGGP.l2SG
    rw [(GlobalTheory.BesselSchur.measurableEmbedding_lmul hdet).lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [hae hS] with x hx
    have e : R.σ t (R.σ (t⁻¹ * Matrix.of x) v) = R.σ (Matrix.of x) v := by
      rw [← hmul t htG _ (Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul htinv hx), ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet,
        Matrix.one_mul]
    exact congrArg (fun y => ((‖B y‖₊ : ℝ≥0∞)) ^ 2) e
  obtain ⟨l, hl⟩ := Gp91.GlobalTheory.T.bessel_gap_exists_functional hH.1 k r ε mu h R Wp z π u _ _ _ _ hDG hgap hok hS'
  obtain ⟨v₁, hv₁, hlv⟩ := GlobalTheory.T.exists_kFinite_besselPeriod_ne_zero_gap hH k r ε mu h R Wp z π u _ _ _ _ _ l w hDS hgap hok hS' hB' hw
    (by rw [hmove]; exact h0) (by rw [hmove]; exact h1) hl
  obtain ⟨c₀, hc₀, hfd⟩ := schur_fdeg_gap hH.1 k r ε μG hS.2.2.2.2.2.2.1
  have hdd : 0 < c₀ * Formalism.QuantumDeterminants.fdegHC mu := mul_pos hc₀ (GlobalTheory.BesselSchur.fdegHC_pos hDS.1.1)
  have hv₁s : v₁ ∈ R.sm := hTK _ (hKT _ hv₁)
  have hiso := Gp91.GlobalTheory.T.isIsoB_sqrt_fdeg_smul_of_gap hH.1 k r ε mu h R Wp z π u _ _ _ _ l _ hDG hgap hok hS' hl
    (hfd mu R hDG).1 ⟨v₁, hv₁s, hlv⟩
  obtain ⟨hb, hiso⟩ := hiso
  obtain ⟨a, ha⟩ := GlobalTheory.T.besselMaps_proportional_discreteSeries_largeGap hH k r ε mu R Wp z π u _ _ _ _ _ _ hDG hS' hb
    ⟨v₁, hv₁s, smul_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hdd).ne') hlv⟩ hB'
  refine ⟨(‖a‖₊ : ℝ≥0∞) ^ 2, fun v hv => ?_⟩
  have e : ((‖v‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]; rfl
  rw [← hmove, e, ← hiso v hv]
  unfold PI.BesselPeriodGGP.l2SG
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  refine lintegral_congr_ae ?_
  filter_upwards [hae hS'] with x hx
  rw [ha _ (hsm _ hx v hv), nnnorm_smul, ENNReal.coe_mul, mul_pow]

/- English proof (translation)
Introduce `hH D large₂ C' Cl Cg cb Cu cT CT C0 hCl hθ _ hZ τ w w' θ W hW A hA hT v hv`. Establish `hθ0` using `hθ τ w w' θ W hW`. Use `FiniteDimensional.complete ℂ W.Wp` as an intermediate fact. Establish `hU : ∀ i : Fin D.R.k, uOne D w τ (i.val + 1) = uS D w τ i` using `fun i => by`. Unfold `uOne`.

Rewrite using `[dif_pos ⟨by omega, i.isLt⟩]`. Both sides reduce to the same expression. Take `⟨hnum, -, heps⟩` from `GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w _ hU`. Take `⟨-, -, -, -, -, -, -, -, -, -, hgap, hok, -, hh, -⟩` from `hnum`. Rewrite `hgap` using `[heps]`.

Establish `hgap' : GapAtLeast (epsSH D.R) (lamD D τ) ((D.R.r : ℝ) ^ 19 / 4)` using `fun a b hab => le_trans (by have : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity linarith) (hgap a b hab)`. Establish `hv1 : 1 ≤ D.host.v` using `hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hvpos : 0 < D.host.v` using `by linarith`. Take `⟨c1, -, z1, -, t1, -, hG, w1, -, -, -, hN, q1, -⟩` from `hW`. Take `⟨hpar, hds, b1, -, hsm, hv0, ⟨P, hP, hlow⟩, hc, l1, -, -⟩` from `hA`.

Establish `hTz : 0 < Tz D.R.k D.R.rS W.z` using `by rw [t1]; exact hT`. Establish `hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN`. Rewrite using `[hN]`. Conclude with `GlobalTheory.haarLie_isHaarOn_Nset _ _ _ (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_lt_top`. Establish `hS : SideG D.R.k D.R.rS W.z W.π (uOne D w τ) W.μW W.μN W.μG W.νS` using `⟨z1, hTz, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z1 hTz c1 hU, w1, hNH, hG, q1⟩`.

Establish `hka : 0 < D.host.ka` using `div_pos Real.pi_pos hvpos`. Establish `hg0 : (0 : ℝ) < D.host.g 0` using `by exact_mod_cast (D.host.g_prime 0).pos`. Establish `hg1 : (0 : ℝ) < D.host.g 1` using `by exact_mod_cast (D.host.g_prime 1).pos`. Establish `hcne : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (by positivity)`. Establish `hKF : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin A.v0`.

Take `⟨S, ⟨hfd, hst⟩, hwS⟩` from `PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup (Formalism.REAL.Kset (epsSH D.R)) (fun g => A.σ (P⁻¹ * g * P)) (F := {S | IsKTypeOf (epsSH D.R) (fun g => A.σ (P⁻¹ * g * P)) (lowK (epsSH D.R) (lamD D τ)) S}) (fun S hS => ⟨hS.1, hS.2.1⟩) hlow`. Use `⟨S, hfd, hwS, fun g hg x hx => ?_⟩` and prove the remaining obligations. Take `⟨hK, hback⟩` from `PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hP hg`. Establish `h` using `hst _ hK x hx`. Simplify using `only at h`.

Rewrite `h` using `[hback]`. Then use the resulting hypothesis. Establish `hnt : Nontrivial W.Wp`. Take `⟨g, -, hnt, -⟩` from `c1`. Conclude with `hnt`. Establish `hrk : (0 : ℝ) < Module.finrank ℂ W.Wp` using `by exact_mod_cast Module.finrank_pos`.

Establish `l1' : PI.BesselPeriodGGP.l2SG W.νS (fun g => A.B (A.σ g A.v0)) = ENNReal.ofReal (A.cN * Module.finrank ℂ W.Wp)` using `l1`. Take `⟨a, ha⟩` from `exists_mass_eq hH (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) (B := A.B) (w := A.v0) hcne ⟨hpar, hds⟩ hgap' hok hS (GlobalTheory.BesselSchur.isBesselMapSm_of b1) hKF (by rw [l1']; exact (ENNReal.ofReal_pos.2 (mul_pos hc hrk)).ne') (by rw [l1']; exact ENNReal.ofReal_ne_top)`. Establish `e1 : l2SG W.νS (fun g => A.B (A.σ g v)) = a * (‖v‖₊ : ℝ≥0∞) ^ 2` using `ha v hv`. Establish `e2 : l2SG W.νS A.Φ = a * (‖A.v0‖₊ : ℝ≥0∞) ^ 2` using `ha A.v0 hsm`. Rewrite using `[e1, e2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bessel_schur : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), 1000 ≤ Cl →
    (∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → 0 < θ) → (∀ w, 0 < Tr D w) →
    BSch D large₂ C' Cl Cg cb Cu cT CT C0 := by
  intro hH D large₂ C' Cl Cg cb Cu cT CT C0 hCl hθ _ hZ τ w w' θ W hW A hA hT v hv
  have hθ0 := hθ τ w w' θ W hW
  have := FiniteDimensional.complete ℂ W.Wp
  have hU : ∀ i : Fin D.R.k, uOne D w τ (i.val + 1) = uS D w τ i := fun i => by
    unfold uOne
    rw [dif_pos ⟨by omega, i.isLt⟩]
    rfl
  obtain ⟨hnum, -, heps⟩ := GlobalTheory.SizeNum.num_of_size D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl τ w _ hU
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgap, hok, -, hh, -⟩ := hnum
  rw [heps] at hgap
  have hgap' : GapAtLeast (epsSH D.R) (lamD D τ) ((D.R.r : ℝ) ^ 19 / 4) := fun a b hab =>
    le_trans (by have : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
                 linarith) (hgap a b hab)
  have hv1 : 1 ≤ D.host.v := hZ.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hvpos : 0 < D.host.v := by linarith
  obtain ⟨c1, -, z1, -, t1, -, hG, w1, -, -, -, hN, q1, -⟩ := hW
  obtain ⟨hpar, hds, b1, -, hsm, hv0, ⟨P, hP, hlow⟩, hc, l1, -, -⟩ := hA
  have hTz : 0 < Tz D.R.k D.R.rS W.z := by rw [t1]; exact hT
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hN]
    exact GlobalTheory.haarLie_isHaarOn_Nset _ _ _ (ENNReal.ofReal_pos.2 (by positivity)) ENNReal.ofReal_lt_top
  have hS : SideG D.R.k D.R.rS W.z W.π (uOne D w τ) W.μW W.μN W.μG W.νS :=
    ⟨z1, hTz, ⟨_, c1⟩, GlobalTheory.ThA.capParam_of_isHCTypeW _ _ _ _ _ _ _ z1 hTz c1 hU, w1, hNH, hG, q1⟩
  have hka : 0 < D.host.ka := div_pos Real.pi_pos hvpos
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  have hcne : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (by positivity)
  have hKF : (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin A.v0 := by
    obtain ⟨S, ⟨hfd, hst⟩, hwS⟩ := PI.UnitaryGroupMassFormula.LowSmooth.exists_finStable_of_mem_sSup (Formalism.REAL.Kset (epsSH D.R))
      (fun g => A.σ (P⁻¹ * g * P))
      (F := {S | IsKTypeOf (epsSH D.R) (fun g => A.σ (P⁻¹ * g * P)) (lowK (epsSH D.R) (lamD D τ)) S})
      (fun S hS => ⟨hS.1, hS.2.1⟩) hlow
    refine ⟨S, hfd, hwS, fun g hg x hx => ?_⟩
    obtain ⟨hK, hback⟩ := PI.UnitaryGroupMassFormula.LowSmooth.conj_mem_Kset hP hg
    have h := hst _ hK x hx
    simp only at h
    rwa [hback] at h
  have hnt : Nontrivial W.Wp := by
    obtain ⟨g, -, hnt, -⟩ := c1
    exact hnt
  have hrk : (0 : ℝ) < Module.finrank ℂ W.Wp := by exact_mod_cast Module.finrank_pos
  have l1' : PI.BesselPeriodGGP.l2SG W.νS (fun g => A.B (A.σ g A.v0)) =
      ENNReal.ofReal (A.cN * Module.finrank ℂ W.Wp) := l1
  obtain ⟨a, ha⟩ := exists_mass_eq hH (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) (B := A.B) (w := A.v0) hcne ⟨hpar, hds⟩
    hgap' hok hS (GlobalTheory.BesselSchur.isBesselMapSm_of b1) hKF
    (by rw [l1']; exact (ENNReal.ofReal_pos.2 (mul_pos hc hrk)).ne') (by rw [l1']; exact ENNReal.ofReal_ne_top)
  have e1 : l2SG W.νS (fun g => A.B (A.σ g v)) = a * (‖v‖₊ : ℝ≥0∞) ^ 2 := ha v hv
  have e2 : l2SG W.νS A.Φ = a * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 := ha A.v0 hsm
  rw [e1, e2]
  ring

end GlobalTheory.BesselSchurGap
