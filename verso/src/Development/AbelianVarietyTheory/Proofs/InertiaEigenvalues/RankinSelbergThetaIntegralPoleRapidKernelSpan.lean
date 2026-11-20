import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoResidueTermRankinSelbergInnerProductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCompInfGLProd
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.RSThetaLimR

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Rewrite using `[← GlobalTheory.JSW.rspan_eq_mspanR]`. Conclude with `GlobalTheory.JSW.rspan_le (fun φ hφ => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ) (fun F hF h => mul_right_mem_bddForms hF h) (fun F hF X _ ν _ k γ hk => GlobalTheory.JSW.kerInf_mem_bddForms hF hk)`.
-/
theorem mspanR_le_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) :
    GlobalTheory.JSW.mspanR π ≤ bddForms E a ω := by
  rw [← GlobalTheory.JSW.rspan_eq_mspanR]
  exact GlobalTheory.JSW.rspan_le (fun φ hφ => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ)
    (fun F hF h => mul_right_mem_bddForms hF h) (fun F hF X _ ν _ k γ hk => GlobalTheory.JSW.kerInf_mem_bddForms hF hk)

/- English proof (translation)
The claim follows from `hφ.elim (fun h => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ h) (fun h => mspanR_le_bddForms hω hπ h)`.
-/
theorem mem_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {φ : Sm E a}
    (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) : φ.1 ∈ bddForms E a ω :=
  hφ.elim (fun h => mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ h)
    (fun h => mspanR_le_bddForms hω hπ h)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `φ.1 ∈ GlobalTheory.JSW.mspanR π`. Break down `hφ with h | h` into its components or cases. Rewrite using `[← GlobalTheory.JSW.rspan_eq_mspanR]`. Conclude with `GlobalTheory.JSW.mem_rspan h`. Conclude with `h`.
-/
theorem mem_rsm {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) :
    φ ∈ GlobalTheory.RSThetaLowM.rsm π := by
  change φ.1 ∈ GlobalTheory.JSW.mspanR π
  rcases hφ with h | h
  · rw [← GlobalTheory.JSW.rspan_eq_mspanR]; exact GlobalTheory.JSW.mem_rspan h
  · exact h

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Establish `hv : (finiteMeasurePi E (latt a J)).toReal ≠ 0` using `ENNReal.toReal_ne_zero.2 ⟨((isOpen_latt J).measure_pos _ ⟨0, fun i => (idealFiniteAdeles J).zero_mem⟩).ne', (isCompact_latt J).measure_lt_top.ne⟩`. Use `mul_ne_zero (Complex.ofReal_ne_zero.2 hv) ?_` and prove the remaining obligations. Establish `e : (fun u => Φ u) = fun u => (((Φ u).re : ℝ) : ℂ)` using `funext fun u => Complex.ext rfl (by simp [(hpos u).2])`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, Φ x ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne (funext h)`. Establish `hre : (Φ x).re ≠ 0` using `fun h0 => hx (Complex.ext h0 (hpos x).2)`. Establish `hpos' : 0 < ∫ u, (Φ u).re ∂(volume : Measure (Fin a → Cinf E))` using `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (Complex.continuous_re.comp hΦ1.continuous) (hΦ2.comp_left Complex.zero_re) (fun u => (hpos u).1) hre`. Rewrite using `[e, integral_complex_ofReal, infMeasure, integral_smul_measure]`.

Use `Complex.ofReal_ne_zero.2 (smul_ne_zero ?_ hpos'.ne')` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem resConst_ne_zero {Φ : (Fin a → Cinf E) → ℂ} (hΦ1 : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦ2 : HasCompactSupport Φ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (hpos : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (hne : Φ ≠ 0) :
    ((finiteMeasurePi E (latt a J)).toReal : ℂ) * ∫ x, Φ x ∂infMeasure E a ≠ 0 := by
  have hv : (finiteMeasurePi E (latt a J)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
    ⟨((isOpen_latt J).measure_pos _ ⟨0, fun i => (idealFiniteAdeles J).zero_mem⟩).ne',
      (isCompact_latt J).measure_lt_top.ne⟩
  refine mul_ne_zero (Complex.ofReal_ne_zero.2 hv) ?_
  have e : (fun u => Φ u) = fun u => (((Φ u).re : ℝ) : ℂ) := funext fun u => Complex.ext rfl (by simp [(hpos u).2])
  obtain ⟨x, hx⟩ : ∃ x, Φ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hre : (Φ x).re ≠ 0 := fun h0 => hx (Complex.ext h0 (hpos x).2)
  have hpos' : 0 < ∫ u, (Φ u).re ∂(volume : Measure (Fin a → Cinf E)) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (Complex.continuous_re.comp hΦ1.continuous)
      (hΦ2.comp_left Complex.zero_re) (fun u => (hpos u).1) hre
  rw [e, integral_complex_ofReal, infMeasure, integral_smul_measure]
  refine Complex.ofReal_ne_zero.2 (smul_ne_zero ?_ hpos'.ne')
  simp

/- English proof (translation)
Establish `hΦ : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ` using `⟨hΦ1, hΦ2, hΦ3⟩`. Use `haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL`. Use `haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ`. Use `haveI : IsFiniteMeasure (μ.restrict 𝓕') := ⟨by rw [Measure.restrict_apply_univ, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]; exact measure_lt_top _ _⟩`. Use `haveI : SFinite (infMeasure E a) := by unfold infMeasure; infer_instance`.

Take `⟨C, hC⟩` from `hb.2.2.2`. Take `⟨D, hD⟩` from `hb'.2.2.2`. Establish `hΦi : Integrable Φ (infMeasure E a)`. Unfold `infMeasure`. Conclude with `(hΦ1.continuous.integrable_of_hasCompactSupport hΦ2).smul_measure (by simp)`.

Establish `hi : Integrable (fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2) ((μ.restrict 𝓕').prod (infMeasure E a))`. Use `((integrable_const (C * D)).mul_prod hΦi.norm).mono' (continuous_rsInf hb.1 hb'.1 hΦ1.continuous hΦ3).aestronglyMeasurable (.of_forall fun p => ?_)` and prove the remaining obligations. Simplify using `only [rsInf, norm_mul, Complex.norm_conj]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)`. Establish `hx : ∀ x, ∫ g in 𝓕', rsInf ℓ φ.1 φ'.1 Φ g x ∂μ = (∫ g in 𝓕', φ.1 g * conj (φ'.1 g) ∂μ) * Φ x`.

Introduce `x`. Simplify using `only [rsInf]`. Rewrite using `[integral_mul_const]`. Use `congr 1`. Conclude with `GlobalTheory.RSResidue.setIntegral_mul_right h𝓕 (f := fun g => φ.1 g * conj (φ'.1 g)) (GlobalTheory.Petersson.leftInv_mul_conj hω hb hb') _`.

Simplify using `only [GlobalTheory.RSResidue.rsHat_zero J η φ φ' hΦ]`. Rewrite using `[integral_mul_const, integral_integral_swap hi]`. Simplify using `only [hx, integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem setIntegral_rsHat_zero_of_bdd {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ1 : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦ2 : HasCompactSupport Φ) (hΦ3 : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ)
    (η : Fin a → Af E) {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕' : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕' μ) {ω : HChar E} (hω : ω.IsUnitary) {φ φ' : Sm E a}
    (hb : φ.1 ∈ bddForms E a ω) (hb' : φ'.1 ∈ bddForms E a ω) :
    ∫ g in 𝓕', adelicFourierPi E (rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 ∂μ =
      (((finiteMeasurePi E (latt a J)).toReal : ℂ) * ∫ x, Φ x ∂infMeasure E a) *
        ∫ g in 𝓕', φ.1 g * conj (φ'.1 g) ∂μ := by
  have hΦ : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ := ⟨hΦ1, hΦ2, hΦ3⟩
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  haveI : IsFiniteMeasure (μ.restrict 𝓕') :=
    ⟨by rw [Measure.restrict_apply_univ, ← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ h𝓕]; exact measure_lt_top _ _⟩
  haveI : SFinite (infMeasure E a) := by unfold infMeasure; infer_instance
  obtain ⟨C, hC⟩ := hb.2.2.2
  obtain ⟨D, hD⟩ := hb'.2.2.2
  have hΦi : Integrable Φ (infMeasure E a) := by
    unfold infMeasure
    exact (hΦ1.continuous.integrable_of_hasCompactSupport hΦ2).smul_measure (by simp)
  have hi : Integrable (fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2)
      ((μ.restrict 𝓕').prod (infMeasure E a)) := by
    refine ((integrable_const (C * D)).mul_prod hΦi.norm).mono'
      (continuous_rsInf hb.1 hb'.1 hΦ1.continuous hΦ3).aestronglyMeasurable (.of_forall fun p => ?_)
    simp only [rsInf, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC 1)))
      (norm_nonneg _)
  have hx : ∀ x, ∫ g in 𝓕', rsInf ℓ φ.1 φ'.1 Φ g x ∂μ = (∫ g in 𝓕', φ.1 g * conj (φ'.1 g) ∂μ) * Φ x := by
    intro x
    simp only [rsInf]
    rw [integral_mul_const]
    congr 1
    exact GlobalTheory.RSResidue.setIntegral_mul_right h𝓕 (f := fun g => φ.1 g * conj (φ'.1 g))
      (GlobalTheory.Petersson.leftInv_mul_conj hω hb hb') _
  simp only [GlobalTheory.RSResidue.rsHat_zero J η φ φ' hΦ]
  rw [integral_mul_const, integral_integral_swap hi]
  simp only [hx, integral_const_mul]
  ring

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Establish `h` using `mem_rsm hφ`. Establish `h'` using `mem_rsm hφ'`. Establish `hT : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ` using `⟨hΦ, hcs, hs⟩`. Take `⟨-, -, b3⟩` from `GlobalTheory.RSThetaLowM.partB_entire J η hπ hπ' h h' hc hc' hT h𝓕`. Simplify using `only [Complex.ofReal_cpow (ideleModule E _).2.le, Complex.ofReal_sub, Complex.ofReal_one]`.

Conclude with `⟨fun x hx => ⟨(GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx).1, GlobalTheory.RSThetaLowM.integrableOn_partA J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx, (GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx).2⟩, b3.co …`.
-/
theorem theta_integral_low_mspanR {ℓ : Fin a} {π π' : CuspSub E a} (hπ : π.IsUnitary) (hπ' : π'.IsUnitary)
    {φ φ' : Sm E a} (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) (hφ' : φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π')
    (hc : Continuous φ.1) (hc' : Continuous φ'.1) {Φ : (Fin a → Cinf E) → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hcs : HasCompactSupport Φ) (hs : tsupport Φ ⊆ rowSet E ℓ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    (∀ x : ℝ, 1 < x →
      IntegrableOn (fun g : GA E a =>
        (∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ))) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ ∧
      IntegrableOn (fun g : GA E a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ))) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ ∧
      ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x : ℝ) : ℂ)) ∂μ =
        ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ +
        ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ) ∧
    Continuous fun x : ℝ => ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ := by
  have h := mem_rsm hφ
  have h' := mem_rsm hφ'
  have hT : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ := ⟨hΦ, hcs, hs⟩
  obtain ⟨-, -, b3⟩ := GlobalTheory.RSThetaLowM.partB_entire J η hπ hπ' h h' hc hc' hT h𝓕
  simp only [Complex.ofReal_cpow (ideleModule E _).2.le, Complex.ofReal_sub, Complex.ofReal_one]
  exact ⟨fun x hx => ⟨(GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx).1,
      GlobalTheory.RSThetaLowM.integrableOn_partA J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx,
      (GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ' h h' hc hc' hT h𝓕 (s := x) hx).2⟩,
    b3.continuous.comp Complex.continuous_ofReal⟩

end GlobalTheory.RSThetaLimR

namespace GlobalTheory.RSThetaLimR

/- English proof (translation)
Introduce `E _ _ _ a ℓ Φ hΦ hc hs J η μ _ 𝓕 𝓕' h𝓕 h𝓕'`. Take `⟨K, hKdef⟩ : ∃ K : ℂ, K = ((GroundTheory.Automorphic.GJMatrix.finiteMeasurePi E (GlobalTheory.ThetaPoisson.latt a J)).toReal : ℂ) * ∫ x, Φ x ∂GlobalTheory.ThetaPoisson.infMeasure E a` from `⟨_, rfl⟩`. Establish `hK0 : (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → K ≠ 0` using `fun h1 h2 => hKdef ▸ resConst_ne_zero hΦ hc J h1 h2`. Establish `had : ((a : ℝ) * (Module.finrank ℚ E : ℝ)) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 ℓ.pos)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')`. Use `⟨((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ)) * K, fun h1 h2 => mul_ne_zero (Complex.ofReal_ne_zero.2 (one_div_ne_zero had)) (hK0 h1 h2), ?_⟩` and prove the remaining obligations.

Introduce `π π' ω hω hπ hπ' φ φ' hφ hφ'`. Establish `hu : π.IsUnitary` using `⟨ω, hω, CuspSub.hasCentral_iff.2 hπ⟩`. Establish `hu' : π'.IsUnitary` using `⟨ω, hω, CuspSub.hasCentral_iff.2 hπ'⟩`. Establish `hb` using `mem_bddForms hω hπ hφ`. Establish `hb'` using `mem_bddForms hω hπ' hφ'`.

Take `⟨u1, u2, u3, -⟩` from `GlobalTheory.RSThetaM.theta_integral_upper_mspan E a ℓ π π' hu hu' φ φ' hφ hφ' Φ hΦ.continuous hc hs J η μ 𝓕 h𝓕`. Take `⟨l1, l2⟩` from `theta_integral_low_mspanR hu hu' hφ hφ' hb.1 hb'.1 hΦ hc hs J η h𝓕`. Take `⟨f1, f2, f3⟩` from `GlobalTheory.RSResidue.rsHat_zero_props hω hb hb' ⟨hΦ, hc, hs⟩ J η`. Establish `hres` using `GlobalTheory.T.tendsto_residueTerm_rankinSelberg_innerProduct E a ℓ.pos μ 𝓕 𝓕' h𝓕 h𝓕' _ f1 f2 f3`. Rewrite `hres` using `[setIntegral_rsHat_zero_of_bdd hΦ hc hs J η h𝓕' hω hb hb', ← hKdef]`.

Establish `hδc : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ)` using `continuous_subtype_val.comp (continuous_ideleModule.comp GeneralLinearGroup.continuous_det)`. Establish `hδ0 : ∀ g : GA E a, 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ)` using `fun g => (ideleModule E _).2`. Establish `hT : MeasurableSet {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}` using `(isClosed_le hδc continuous_const).measurableSet`. Establish `hsum : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) = ∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val)` using `fun g => GlobalTheory.RSThetaLow.tsum_rsPsi_eq_tsum_ne_zero J η φ.1 φ'.1 hs g`. Establish `hint : ∀ x : ℝ, 1 < x → IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) 𝓕 μ`.

Introduce `x hx`. Establish `iLo : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) (𝓕 ∩ {g | (ideleModule E (GeneralLine …`. Simplify using `only [hsum]`. Conclude with `(l1 x hx).1`. Establish `iHi : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) (𝓕 ∩ {g | 1 ≤ (ideleModule E (General …`.

Simplify using `only [Complex.ofReal_cpow (hδ0 _).le]`. Conclude with `u3 x`. Use `(iLo.union iHi).mono_set fun g hg => ?_` and prove the remaining obligations. Distinguish the cases in `h : (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1`. Conclude with `Or.inl ⟨hg, h⟩`.

Conclude with `Or.inr ⟨hg, (not_le.1 h).le⟩`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Use `set U : ℝ → ℂ := fun x => ∫ g in 𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ …`. Use `set B : ℝ → ℂ := fun x => ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹). …`. Establish `hsplit : ∀ x : ℝ, 1 < x → ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ = ∫ g in (𝓕 ∩ {g | (ideleModule E (Ge …`.

Introduce `x hx`. Rewrite using `[← integral_inter_add_diff hT (hint x hx)]`. Use `congr 1`. Simplify using `only [hsum]`. Conclude with `(l1 x hx).2.2`.

Use `set M : ℝ := ∫ g in 𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (2 : ℝ) ∂μ wit …`. Establish `hUb : ∀ x : ℝ, x ≤ 2 → ‖U x‖ ≤ M`. Introduce `x hx2`. Use `norm_integral_le_of_norm_le ((u2 2).mono_set fun g hg => ⟨hg.1, by have h := hg.2; simp only [Set.mem_setOf_eq, not_le] at h ⊢; exact h.le⟩) ?_` and prove the remaining obligations. Use `(ae_restrict_of_ae_restrict_of_subset (Set.diff_subset_compl _ _) (ae_restrict_mem hT.compl)).mono fun g hg => ?_` and prove the remaining obligations.

Establish `h1 : 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)`. Establish `h` using `hg`. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at h`. Conclude with `h.le`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hδ0 g).le _)]`.

Conclude with `mul_le_mul (norm_tsum_le_tsum_norm (u1 g)) (Real.rpow_le_rpow_of_exponent_le h1 hx2) (Real.rpow_nonneg (hδ0 g).le _) (tsum_nonneg fun _ => norm_nonneg _)`. Establish `hx1 : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 0)`. Establish `: Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) (𝓝 1) (𝓝 ((((1 : ℝ) - 1 : ℝ)) : ℂ))` using `(Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).tendsto 1`. Simplify using `using this.mono_left nhdsWithin_le_nhds`. Establish `tB : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * B x) (𝓝[>] 1) (𝓝 0)`.

Simplify using `using hx1.mul ((l2.tendsto 1).mono_left nhdsWithin_le_nhds)`. Establish `tU : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * U x) (𝓝[>] 1) (𝓝 0)`. Use `squeeze_zero_norm' (a := fun x : ℝ => ‖((x - 1 : ℝ) : ℂ)‖ * M) ?_ (by have h := hx1.norm.mul_const M; rwa [norm_zero, zero_mul] at h)` and prove the remaining obligations. Use `filter_upwards [Ioc_mem_nhdsGT (one_lt_two : (1 : ℝ) < 2)] with x hx`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_mul_of_nonneg_left (hUb x hx.2) (norm_nonneg _)`. Establish `tot` using `(hres.add tB).add tU`. Rewrite `*` using `[add_zero, add_zero, mul_assoc]`. Use `tot.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with x hx`.

Rewrite using `[hsplit x hx]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_integral_pole_mspanR : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∃ c : ℂ, ((∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → c ≠ 0) ∧ ∀ (π π' : CuspSub E a) (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω → ∀ φ φ' : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') → (∀ x : ℝ, 1 < x → IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) 𝓕 μ) ∧ Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ) (𝓝[>] 1) (𝓝 (c * ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ'.1 g) ∂μ)) := by
  intro E _ _ _ a ℓ Φ hΦ hc hs J η μ _ 𝓕 𝓕' h𝓕 h𝓕'
  obtain ⟨K, hKdef⟩ : ∃ K : ℂ, K = ((GroundTheory.Automorphic.GJMatrix.finiteMeasurePi E (GlobalTheory.ThetaPoisson.latt a J)).toReal : ℂ) * ∫ x, Φ x ∂GlobalTheory.ThetaPoisson.infMeasure E a := ⟨_, rfl⟩
  have hK0 : (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → K ≠ 0 := fun h1 h2 => hKdef ▸ resConst_ne_zero hΦ hc J h1 h2
  have had : ((a : ℝ) * (Module.finrank ℚ E : ℝ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.pos_iff_ne_zero.1 ℓ.pos)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  refine ⟨((((1 : ℝ) / ((a : ℝ) * (Module.finrank ℚ E : ℝ)) : ℝ) : ℂ)) * K,
    fun h1 h2 => mul_ne_zero (Complex.ofReal_ne_zero.2 (one_div_ne_zero had)) (hK0 h1 h2), ?_⟩
  intro π π' ω hω hπ hπ' φ φ' hφ hφ'
  have hu : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hπ⟩
  have hu' : π'.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hπ'⟩
  have hb := mem_bddForms hω hπ hφ
  have hb' := mem_bddForms hω hπ' hφ'
  obtain ⟨u1, u2, u3, -⟩ := GlobalTheory.RSThetaM.theta_integral_upper_mspan E a ℓ π π' hu hu' φ φ' hφ hφ' Φ hΦ.continuous hc hs J η μ 𝓕 h𝓕
  obtain ⟨l1, l2⟩ := theta_integral_low_mspanR hu hu' hφ hφ' hb.1 hb'.1 hΦ hc hs J η h𝓕
  obtain ⟨f1, f2, f3⟩ := GlobalTheory.RSResidue.rsHat_zero_props hω hb hb' ⟨hΦ, hc, hs⟩ J η
  have hres := GlobalTheory.T.tendsto_residueTerm_rankinSelberg_innerProduct E a ℓ.pos μ 𝓕 𝓕' h𝓕 h𝓕' _ f1 f2 f3
  rw [setIntegral_rsHat_zero_of_bdd hΦ hc hs J η h𝓕' hω hb hb', ← hKdef] at hres
  have hδc : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    continuous_subtype_val.comp (continuous_ideleModule.comp GeneralLinearGroup.continuous_det)
  have hδ0 : ∀ g : GA E a, 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) := fun g => (ideleModule E _).2
  have hT : MeasurableSet {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1} := (isClosed_le hδc continuous_const).measurableSet
  have hsum : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) = ∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := fun g =>
    GlobalTheory.RSThetaLow.tsum_rsPsi_eq_tsum_ne_zero J η φ.1 φ'.1 hs g
  have hint : ∀ x : ℝ, 1 < x → IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) 𝓕 μ := by
    intro x hx
    have iLo : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ)) (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
      simp only [hsum]; exact (l1 x hx).1
    have iHi : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ))
        (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) μ := by
      simp only [Complex.ofReal_cpow (hδ0 _).le]; exact u3 x
    refine (iLo.union iHi).mono_set fun g hg => ?_
    by_cases h : (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1
    · exact Or.inl ⟨hg, h⟩
    · exact Or.inr ⟨hg, (not_le.1 h).le⟩
  refine ⟨hint, ?_⟩

  set U : ℝ → ℂ := fun x => ∫ g in 𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ with hU
  set B : ℝ → ℂ := fun x => ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* (g⁻¹).valᵀ)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ with hB
  have hsplit : ∀ x : ℝ, 1 < x → ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ =
      ∫ g in (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}), GroundTheory.Automorphic.GJMatrix.adelicFourierPi E (GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g) 0 * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x - 1) : ℝ) : ℂ)) ∂μ + B x + U x := by
    intro x hx
    rw [← integral_inter_add_diff hT (hint x hx)]
    congr 1
    simp only [hsum]
    exact (l1 x hx).2.2

  set M : ℝ := ∫ g in 𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
    (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) * (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (2 : ℝ) ∂μ with hM
  have hUb : ∀ x : ℝ, x ≤ 2 → ‖U x‖ ≤ M := by
    intro x hx2
    refine norm_integral_le_of_norm_le ((u2 2).mono_set fun g hg => ⟨hg.1, by have h := hg.2; simp only [Set.mem_setOf_eq, not_le] at h ⊢; exact h.le⟩) ?_
    refine (ae_restrict_of_ae_restrict_of_subset (Set.diff_subset_compl _ _) (ae_restrict_mem hT.compl)).mono
      fun g hg => ?_
    have h1 : 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) := by
      have h := hg; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at h; exact h.le
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hδ0 g).le _)]
    exact mul_le_mul (norm_tsum_le_tsum_norm (u1 g)) (Real.rpow_le_rpow_of_exponent_le h1 hx2)
      (Real.rpow_nonneg (hδ0 g).le _) (tsum_nonneg fun _ => norm_nonneg _)
  have hx1 : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ)) (𝓝 1) (𝓝 ((((1 : ℝ) - 1 : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).tendsto 1
    simpa using this.mono_left nhdsWithin_le_nhds
  have tB : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * B x) (𝓝[>] 1) (𝓝 0) := by
    simpa using hx1.mul ((l2.tendsto 1).mono_left nhdsWithin_le_nhds)
  have tU : Tendsto (fun x : ℝ => ((x - 1 : ℝ) : ℂ) * U x) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => ‖((x - 1 : ℝ) : ℂ)‖ * M) ?_
      (by have h := hx1.norm.mul_const M; rwa [norm_zero, zero_mul] at h)
    filter_upwards [Ioc_mem_nhdsGT (one_lt_two : (1 : ℝ) < 2)] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hUb x hx.2) (norm_nonneg _)
  have tot := (hres.add tB).add tU
  rw [add_zero, add_zero, mul_assoc] at *
  refine tot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [hsplit x hx]
  ring

end GlobalTheory.RSThetaLimR

end
