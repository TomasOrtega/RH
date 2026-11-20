import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FundamentalDomainSetIntegralMulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder NNReal ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftShift

/- English proof (translation)
Establish `hle : μ 𝓕 ≤ μ C`. Rewrite using `[h𝓕.measure_eq_tsum C]`. Use `le_trans (measure_mono ?_) (measure_iUnion_le _)` and prove the remaining obligations. Introduce `h hh`. Take `⟨γ, hγ, c, hc, rfl⟩` from `hcov h`.

Conclude with `Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hh⟩`. Establish `hfin : μ 𝓕 ≠ ⊤` using `(hle.trans_lt hC.measure_lt_top).ne`. Establish `hpos : μ 𝓕 ≠ 0` using `h𝓕.measure_ne_zero (NeZero.ne μ)`. Establish `h` using `Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g => g * k) μ) μ`. Use `set c := Measure.haarScalarFactor (Measure.map (fun g => g * k) μ) μ with hc`.

Establish `hq : Measure.QuasiMeasurePreserving (fun g : G => g * k) μ μ` using `⟨measurable_mul_const k, by rw [h]; exact Measure.smul_absolutelyContinuous⟩`. Establish `h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ`. Use `h𝓕.preimage_of_equiv hq (e := id) Function.bijective_id ?_` and prove the remaining obligations. Introduce `γ g`. Simplify using `only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]`.

Establish `h1 : Measure.map (fun g => g * k) μ 𝓕 = μ 𝓕`. Use `(MeasurableEquiv.mulRight k).map_apply (μ := μ) 𝓕` as an intermediate fact. Rewrite `this` using `[MeasurableEquiv.coe_mulRight]`. Rewrite using `[this]`. Conclude with `h2.measure_eq h𝓕`.

Establish `h3 : (c : ℝ≥0∞) * μ 𝓕 = 1 * μ 𝓕`. Rewrite using `[one_mul]`. Use `conv_rhs => rw [← h1, h]`. Simplify using the standard rewrite rules. Establish `h4 : (c : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj hpos hfin).1 h3`.

Establish `h5 : c = 1` using `by exact_mod_cast h4`. Rewrite using `[h, h5, one_smul]`.
-/
theorem map_mul_right_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 C : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (k : G) :
    Measure.map (fun g => g * k) μ = μ := by
  have hle : μ 𝓕 ≤ μ C := by
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro h hh
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hh⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hC.measure_lt_top).ne
  have hpos : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun g => g * k) μ) μ
  set c := Measure.haarScalarFactor (Measure.map (fun g => g * k) μ) μ with hc
  have hq : Measure.QuasiMeasurePreserving (fun g : G => g * k) μ μ :=
    ⟨measurable_mul_const k, by rw [h]; exact Measure.smul_absolutelyContinuous⟩
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hq (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have h1 : Measure.map (fun g => g * k) μ 𝓕 = μ 𝓕 := by
    have := (MeasurableEquiv.mulRight k).map_apply (μ := μ) 𝓕
    rw [MeasurableEquiv.coe_mulRight] at this
    rw [this]
    exact h2.measure_eq h𝓕
  have h3 : (c : ℝ≥0∞) * μ 𝓕 = 1 * μ 𝓕 := by
    rw [one_mul]
    conv_rhs => rw [← h1, h]
    simp
  have h4 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 : c = 1 := by exact_mod_cast h4
  rw [h, h5, one_smul]

/- English proof (translation)
Introduce `D ψ V W χS χT ω ν 𝓕 s F H hpos hν h𝓕 hs hF hinv k _`. Use `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig W.gram` as an intermediate fact. Take `⟨_, _, _, _⟩` from `GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable W`. Take `⟨C, hC, hcov⟩` from `GlobalTheory.definite_unitary_cocompact W hpos`. Take `⟨hcont, hθ⟩` from `GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω H s hs`.

Establish `hk` using `map_mul_right_of_cocompact (GQ W) ν 𝓕 C h𝓕 hC hcov k`. Use function extensionality and compare the values at `g`. Establish `hΦ : ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) s * F (γ * h) = thetaKO ω g h s * F h`. Introduce `γ hγ h`. Use `hθ 1 (one_mem _) γ hγ g h` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Rewrite using `[this, hinv γ hγ]`. Establish `hi : IntegrableOn (fun h => thetaKO ω g h s * F h) 𝓕 ν` using `GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain W ν 𝓕 C hν h𝓕 hC hcov _ ((hcont.comp (Continuous.prodMk_right g)).mul hF) hΦ`. Establish `key` using `(GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ W) ν 𝓕 h𝓕 k hk (fun h => thetaKO ω g h s * F h) hΦ hi).2`. Establish `hsh : ∀ h, thetaKO ω g h (ω (1, k) s) = thetaKO ω g (h * k) s`.

Introduce `h`. Establish `h1 : ω (g, h * k) = ω (g, h) * ω (1, k)`. Rewrite using `[← map_mul, Prod.mk_mul_mk, mul_one]`. Unfold `thetaKO`. Rewrite using `[h1]`.

Both sides reduce to the same expression. Unfold `Lift.liftInt`. Simplify using `only [hsh, rTr]`. Conclude with `key`.
-/
theorem liftInt_shift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (s : WO V W → ℂ) (F : GA D W → ℂ), IsWeilDatumO ψ V W χS χT ω → (∀ τ, (gramAt D W τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν → IsThetaFunO ψ V W s → Continuous F → (∀ γ ∈ GQ W, ∀ h, F (γ * h) = F h) → ∀ k ∈ GinfC W, Lift.liftInt ν 𝓕 (thetaKO ω) (ω (1, k) s) (rTr W k F) = Lift.liftInt ν 𝓕 (thetaKO ω) s F := by
  intro D ψ V W χS χT ω ν 𝓕 s F H hpos hν h𝓕 hs hF hinv k _
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig W.gram
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable W
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact W hpos
  obtain ⟨hcont, hθ⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ V W χS χT ω H s hs
  have hk := map_mul_right_of_cocompact (GQ W) ν 𝓕 C h𝓕 hC hcov k
  funext g
  have hΦ : ∀ γ ∈ GQ W, ∀ h, thetaKO ω g (γ * h) s * F (γ * h) = thetaKO ω g h s * F h := by
    intro γ hγ h
    have := hθ 1 (one_mem _) γ hγ g h
    rw [one_mul] at this
    rw [this, hinv γ hγ]
  have hi : IntegrableOn (fun h => thetaKO ω g h s * F h) 𝓕 ν :=
    GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain W ν 𝓕 C hν h𝓕 hC hcov _
      ((hcont.comp (Continuous.prodMk_right g)).mul hF) hΦ
  have key := (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ W) ν 𝓕 h𝓕 k hk
    (fun h => thetaKO ω g h s * F h) hΦ hi).2
  have hsh : ∀ h, thetaKO ω g h (ω (1, k) s) = thetaKO ω g (h * k) s := by
    intro h
    have h1 : ω (g, h * k) = ω (g, h) * ω (1, k) := by
      rw [← map_mul, Prod.mk_mul_mk, mul_one]
    unfold thetaKO
    rw [h1]
    rfl
  unfold Lift.liftInt
  simp only [hsh, rTr]
  exact key

end GlobalTheory.LiftShift
