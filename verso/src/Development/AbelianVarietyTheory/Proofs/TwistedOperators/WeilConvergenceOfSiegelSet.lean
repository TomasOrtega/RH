import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralFundamentalDomainLeOfMeetsOrbitsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianWittIndexLeNegativeSignatureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelSiegelSetLeTorusPowerHeightStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.WeilConv

/- English proof (translation)
Introduce `D ψ θ hθ ε M X χ χ' ω hω p hsig hd ν 𝓕 hν Φ hΦ`. Take `⟨τ, hτ⟩` from `hsig`. Take `⟨i1, i2, i3, i4, i5, i6, i7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M`. Establish `hν1` using `hν.1`. Take `⟨r, Xf, Yf, hW⟩` from `GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram M)`.

Establish `hr : r ≤ p` using `GlobalTheory.T.hermitianWittIndex_le_negative_signature M hτ hW`. Take `⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩` from `hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) M.rank M.gram (isHermND_gram M) r Xf Yf hW`. Take `⟨-, C₁, hC₁⟩` from `hmeas ν hν1`. Take `⟨N, C, hC⟩` from `GlobalTheory.T.thetaKernel_siegelSet_le_torusPower_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj`. Establish `hω' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε)` using `hω`.

Establish `hcont : ∀ h, Continuous fun g => thetaKO ω g h Φ` using `fun h => (hω'.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε M).prodMk continuous_const)`. Establish `hinv : ∀ h, ∀ γ ∈ GQ M, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ` using `fun h γ hγ g => by`. Establish `e1 : (((ofSgn ε M).symm (γ * g), h) : GA D (sgn ε M) × GA D X) = ((ofSgn ε M).symm γ, 1) * ((ofSgn ε M).symm g, h)` using `by simp`. Use `show (ω.toSgn ε) ((ofSgn ε M).symm (γ * g), h) Φ 0 = (ω.toSgn ε) ((ofSgn ε M).symm g, h) Φ 0`. Rewrite using `[e1, map_mul, Module.End.mul_apply]`.

Conclude with `hω'.om_aut _ (ofSgn_symm_mem_GQ ε hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hΦ)`. Use `set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig M.gram Xf Yf Ω c K with hSdef`. Establish `hSm : MeasurableSet S` using `hcl.measurableSet`. Establish `hScov : ∀ g, ∃ γ ∈ GQ M, γ * g ∈ S` using `fun g => by`. Take `⟨γ, hγ, s, hs, e⟩` from `hcov g`.

Use `⟨γ⁻¹, inv_mem hγ, ?_⟩` and prove the remaining obligations. Rewrite using `[e, inv_mul_cancel_left]`. Conclude with `hs`. Establish `hI` using `GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil D.host.F M.rank r X.rank hc (by omega)`. Use `set I := ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) * ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) with hIdef`.

Establish `key : ∀ h, ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤ C₁ * (ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N) * I)` using `fun h => by`. Establish `hA : 0 ≤ max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `hC₁ (fun g => ‖thetaKO ω g h Φ‖ₑ) _ (by fun_prop) fun q hq t ht a ha k hk => ?_` and prove the remaining obligations. Establish `ht0 : ∀ i, 0 < t i` using `ht.1`.

Establish `hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)` using `Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _`. Rewrite using `[← ofReal_norm_eq_enorm]`. Use `ENNReal.ofReal_le_ofReal ((hC h q hq t ht a ha k hk).trans ?_)` and prove the remaining obligations. Establish `hH : 0 ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N` using `by positivity`. Use `gcongr`.

Conclude with `le_max_left _ _`. Use `_ = C₁ * (ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N) * I) := by`. Rewrite using `[hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `congr 1`. Conclude with `lintegral_congr fun t => by rw [ENNReal.ofReal_mul hA, mul_assoc]`.

Use `⟨N, (C₁ : ℝ) * max C 0 * I.toReal, fun h => ⟨⟨(hcont h).aestronglyMeasurable, ?_⟩, ?_⟩⟩` and prove the remaining obligations. Conclude with `(key h).trans_lt (by finiteness)`. Rewrite using `[integral_norm_eq_lintegral_enorm (hcont h).aestronglyMeasurable]`. Establish `hA : 0 ≤ max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N` using `by positivity`. Use `(ENNReal.toReal_mono (by finiteness) (key h)).trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.coe_toReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weilConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.SquareSt.WeilConvergence := by
  intro D ψ θ hθ ε M X χ χ' ω hω p hsig hd ν 𝓕 hν Φ hΦ
  obtain ⟨τ, hτ⟩ := hsig
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D M
  have hν1 := hν.1
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram M)
  have hr : r ≤ p := GlobalTheory.T.hermitianWittIndex_le_negative_signature M hτ hW
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) M.rank M.gram (isHermND_gram M) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν1
  obtain ⟨N, C, hC⟩ := GlobalTheory.T.thetaKernel_siegelSet_le_torusPower_height ψ θ hθ ε M X χ χ' ω hω Φ hΦ r Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj
  have hω' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hω
  have hcont : ∀ h, Continuous fun g => thetaKO ω g h Φ := fun h =>
    (hω'.om_cont Φ hΦ 0).comp ((continuous_ofSgn_symm ε M).prodMk continuous_const)
  have hinv : ∀ h, ∀ γ ∈ GQ M, ∀ g, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := fun h γ hγ g => by
    have e1 : (((ofSgn ε M).symm (γ * g), h) : GA D (sgn ε M) × GA D X) =
        ((ofSgn ε M).symm γ, 1) * ((ofSgn ε M).symm g, h) := by simp
    show (ω.toSgn ε) ((ofSgn ε M).symm (γ * g), h) Φ 0 = (ω.toSgn ε) ((ofSgn ε M).symm g, h) Φ 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hω'.om_aut _ (ofSgn_symm_mem_GQ ε hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hΦ)
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig M.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ M, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI := GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil D.host.F M.rank r X.rank hc (by omega)
  set I := ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) with hIdef
  have key : ∀ h, ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤
      C₁ * (ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N) * I) := fun h => by
    have hA : 0 ≤ max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
    calc ∫⁻ g in 𝓕, ‖thetaKO ω g h Φ‖ₑ ∂ν ≤ ∫⁻ g in S, ‖thetaKO ω g h Φ‖ₑ ∂ν :=
          GlobalTheory.T.lintegral_fundamentalDomain_le_of_meets_all_orbits (GQ M) ν hν.2 hSm hScov (hcont h).enorm.measurable
            (fun γ hγ g => by rw [hinv h γ hγ g])
      _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N *
            ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank)) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F M.rank t * ∏ i, t i)⁻¹) := by
          refine hC₁ (fun g => ‖thetaKO ω g h Φ‖ₑ) _ (by fun_prop) fun q hq t ht a ha k hk => ?_
          have ht0 : ∀ i, 0 < t i := ht.1
          have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * X.rank) :=
            Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
          rw [← ofReal_norm_eq_enorm]
          refine ENNReal.ofReal_le_ofReal ((hC h q hq t ht a ha k hk).trans ?_)
          have hH : 0 ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
          gcongr
          exact le_max_left _ _
      _ = C₁ * (ENNReal.ofReal (max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N) * I) := by
          rw [hIdef, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hA, mul_assoc]
  refine ⟨N, (C₁ : ℝ) * max C 0 * I.toReal, fun h => ⟨⟨(hcont h).aestronglyMeasurable, ?_⟩, ?_⟩⟩
  · exact (key h).trans_lt (by finiteness)
  · rw [integral_norm_eq_lintegral_enorm (hcont h).aestronglyMeasurable]
    have hA : 0 ≤ max C 0 * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by positivity
    refine (ENNReal.toReal_mono (by finiteness) (key h)).trans (le_of_eq ?_)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.coe_toReal]
    ring

/- English proof (translation)
Introduce `hRT _` and use `weilConvergence_of_siegelSet hRT`.
-/
theorem weilConvergence : GlobalTheory.Published.SiegelSetUnitary → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.SquareSt.WeilConvergence :=
  fun hRT _ => weilConvergence_of_siegelSet hRT

end GlobalTheory.WeilConv

end
