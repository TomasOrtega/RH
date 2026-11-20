import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddChar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensChLift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace AdelicCharacterCondition

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem isCharAF_of {E : Type} [Field E] [NumberField E] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF E ψ := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  have hb : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
  obtain ⟨y, hy⟩ := hψ.loc ⟨M, hM.isPrime, hb⟩
  exact ⟨hψ.cont, hψ.norm, hψ.rat, _, hy⟩

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem condAA {E : Type} [Field E] [NumberField E] {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) :
    ∀ᶠ v in (cofinite : Filter (HeightOneSpectrum (𝓞 E))), ∀ t : v.adicCompletion E,
      (∀ s ∈ v.adicCompletionIntegers E, ψ (sFin E (sLoc E v (s * t))) = 1) ↔ t ∈ v.adicCompletionIntegers E := by
  have h := _root_.PI.VolStabSW.VolAAW.condAA_of (_root_.PI.VolStabSW.VolAAW.condExact_of _root_.PI.VolStabSW.sAf_holds
    (_root_.PI.VolStabSW.chInf_of_lift _root_.PI.VolStabSW.chLift_holds)) E ψ (isCharAF_of hψ)
  filter_upwards [h] with v hv t
  simp only [sFin_sLoc_eq]
  exact hv t

end AdelicCharacterCondition

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem adelic_character_holds : StandardCharacterExists := by
  intro E _ _ _
  obtain ⟨ψ, hψ⟩ := exists_stdPsi E
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [AdelicCharacterCondition.condAA hψ] with w hw
  have hint : ∀ y ∈ Ov E w, ψ (sFin E (sLoc E w y)) = 1 := by
    intro y hy
    have := (hw 1).2 (one_mem _) y hy
    rwa [mul_one] at this
  refine ⟨hint, ?_⟩
  set ϖ := _root_.PI.VolStabSW.unifV w with hϖ
  have hϖ0 : ϖ ≠ 0 := (_root_.PI.VolStabSW.unifV_spec w).1
  have hu : IsUnifV E w ϖ := _root_.PI.VolStabSW.unifV_val w
  have hnot : ϖ⁻¹ ∉ w.adicCompletionIntegers E := by
    intro h
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at h
    have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := _root_.PI.VolStabSW.unifV_val w
    rw [hv] at h
    exact absurd h (by decide)
  have hex : ¬ ∀ s ∈ w.adicCompletionIntegers E, ψ (sFin E (sLoc E w (s * ϖ⁻¹))) = 1 :=
    fun h => hnot ((hw _).1 h)
  push Not at hex
  obtain ⟨s, hs, hne⟩ := hex
  refine ⟨ϖ, s * ϖ⁻¹, hu, ?_, hne⟩
  rw [mul_comm s, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  exact hs

end PositivityTheory.jumpWindows

end
