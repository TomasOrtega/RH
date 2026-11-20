import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSubgroupCountableAndExistsStrictFundamen
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SWQ

/- English proof (translation)
Introduce `F _ _`. Set `Γ : AddSubgroup (AF F)` to `(algebraMap F (AF F)).range.toAddSubgroup`. Establish `hdisc : DiscreteTopology Γ`. Take `⟨U, hU, hU0⟩` from `GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F`. Take `⟨V, hVU, hVo, h0V⟩` from `mem_nhds_iff.1 hU`.

Rewrite using `[discreteTopology_iff_isOpen_singleton_zero]`. Establish `: ({0} : Set Γ) = ((↑) : Γ → AF F) ⁻¹' V`. Use extensionality with `⟨x, hx⟩`. Take `⟨y, rfl⟩` from `hx`. Simplify using `only [Set.mem_singleton_iff, Set.mem_preimage]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: algebraMap F (AF F) y = 0` using `congrArg Subtype.val h`. Rewrite using `[this]`. Conclude with `h0V`.

Introduce `h`. Use `hU0 y (hVU h)` as an intermediate fact. Substitute `this` using the available equality. Use `ext`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `hVo.preimage continuous_subtype_val`. Use `letI : MeasurableSpace (Multiplicative (AF F)) := borel _`. Use `haveI : BorelSpace (Multiplicative (AF F)) := ⟨rfl⟩`. Use `haveI : SecondCountableTopology (Multiplicative (AF F)) := inferInstanceAs (SecondCountableTopology (AF F))`.

Use `haveI : DiscreteTopology (AddSubgroup.toSubgroup Γ) := hdisc`. Take `⟨hc, D, hDm, hD⟩` from `GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain (AddSubgroup.toSubgroup Γ)`. Use `haveI : Countable Γ := hc`. Set `D' : Set (AF F)` to `Multiplicative.ofAdd ⁻¹' D`. Establish `hDm' : MeasurableSet D'` using `hDm`.

Establish `hfd : ∀ m : Measure (AF F), IsAddFundamentalDomain Γ D' m`. Introduce `m`. Use `IsAddFundamentalDomain.mk' hDm'.nullMeasurableSet ?_` and prove the remaining obligations. Introduce `x`. Take `⟨γ, hγ, huniq⟩` from `hD (Multiplicative.ofAdd x)`.

Use `⟨⟨γ.1.toAdd, γ.2⟩, hγ, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Use `huniq ⟨Multiplicative.ofAdd g.1, g.2⟩ hg` as an intermediate fact. Use `ext`. Conclude with `congrArg (fun s => Multiplicative.toAdd s.1) this`.

Set `μ : Measure (AF F)` to `Measure.addHaar`. Establish `hμD` using `hfd μ`. Take `⟨K, hK, hKx⟩` from `GlobalTheory.AdeleCocompact.exists_compact_adele F`. Establish `hfin : μ D' < ∞`. Combine the equalities or inequalities in the displayed calculation.

Apply `measure_mono` to reduce the goal to its premises. Introduce `d hd`. Take `⟨x, hx⟩` from `hKx d`. Use `Set.mem_iUnion.2 ⟨⟨algebraMap F (AF F) x, x, rfl⟩, ?_, hd⟩` and prove the remaining obligations. Use `⟨_, hx, ?_⟩` and prove the remaining obligations.

Use `show algebraMap F (AF F) x + (d - algebraMap F (AF F) x) = d`. Normalize the expressions using the abelian group laws. Use `_ ≤ ∑' γ : Γ, μ ((γ +ᵥ K) ∩ D') := measure_iUnion_le _`. Use `_ = μ K := (hμD.measure_eq_tsum K).symm`. Use `_ < ∞ := hK.measure_lt_top`.

Establish `hpos : μ D' ≠ 0`. Introduce `h0`. Use `hμD.measure_eq_tsum' Set.univ` as an intermediate fact. Simplify using `only [Set.univ_inter] at this`. Establish `h2 : ∀ g : Γ, μ (g +ᵥ D') = 0` using `fun g => by`.

Rewrite using `[measure_vadd]`. Conclude with `h0`. Simplify using `only [h2, tsum_zero] at this`. Conclude with `(Measure.measure_univ_ne_zero.2 (NeZero.ne μ)) this`. Use `⟨(μ D')⁻¹ • μ, ?_, D', hDm', hfd _, ?_⟩` and prove the remaining obligations.

Conclude with `Measure.IsAddHaarMeasure.smul (μ := μ) (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hpos)`. Rewrite using `[Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin.ne]`.
-/
theorem exists_adeles_haarMeasure_covolume_one : ∀ (F : Type) [Field F] [NumberField F], ∃ ν : Measure (AF F), IsCov1 ν := by
  intro F _ _
  let Γ : AddSubgroup (AF F) := (algebraMap F (AF F)).range.toAddSubgroup
  have hdisc : DiscreteTopology Γ := by
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    obtain ⟨V, hVU, hVo, h0V⟩ := mem_nhds_iff.1 hU
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have : ({0} : Set Γ) = ((↑) : Γ → AF F) ⁻¹' V := by
      ext ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := hx
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · intro h
        have : algebraMap F (AF F) y = 0 := congrArg Subtype.val h
        rw [this]; exact h0V
      · intro h
        have := hU0 y (hVU h)
        subst this
        ext; simp
    rw [this]
    exact hVo.preimage continuous_subtype_val
  letI : MeasurableSpace (Multiplicative (AF F)) := borel _
  haveI : BorelSpace (Multiplicative (AF F)) := ⟨rfl⟩
  haveI : SecondCountableTopology (Multiplicative (AF F)) := inferInstanceAs (SecondCountableTopology (AF F))
  haveI : DiscreteTopology (AddSubgroup.toSubgroup Γ) := hdisc
  obtain ⟨hc, D, hDm, hD⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain (AddSubgroup.toSubgroup Γ)
  haveI : Countable Γ := hc
  let D' : Set (AF F) := Multiplicative.ofAdd ⁻¹' D
  have hDm' : MeasurableSet D' := hDm
  have hfd : ∀ m : Measure (AF F), IsAddFundamentalDomain Γ D' m := by
    intro m
    refine IsAddFundamentalDomain.mk' hDm'.nullMeasurableSet ?_
    intro x
    obtain ⟨γ, hγ, huniq⟩ := hD (Multiplicative.ofAdd x)
    refine ⟨⟨γ.1.toAdd, γ.2⟩, hγ, ?_⟩
    intro g hg
    have := huniq ⟨Multiplicative.ofAdd g.1, g.2⟩ hg
    ext
    exact congrArg (fun s => Multiplicative.toAdd s.1) this
  let μ : Measure (AF F) := Measure.addHaar
  have hμD := hfd μ
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have hfin : μ D' < ∞ := by
    calc μ D' ≤ μ (⋃ γ : Γ, (γ +ᵥ K) ∩ D') := by
          apply measure_mono
          intro d hd
          obtain ⟨x, hx⟩ := hKx d
          refine Set.mem_iUnion.2 ⟨⟨algebraMap F (AF F) x, x, rfl⟩, ?_, hd⟩
          refine ⟨_, hx, ?_⟩
          show algebraMap F (AF F) x + (d - algebraMap F (AF F) x) = d
          abel
      _ ≤ ∑' γ : Γ, μ ((γ +ᵥ K) ∩ D') := measure_iUnion_le _
      _ = μ K := (hμD.measure_eq_tsum K).symm
      _ < ∞ := hK.measure_lt_top
  have hpos : μ D' ≠ 0 := by
    intro h0
    have := hμD.measure_eq_tsum' Set.univ
    simp only [Set.univ_inter] at this
    have h2 : ∀ g : Γ, μ (g +ᵥ D') = 0 := fun g => by
      rw [measure_vadd]; exact h0
    simp only [h2, tsum_zero] at this
    exact (Measure.measure_univ_ne_zero.2 (NeZero.ne μ)) this
  refine ⟨(μ D')⁻¹ • μ, ?_, D', hDm', hfd _, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul (μ := μ) (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hpos)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin.ne]

end GlobalTheory.SWQ
