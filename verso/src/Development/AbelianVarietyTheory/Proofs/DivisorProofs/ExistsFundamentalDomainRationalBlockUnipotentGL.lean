import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open Topology

namespace GlobalTheory.CuspRep

/- English proof (translation)
Use `discreteTopology_of_isOpen_singleton_zero ?_` and prove the remaining obligations. Establish `hU : IsOpen (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd E)` using `isOpen_set_pi Set.finite_univ fun _ _ => Formalism.IndefR.Eqv.G5.adl_isOpen_nbhd`. Establish `h : ({0} : Set (ratN E a s)) = Subtype.val ⁻¹' (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd E)`. Use extensionality with `⟨x, q, hq⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `hx p _`. Establish `: x = 0` using `congrArg Subtype.val hx`. Substitute `this` using the available equality. Conclude with `Formalism.IndefR.Eqv.G5.adl_zero_mem_nbhd`. Introduce `hx`.

Substitute `hq` using the available equality. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `p`. Establish `h0 : q p = 0` using `Formalism.IndefR.Eqv.G5.adl_eq_zero_of_mem_nbhd (q p) (hx p (Set.mem_univ _))`. Use `show algebraMap E (Ad E) (q p) = 0`.

Rewrite using `[h0, map_zero]`. Rewrite using `[h]`. Conclude with `hU.preimage continuous_subtype_val`.
-/
theorem discreteTopology_ratN (E : Type) [Field E] [NumberField E] (a s : ℕ) :
    DiscreteTopology (ratN E a s) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hU : IsOpen (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd E) :=
    isOpen_set_pi Set.finite_univ fun _ _ => Formalism.IndefR.Eqv.G5.adl_isOpen_nbhd
  have h : ({0} : Set (ratN E a s)) =
      Subtype.val ⁻¹' (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd E) := by
    ext ⟨x, q, hq⟩
    constructor
    · intro hx p _
      have : x = 0 := congrArg Subtype.val hx
      subst this
      exact Formalism.IndefR.Eqv.G5.adl_zero_mem_nbhd
    · intro hx
      subst hq
      apply Subtype.ext
      funext p
      have h0 : q p = 0 := Formalism.IndefR.Eqv.G5.adl_eq_zero_of_mem_nbhd (q p) (hx p (Set.mem_univ _))
      show algebraMap E (Ad E) (q p) = 0
      rw [h0, map_zero]
  rw [h]
  exact hU.preimage continuous_subtype_val

/- English proof (translation)
Introduce `E _ _ _ a s _ _ μ _`. Use `haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E`. Use `haveI := discreteTopology_ratN E a s`. Use `haveI := countable_ratN (E := E) (a := a) s`. Take `⟨D, -, -, hD⟩` from `GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (ratN E a s)`.

Use `haveI : MeasurableConstVAdd (ratN E a s) (BlockIx a s → Ad E) := ⟨fun γ => (continuous_const.add continuous_id : Continuous fun x : BlockIx a s → Ad E => (γ : BlockIx a s → Ad E) + x).measurable⟩`. Use `haveI : VAddInvariantMeasure (ratN E a s) (BlockIx a s → Ad E) μ := ⟨fun γ t _ => measure_preimage_add μ (γ : BlockIx a s → Ad E) t⟩`. Establish `hμ : μ ≠ 0` using `fun h => by`. Use `isOpen_univ.measure_ne_zero μ Set.univ_nonempty` as an intermediate fact. Rewrite `this` using `[h]`.

Conclude with `this rfl`. Conclude with `⟨D, hD μ, (hD μ).measure_ne_zero hμ, covol_lt_top μ D (hD μ)⟩`.
-/
theorem exists_isAddFundamentalDomain_ratN : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (s : ℕ) [MeasurableSpace (BlockIx a s → Ad E)] [BorelSpace (BlockIx a s → Ad E)] (μ : Measure (BlockIx a s → Ad E)) [μ.IsAddHaarMeasure], ∃ 𝓕 : Set (BlockIx a s → Ad E), IsAddFundamentalDomain (ratN E a s) 𝓕 μ ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 < ⊤ := by
  intro E _ _ _ a s _ _ μ _
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := discreteTopology_ratN E a s
  haveI := countable_ratN (E := E) (a := a) s
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (ratN E a s)
  haveI : MeasurableConstVAdd (ratN E a s) (BlockIx a s → Ad E) :=
    ⟨fun γ => (continuous_const.add continuous_id :
      Continuous fun x : BlockIx a s → Ad E => (γ : BlockIx a s → Ad E) + x).measurable⟩
  haveI : VAddInvariantMeasure (ratN E a s) (BlockIx a s → Ad E) μ :=
    ⟨fun γ t _ => measure_preimage_add μ (γ : BlockIx a s → Ad E) t⟩
  have hμ : μ ≠ 0 := fun h => by
    have := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    rw [h] at this
    exact this rfl
  exact ⟨D, hD μ, (hD μ).measure_ne_zero hμ, covol_lt_top μ D (hD μ)⟩

end GlobalTheory.CuspRep
