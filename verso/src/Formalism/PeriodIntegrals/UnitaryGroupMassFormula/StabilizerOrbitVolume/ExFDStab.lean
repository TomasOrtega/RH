import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibInfEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.FundamentalDomainExists

noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

def SCHA : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  SecondCountableTopology (HA (AF F) σ J)

def DiscHF : Prop := InCtx fun F _E _ _ _ _ _ σ _M J _a _X0 _hT =>
  DiscreteTopology (HFinIn (AF F) σ J)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' _hμ'`. Establish `i1 : SecondCountableTopology (HA (AF F) σ J)` using `h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet`. Establish `i2 : DiscreteTopology (HFinIn (AF F) σ J)` using `h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet`. Establish `i3 : SecondCountableTopology (stabT (AF F) σ J X0)` using `TopologicalSpace.Subtype.secondCountableTopology (stabT (AF F) σ J X0 : Set (HA (AF F) σ J))`. Set `f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J` to `fun x => ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩`.

Establish `hf : Continuous f` using `((continuous_subtype_val.comp continuous_subtype_val : Continuous fun x : ratIn F E σ M J (stabT (AF F) σ J X0) => ((x : stabT (AF F) σ J X0) : HA (AF F) σ J))).subtype_mk _`. Establish `hinj : Function.Injective f`. Introduce `x y hxy`. Establish `e` using `congrArg Subtype.val hxy`. Conclude with `Subtype.ext (Subtype.ext e)`.

Establish `: DiscreteTopology (ratIn F E σ M J (stabT (AF F) σ J X0))` using `DiscreteTopology.of_continuous_injective hf hinj`. Take `⟨𝓕, -, h𝓕⟩` from `PI.VolSemiDirect.W.exists_fd (G := stabT (AF F) σ J X0) (ratIn F E σ M J (stabT (AF F) σ J X0))`. Conclude with `⟨𝓕, h𝓕 μ'⟩`.
-/
theorem exFDStab_of (h1 : SCHA) (h2 : DiscHF) : ExFDStab := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet μ' _hμ'
  have i1 : SecondCountableTopology (HA (AF F) σ J) := h1 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i2 : DiscreteTopology (HFinIn (AF F) σ J) := h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  have i3 : SecondCountableTopology (stabT (AF F) σ J X0) :=
    TopologicalSpace.Subtype.secondCountableTopology (stabT (AF F) σ J X0 : Set (HA (AF F) σ J))
  let f : ratIn F E σ M J (stabT (AF F) σ J X0) → HFinIn (AF F) σ J := fun x =>
    ⟨((x : stabT (AF F) σ J X0) : HA (AF F) σ J), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_subtype_val :
      Continuous fun x : ratIn F E σ M J (stabT (AF F) σ J X0) => ((x : stabT (AF F) σ J X0) : HA (AF F) σ J))).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  have : DiscreteTopology (ratIn F E σ M J (stabT (AF F) σ J X0)) := DiscreteTopology.of_continuous_injective hf hinj
  obtain ⟨𝓕, -, h𝓕⟩ := PI.VolSemiDirect.W.exists_fd (G := stabT (AF F) σ J X0) (ratIn F E σ M J (stabT (AF F) σ J X0))
  exact ⟨𝓕, h𝓕 μ'⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hE M J hJ _ _ _ _ _ _ _ _`. Conclude with `(h F E σ hE M J hJ).2`.
-/
theorem discHF_of_discHA (h : PI.VolSemiDirect.W.DiscHA) : DiscHF := by
  intro F E _ _ _ _ _ σ hE M J hJ _ _ _ _ _ _ _ _
  exact (h F E σ hE M J hJ).2

end PI.VolStabSW
