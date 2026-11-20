import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

/- English proof (translation)
Introduce `D V R hR L hL Q`. Take `⟨⟨K, hK, hKc, hKo⟩, -⟩` from `(GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V Q).2.2.2.2.2.2.2.2.1 L hL (· ∈ Q)`. Establish `hKG : ∀ g : GA D V, g ∈ K → g ∈ grpAt V (· ∈ Q)` using `fun g hg => ((hK g).1 hg).1`. Establish `h1 : InK V L (· ∈ Q) 1` using `(hK 1).1 K.one_mem`. Set `S : Set (grpAt V (· ∈ Q))` to `{g | InK V L (· ∈ Q) g.1}`.

Establish `hSe : S = ((K.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q)))`. Use extensionality with `g`. Simplify using `[S, Subgroup.mem_subgroupOf, hK]`. Establish `hSo : IsOpen S` using `hSe ▸ hKo`. Establish `hSc : IsCompact S`.

Rewrite using `[Topology.IsInducing.subtypeVal.isCompact_iff]`. Use `hKc using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`.

Conclude with `(hK _).2 hg`. Introduce `hx`. Conclude with `⟨⟨x, hKG x hx⟩, (hK x).1 hx, rfl⟩`. Set `T` to `R.subgroupOf (grpAt V (· ∈ Q))`. Set `S' : Set T` to `{g | InK V L (· ∈ Q) g.1.1}`.

Establish `hS'o : IsOpen S'` using `hSo.preimage continuous_subtype_val`. Establish `hS'c : IsCompact S'`. Rewrite using `[(Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal).isCompact_iff]`. Use `hKc.inter_right hR using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `⟨(hK _).2 hg, Subgroup.mem_subgroupOf.1 g.2⟩`. Introduce and unpack `⟨hx, hxR⟩`. Conclude with `⟨⟨⟨x, hKG x hx⟩, Subgroup.mem_subgroupOf.2 hxR⟩, (hK x).1 hx, rfl⟩`.

Set `K₀ : TopologicalSpace.PositiveCompacts (grpAt V (· ∈ Q))` to `⟨⟨S, hSc⟩, by rw [hSo.interior_eq]; exact ⟨1, h1⟩⟩`. Set `K₁ : TopologicalSpace.PositiveCompacts T` to `⟨⟨S', hS'c⟩, by rw [hS'o.interior_eq]; exact ⟨1, h1⟩⟩`. Use `⟨Measure.haarMeasure K₁, Measure.haarMeasure K₀, inferInstance, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Measure.haarMeasure_self (K₀ := K₀)`. Conclude with `Measure.haarMeasure_self (K₀ := K₁)`.
-/
theorem normAt_exists : ∀ (D : D7) (V : HSp D) (R : Subgroup (GA D V)), IsClosed (R : Set (GA D V)) → ∀ (L : Lat V),
    IsSelfDualC V L → ∀ Q : Finset (Pl D), ∃ ρ μ, IsNormAt V R L (· ∈ Q) ρ μ := by
  intro D V R hR L hL Q
  obtain ⟨⟨K, hK, hKc, hKo⟩, -⟩ := (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V Q).2.2.2.2.2.2.2.2.1 L hL (· ∈ Q)
  have hKG : ∀ g : GA D V, g ∈ K → g ∈ grpAt V (· ∈ Q) := fun g hg => ((hK g).1 hg).1
  have h1 : InK V L (· ∈ Q) 1 := (hK 1).1 K.one_mem

  let S : Set (grpAt V (· ∈ Q)) := {g | InK V L (· ∈ Q) g.1}
  have hSe : S = ((K.subgroupOf (grpAt V (· ∈ Q)) : Subgroup _) : Set (grpAt V (· ∈ Q))) := by
    ext g; simp [S, Subgroup.mem_subgroupOf, hK]
  have hSo : IsOpen S := hSe ▸ hKo
  have hSc : IsCompact S := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    convert hKc using 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩; exact (hK _).2 hg
    · intro hx; exact ⟨⟨x, hKG x hx⟩, (hK x).1 hx, rfl⟩

  let T := R.subgroupOf (grpAt V (· ∈ Q))
  let S' : Set T := {g | InK V L (· ∈ Q) g.1.1}
  have hS'o : IsOpen S' := hSo.preimage continuous_subtype_val
  have hS'c : IsCompact S' := by
    rw [(Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal).isCompact_iff]
    convert hKc.inter_right hR using 1
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩; exact ⟨(hK _).2 hg, Subgroup.mem_subgroupOf.1 g.2⟩
    · rintro ⟨hx, hxR⟩
      exact ⟨⟨⟨x, hKG x hx⟩, Subgroup.mem_subgroupOf.2 hxR⟩, (hK x).1 hx, rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts (grpAt V (· ∈ Q)) :=
    ⟨⟨S, hSc⟩, by rw [hSo.interior_eq]; exact ⟨1, h1⟩⟩
  let K₁ : TopologicalSpace.PositiveCompacts T :=
    ⟨⟨S', hS'c⟩, by rw [hS'o.interior_eq]; exact ⟨1, h1⟩⟩
  refine ⟨Measure.haarMeasure K₁, Measure.haarMeasure K₀, inferInstance, inferInstance, ?_, ?_⟩
  · exact Measure.haarMeasure_self (K₀ := K₀)
  · exact Measure.haarMeasure_self (K₀ := K₁)

end GlobalTheory.SeeSaw
