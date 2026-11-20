import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulRightEqOfFundamentalDomain
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal NNReal

namespace GlobalTheory.ResLine

/- English proof (translation)
Use `haveI : (ν.map φ).IsHaarMeasure := φ.isHaarMeasure_map ν`. Establish `hc` using `Measure.isMulLeftInvariant_eq_smul (ν.map φ) ν`. Use `set c := Measure.haarScalarFactor (ν.map φ) ν`. Establish `hφm : Measurable φ` using `φ.continuous.measurable`. Establish `hq : Measure.QuasiMeasurePreserving φ ν ν`.

Use `⟨hφm, ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Conclude with `Measure.smul_absolutelyContinuous`. Establish `h' : IsFundamentalDomain Λ (φ ⁻¹' D) ν`. Use `hD.preimage_of_equiv hq (e := fun g : Λ => (⟨φ.symm g, h2 g g.2⟩ : Λ)) ?_ ?_` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `φ.symm.injective (congrArg Subtype.val hab)`. Introduce `a`.

Conclude with `⟨⟨φ a, h1 a a.2⟩, Subtype.ext (φ.symm_apply_apply a)⟩`. Introduce `g x`. Simplify using `[Subgroup.smul_def]`. Establish `hm : ν (φ ⁻¹' D) = ν D` using `h'.measure_eq hD`. Establish `h0 : ν D ≠ 0` using `hD.measure_ne_zero (NeZero.ne ν)`.

Establish `hmap : (ν.map φ) D = ν (φ ⁻¹' D)` using `MeasurableEquiv.map_apply φ.toHomeomorph.toMeasurableEquiv D`. Establish `h3 : (c : ℝ≥0∞) * ν D = 1 * ν D`. Combine the equalities or inequalities in the displayed calculation. Establish `hc1 : c = 1`. Use `(ENNReal.mul_left_inj h0 hfin).1 h3` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Rewrite using `[hc, hc1, one_smul]`.
-/
theorem map_eq_self_of_normalises_lattice {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [LocallyCompactSpace B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]
    (Λ : Subgroup B) [Countable Λ] (ν : Measure B) [ν.IsHaarMeasure] (D : Set B) (hD : IsFundamentalDomain Λ D ν)
    (hfin : ν D ≠ ⊤) (φ : B ≃ₜ* B) (h1 : ∀ b ∈ Λ, φ b ∈ Λ) (h2 : ∀ b ∈ Λ, φ.symm b ∈ Λ) : ν.map φ = ν := by
  haveI : (ν.map φ).IsHaarMeasure := φ.isHaarMeasure_map ν
  have hc := Measure.isMulLeftInvariant_eq_smul (ν.map φ) ν
  set c := Measure.haarScalarFactor (ν.map φ) ν
  have hφm : Measurable φ := φ.continuous.measurable
  have hq : Measure.QuasiMeasurePreserving φ ν ν := by
    refine ⟨hφm, ?_⟩
    rw [hc]
    exact Measure.smul_absolutelyContinuous
  have h' : IsFundamentalDomain Λ (φ ⁻¹' D) ν := by
    refine hD.preimage_of_equiv hq (e := fun g : Λ => (⟨φ.symm g, h2 g g.2⟩ : Λ)) ?_ ?_
    · constructor
      · intro a b hab
        apply Subtype.ext
        exact φ.symm.injective (congrArg Subtype.val hab)
      · intro a
        exact ⟨⟨φ a, h1 a a.2⟩, Subtype.ext (φ.symm_apply_apply a)⟩
    · intro g x
      simp [Subgroup.smul_def]
  have hm : ν (φ ⁻¹' D) = ν D := h'.measure_eq hD
  have h0 : ν D ≠ 0 := hD.measure_ne_zero (NeZero.ne ν)
  have hmap : (ν.map φ) D = ν (φ ⁻¹' D) :=
    MeasurableEquiv.map_apply φ.toHomeomorph.toMeasurableEquiv D
  have h3 : (c : ℝ≥0∞) * ν D = 1 * ν D := by
    calc (c : ℝ≥0∞) * ν D = (c • ν) D := by simp [Measure.smul_apply]
      _ = (ν.map φ) D := by rw [hc]
      _ = 1 * ν D := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h3
    exact_mod_cast this
  rw [hc, hc1, one_smul]

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM h m hm f hf`. Use `haveI := h.haarN`. Use `haveI : LocallyCompactSpace N := h.closedN.locallyCompactSpace`. Use `haveI : LocallyCompactSpace M := h.closedM.locallyCompactSpace`. Use `haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)`.

Use `haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology (M : Set G)`. Establish `hcount : ∀ K : Subgroup G, Countable (Λ.subgroupOf K)` using `fun K => Function.Injective.countable (f := fun g : Λ.subgroupOf K => (⟨g.1.1, g.2⟩ : Λ)) fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun g : Λ => (g : G)) hab))`. Use `haveI := hcount N`. Use `haveI := hcount M`. Establish `hB : ∀ x : M, ∀ b ∈ N, M.subtype x * b * (M.subtype x)⁻¹ ∈ N` using `fun x b hb => h.norm x x.2 b hb`.

Establish `key` using `GlobalTheory.ConjModulus.map_conj_eq_self_of_lattice M G M.subtype continuous_subtype_val N h.closedN hB ν h.haarN (Λ.subgroupOf M) π DM h.haarM h.domM h.finM (fun x hx => by`. Establish `hx' : (x : G) ∈ Λ` using `hx`. Use `map_eq_self_of_normalises_lattice (Λ.subgroupOf N) ν DN h.domN h.finN (GlobalTheory.ConjModulus.conjCME M.subtype N hB x) ?_ ?_` and prove the remaining obligations. Introduce `b hb`. Establish `hb' : (b : G) ∈ Λ` using `hb`.

Conclude with `Λ.mul_mem (Λ.mul_mem hx' hb') (Λ.inv_mem hx')`. Introduce `b hb`. Establish `hb' : (b : G) ∈ Λ` using `hb`. Conclude with `Λ.mul_mem (Λ.mul_mem (Λ.inv_mem hx') hb') (Λ.inv_mem (Λ.inv_mem hx'))) ⟨m, hm⟩`. Establish `hφm : Measurable (fun b : N => (⟨M.subtype ⟨m, hm⟩ * b * (M.subtype ⟨m, hm⟩)⁻¹, hB ⟨m, hm⟩ b b.2⟩ : N))` using `(GlobalTheory.ConjModulus.conjCME M.subtype N hB ⟨m, hm⟩).continuous.measurable`.

Use `lintegral_map (μ := ν) (hf.comp measurable_subtype_coe) hφm` as an intermediate fact. Rewrite `this` using `[key]`. Conclude with `this.symm`.
-/
theorem lintegral_conj_eq_of_semiLat : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ m ∈ M, ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (m * u * m⁻¹) ∂ν = ∫⁻ u : N, f u ∂ν := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM h m hm f hf
  haveI := h.haarN
  haveI : LocallyCompactSpace N := h.closedN.locallyCompactSpace
  haveI : LocallyCompactSpace M := h.closedM.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set G)
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology (M : Set G)
  have hcount : ∀ K : Subgroup G, Countable (Λ.subgroupOf K) := fun K =>
    Function.Injective.countable (f := fun g : Λ.subgroupOf K => (⟨g.1.1, g.2⟩ : Λ))
      fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun g : Λ => (g : G)) hab))
  haveI := hcount N
  haveI := hcount M
  have hB : ∀ x : M, ∀ b ∈ N, M.subtype x * b * (M.subtype x)⁻¹ ∈ N := fun x b hb => h.norm x x.2 b hb
  have key := GlobalTheory.ConjModulus.map_conj_eq_self_of_lattice M G M.subtype continuous_subtype_val N h.closedN hB ν h.haarN
    (Λ.subgroupOf M) π DM h.haarM h.domM h.finM (fun x hx => by
      have hx' : (x : G) ∈ Λ := hx
      refine map_eq_self_of_normalises_lattice (Λ.subgroupOf N) ν DN h.domN h.finN
        (GlobalTheory.ConjModulus.conjCME M.subtype N hB x) ?_ ?_
      · intro b hb
        have hb' : (b : G) ∈ Λ := hb
        exact Λ.mul_mem (Λ.mul_mem hx' hb') (Λ.inv_mem hx')
      · intro b hb
        have hb' : (b : G) ∈ Λ := hb
        exact Λ.mul_mem (Λ.mul_mem (Λ.inv_mem hx') hb') (Λ.inv_mem (Λ.inv_mem hx'))) ⟨m, hm⟩
  have hφm : Measurable (fun b : N => (⟨M.subtype ⟨m, hm⟩ * b * (M.subtype ⟨m, hm⟩)⁻¹, hB ⟨m, hm⟩ b b.2⟩ : N)) :=
    (GlobalTheory.ConjModulus.conjCME M.subtype N hB ⟨m, hm⟩).continuous.measurable
  have := lintegral_map (μ := ν) (hf.comp measurable_subtype_coe) hφm
  rw [key] at this
  exact this.symm

end GlobalTheory.ResLine
