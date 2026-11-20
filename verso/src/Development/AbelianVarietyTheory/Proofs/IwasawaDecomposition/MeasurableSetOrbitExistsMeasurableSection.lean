import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.OrbitSection

/- English proof (translation)
Establish `h : ∀ y : X, ∃ c : C, (y ∈ Set.range f → f c = y ∧ ∀ c', f c' = y → (c : ℝ) ≤ c') ∧ (y ∉ Set.range f → c = c₀)`. Introduce `y`. Distinguish the cases in `hy : y ∈ Set.range f`. Establish `hc : IsCompact (f ⁻¹' {y})` using `(isClosed_singleton.preimage hf).isCompact`. Take `⟨c, hc1, hc2⟩` from `hc.exists_isMinOn (f := fun c : C => (c : ℝ)) hy continuous_subtype_val.continuousOn`.

Conclude with `⟨c, fun _ => ⟨hc1, fun c' h' => hc2 h'⟩, fun h => absurd hy h⟩`. Conclude with `⟨c₀, fun h => absurd h hy, fun _ => rfl⟩`. Use `choose τ h1 h2 using h`. Use `⟨τ, ?_, fun y hy => (h1 y hy).1⟩` and prove the remaining obligations. Establish `hm : Measurable fun y => (τ y : ℝ)`.

Use `measurable_of_Iic fun a => ?_` and prove the remaining obligations. Establish `he : (fun y => (τ y : ℝ)) ⁻¹' Set.Iic a = f '' {c : C | (c : ℝ) ≤ a} ∪ ((Set.range f)ᶜ ∩ {_y | (c₀ : ℝ) ≤ a})`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]`. Distinguish the cases in `hy : y ∈ Set.range f`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Or.inl ⟨τ y, h, (h1 y hy).1⟩`. Introduce and unpack `(⟨c, hc, hcy⟩ | h)`. Conclude with `((h1 y hy).2 c hcy).trans hc`.

Conclude with `absurd hy h.1`. Rewrite using `[h2 y hy]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `Or.inr ⟨hy, h⟩`.

Introduce and unpack `(⟨c, -, hcy⟩ | h)`. Conclude with `absurd ⟨c, hcy⟩ hy`. Conclude with `h.2`. Rewrite using `[he]`. Use `MeasurableSet.union ?_ (MeasurableSet.inter ?_ (MeasurableSet.const _))` and prove the remaining obligations.

Conclude with `((isClosed_le continuous_subtype_val continuous_const).isCompact.image hf).isClosed.measurableSet`. Conclude with `(isCompact_range hf).isClosed.measurableSet.compl`. Conclude with `hm.subtype_mk (h := fun y => (τ y).2)`.
-/
theorem exists_section_real {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (C : Set ℝ) [CompactSpace C] (c₀ : C) (f : C → X) (hf : Continuous f) :
    ∃ τ : X → C, Measurable τ ∧ ∀ y ∈ Set.range f, f (τ y) = y := by
  have h : ∀ y : X, ∃ c : C, (y ∈ Set.range f → f c = y ∧ ∀ c', f c' = y → (c : ℝ) ≤ c') ∧
      (y ∉ Set.range f → c = c₀) := by
    intro y
    by_cases hy : y ∈ Set.range f
    · have hc : IsCompact (f ⁻¹' {y}) := (isClosed_singleton.preimage hf).isCompact
      obtain ⟨c, hc1, hc2⟩ := hc.exists_isMinOn (f := fun c : C => (c : ℝ)) hy
        continuous_subtype_val.continuousOn
      exact ⟨c, fun _ => ⟨hc1, fun c' h' => hc2 h'⟩, fun h => absurd hy h⟩
    · exact ⟨c₀, fun h => absurd h hy, fun _ => rfl⟩
  choose τ h1 h2 using h
  refine ⟨τ, ?_, fun y hy => (h1 y hy).1⟩
  have hm : Measurable fun y => (τ y : ℝ) := by
    refine measurable_of_Iic fun a => ?_
    have he : (fun y => (τ y : ℝ)) ⁻¹' Set.Iic a =
        f '' {c : C | (c : ℝ) ≤ a} ∪ ((Set.range f)ᶜ ∩ {_y | (c₀ : ℝ) ≤ a}) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_inter_iff,
        Set.mem_compl_iff, Set.mem_setOf_eq]
      by_cases hy : y ∈ Set.range f
      · constructor
        · intro h
          exact Or.inl ⟨τ y, h, (h1 y hy).1⟩
        · rintro (⟨c, hc, hcy⟩ | h)
          · exact ((h1 y hy).2 c hcy).trans hc
          · exact absurd hy h.1
      · rw [h2 y hy]
        constructor
        · intro h
          exact Or.inr ⟨hy, h⟩
        · rintro (⟨c, -, hcy⟩ | h)
          · exact absurd ⟨c, hcy⟩ hy
          · exact h.2
    rw [he]
    refine MeasurableSet.union ?_ (MeasurableSet.inter ?_ (MeasurableSet.const _))
    · exact ((isClosed_le continuous_subtype_val continuous_const).isCompact.image
        hf).isClosed.measurableSet
    · exact (isCompact_range hf).isClosed.measurableSet.compl
  exact hm.subtype_mk (h := fun y => (τ y).2)

/- English proof (translation)
Use `letI := TopologicalSpace.metrizableSpaceMetric K`. Take `⟨p, hp, hps⟩` from `exists_nat_bool_continuous_surjective_of_compact K`. Establish `: CompactSpace cantorSet` using `isCompact_iff_compactSpace.1 isCompact_cantorSet`. Set `q : cantorSet → K` to `p ∘ cantorSetHomeomorphNatToBool`. Establish `hq : Continuous q` using `hp.comp cantorSetHomeomorphNatToBool.continuous`.

Establish `hqs : Function.Surjective q` using `hps.comp cantorSetHomeomorphNatToBool.surjective`. Take `⟨τ, h1, h2⟩` from `exists_section_real cantorSet ⟨0, zero_mem_cantorSet⟩ (f ∘ q) (hf.comp hq)`. Use `⟨q ∘ τ, hq.measurable.comp h1, fun y hy => h2 y ?_⟩` and prove the remaining obligations. Rewrite using `[hqs.range_comp]` and apply the resulting hypothesis.
-/
theorem exists_section_compact {K X : Type} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    [TopologicalSpace.MetrizableSpace K] [MeasurableSpace K] [BorelSpace K]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (f : K → X) (hf : Continuous f) :
    ∃ τ : X → K, Measurable τ ∧ ∀ y ∈ Set.range f, f (τ y) = y := by
  letI := TopologicalSpace.metrizableSpaceMetric K
  obtain ⟨p, hp, hps⟩ := exists_nat_bool_continuous_surjective_of_compact K
  have : CompactSpace cantorSet := isCompact_iff_compactSpace.1 isCompact_cantorSet
  let q : cantorSet → K := p ∘ cantorSetHomeomorphNatToBool
  have hq : Continuous q := hp.comp cantorSetHomeomorphNatToBool.continuous
  have hqs : Function.Surjective q := hps.comp cantorSetHomeomorphNatToBool.surjective
  obtain ⟨τ, h1, h2⟩ := exists_section_real cantorSet ⟨0, zero_mem_cantorSet⟩ (f ∘ q)
    (hf.comp hq)
  refine ⟨q ∘ τ, hq.measurable.comp h1, fun y hy => h2 y ?_⟩
  rwa [hqs.range_comp]

/- English proof (translation)
Introduce `G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀`. Establish `hπ : Continuous fun g : G => g • x₀` using `by fun_prop`. Set `K : ℕ → Set G` to `fun n => insert 1 (compactCovering G n)`. Establish `hK : ∀ n, IsCompact (K n)` using `fun n => (isCompact_compactCovering G n).insert 1`. Establish `hKU : ∀ g : G, ∃ n, g ∈ K n` using `fun g => by`.

Take `⟨n, hn⟩` from `exists_mem_compactCovering g`. Conclude with `⟨n, Or.inr hn⟩`. Set `A : ℕ → Set X` to `fun n => (fun g : G => g • x₀) '' K n`. Establish `hA : ∀ n, MeasurableSet (A n)` using `fun n => ((hK n).image hπ).isClosed.measurableSet`. Establish `hO : MeasurableSet {y : X | ∃ g : G, g • x₀ = y}`.

Establish `: {y : X | ∃ g : G, g • x₀ = y} = ⋃ n, A n`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iUnion]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg⟩`.

Take `⟨n, hn⟩` from `hKU g`. Conclude with `⟨n, g, hn, hg⟩`. Introduce and unpack `⟨n, g, -, hg⟩`. Conclude with `⟨g, hg⟩`. Rewrite using `[this]`.

Conclude with `MeasurableSet.iUnion hA`. Establish `hs : ∀ n, ∃ s : X → G, Measurable s ∧ ∀ y ∈ A n, s y • x₀ = y`. Introduce `n`. Establish `: CompactSpace (K n)` using `isCompact_iff_compactSpace.1 (hK n)`. Establish `: Nonempty (K n)` using `⟨⟨1, Or.inl rfl⟩⟩`.

Take `⟨τ, h1, h2⟩` from `exists_section_compact (fun g : K n => (g : G) • x₀) (hπ.comp continuous_subtype_val)`. Use `⟨fun y => τ y, measurable_subtype_coe.comp h1, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨g, hg, hgy⟩`. Conclude with `h2 y ⟨⟨g, hg⟩, hgy⟩`. Use `choose s hs1 hs2 using hs`.

Establish `hex : ∀ y : X, ∃ n, (y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y)`. Introduce `y`. Distinguish the cases in `hy : ∃ g : G, g • x₀ = y`. Take `⟨g, hg⟩` from `hy`. Take `⟨n, hn⟩` from `hKU g`.

Conclude with `⟨n, Or.inl ⟨g, hn, hg⟩⟩`. Conclude with `⟨0, Or.inr hy⟩`. Use `⟨hO, fun y => s (Nat.find (hex y)) y, ?_, fun y hy => ?_⟩` and prove the remaining obligations. Conclude with `Measurable.find (p := fun n y => y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) hs1 (fun n => (hA n).union hO.compl) hex`. Conclude with `hs2 _ y ((Nat.find_spec (hex y)).resolve_right (not_not.2 hy))`.
-/
theorem measurableSet_orbit_and_exists_section : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousSMul G X] (x₀ : X), MeasurableSet {y : X | ∃ g : G, g • x₀ = y} ∧ ∃ s : X → G, Measurable s ∧ ∀ y, (∃ g : G, g • x₀ = y) → s y • x₀ = y := by
  intro G X _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x₀
  classical
  have hπ : Continuous fun g : G => g • x₀ := by fun_prop
  let K : ℕ → Set G := fun n => insert 1 (compactCovering G n)
  have hK : ∀ n, IsCompact (K n) := fun n => (isCompact_compactCovering G n).insert 1
  have hKU : ∀ g : G, ∃ n, g ∈ K n := fun g => by
    obtain ⟨n, hn⟩ := exists_mem_compactCovering g
    exact ⟨n, Or.inr hn⟩
  let A : ℕ → Set X := fun n => (fun g : G => g • x₀) '' K n
  have hA : ∀ n, MeasurableSet (A n) := fun n => ((hK n).image hπ).isClosed.measurableSet
  have hO : MeasurableSet {y : X | ∃ g : G, g • x₀ = y} := by
    have : {y : X | ∃ g : G, g • x₀ = y} = ⋃ n, A n := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨g, hg⟩
        obtain ⟨n, hn⟩ := hKU g
        exact ⟨n, g, hn, hg⟩
      · rintro ⟨n, g, -, hg⟩
        exact ⟨g, hg⟩
    rw [this]
    exact MeasurableSet.iUnion hA
  have hs : ∀ n, ∃ s : X → G, Measurable s ∧ ∀ y ∈ A n, s y • x₀ = y := by
    intro n
    have : CompactSpace (K n) := isCompact_iff_compactSpace.1 (hK n)
    have : Nonempty (K n) := ⟨⟨1, Or.inl rfl⟩⟩
    obtain ⟨τ, h1, h2⟩ := exists_section_compact (fun g : K n => (g : G) • x₀)
      (hπ.comp continuous_subtype_val)
    refine ⟨fun y => τ y, measurable_subtype_coe.comp h1, ?_⟩
    rintro y ⟨g, hg, hgy⟩
    exact h2 y ⟨⟨g, hg⟩, hgy⟩
  choose s hs1 hs2 using hs
  have hex : ∀ y : X, ∃ n, (y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) := by
    intro y
    by_cases hy : ∃ g : G, g • x₀ = y
    · obtain ⟨g, hg⟩ := hy
      obtain ⟨n, hn⟩ := hKU g
      exact ⟨n, Or.inl ⟨g, hn, hg⟩⟩
    · exact ⟨0, Or.inr hy⟩
  refine ⟨hO, fun y => s (Nat.find (hex y)) y, ?_, fun y hy => ?_⟩
  · exact Measurable.find (p := fun n y => y ∈ A n ∨ ¬ ∃ g : G, g • x₀ = y) hs1 (fun n => (hA n).union hO.compl) hex
  · exact hs2 _ y ((Nat.find_spec (hex y)).resolve_right (not_not.2 hy))

end GlobalTheory.OrbitSection
