import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralFiberDecompositionInvariantStatement
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

/- English proof (translation)
Establish `hf : Continuous fun c : GL (Fin n) ℂ => ((g * c⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - 1` using `(Units.continuous_val.comp (continuous_const.mul continuous_inv)).sub continuous_const`. Establish `hK'` using `hK.image hf`. Establish `hemb : Topology.IsClosedEmbedding (Subtype.val : nilrad W₁ W₂ → Matrix (Fin n) (Fin n) ℂ)` using `(isClosed_nilrad W₁ W₂).isClosedEmbedding_subtypeVal`. Use `⟨_, hemb.isCompact_preimage hK', fun Y hY => ?_⟩` and prove the remaining obligations. Use `⟨(uOf Y)⁻¹ * g, hY, ?_⟩` and prove the remaining obligations.

Establish `: g * ((uOf Y)⁻¹ * g)⁻¹ = uOf Y` using `by group`. Simplify using `only [this, uOf_val, add_sub_cancel_left]`.
-/
theorem exists_isCompact_uOf_subset {n : ℕ} (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (g : GL (Fin n) ℂ) {K : Set (GL (Fin n) ℂ)} (hK : IsCompact K) :
    ∃ C : Set (nilrad W₁ W₂), IsCompact C ∧ {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * g ∈ K} ⊆ C := by
  have hf : Continuous fun c : GL (Fin n) ℂ =>
      ((g * c⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - 1 :=
    (Units.continuous_val.comp (continuous_const.mul continuous_inv)).sub continuous_const
  have hK' := hK.image hf
  have hemb : Topology.IsClosedEmbedding
      (Subtype.val : nilrad W₁ W₂ → Matrix (Fin n) (Fin n) ℂ) :=
    (isClosed_nilrad W₁ W₂).isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage hK', fun Y hY => ?_⟩
  refine ⟨(uOf Y)⁻¹ * g, hY, ?_⟩
  have : g * ((uOf Y)⁻¹ * g)⁻¹ = uOf Y := by group
  simp only [this, uOf_val, add_sub_cancel_left]

/- English proof (translation)
Establish `: nSet W₁ W₂ C = ⋃ X : nilrad W₁ W₂, (fun g => (uOf X)⁻¹ * g) ⁻¹' C`. Use extensionality with `g`. Simplify using `only [nSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨X, c, hc, rfl⟩`.

Conclude with `⟨X, by simpa using hc⟩`. Introduce and unpack `⟨X, hX⟩`. Conclude with `⟨X, _, hX, by simp⟩`. Rewrite using `[this]`. Conclude with `isOpen_iUnion fun X => hC.preimage (continuous_const.mul continuous_id)`.
-/
theorem isOpen_nSet {n : ℕ} (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {C : Set (GL (Fin n) ℂ)}
    (hC : IsOpen C) : IsOpen (nSet W₁ W₂ C) := by
  have : nSet W₁ W₂ C = ⋃ X : nilrad W₁ W₂, (fun g => (uOf X)⁻¹ * g) ⁻¹' C := by
    ext g
    simp only [nSet, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨X, c, hc, rfl⟩
      exact ⟨X, by simpa using hc⟩
    · rintro ⟨X, hX⟩
      exact ⟨X, _, hX, by simp⟩
  rw [this]
  exact isOpen_iUnion fun X => hC.preimage (continuous_const.mul continuous_id)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨X, c, hc, e⟩`. Use `⟨nmul hW h X, c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[uOf_nmul, mul_assoc, e]`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨X, c, hc, rfl⟩`. Use `⟨nmul hW (ninv hW h) X, c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[uOf_nmul, uOf_ninv, mul_assoc]`.
-/
theorem inv_mul_mem_nSet_iff {n : ℕ} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    (C : Set (GL (Fin n) ℂ)) (h : nilrad W₁ W₂) (x : GL (Fin n) ℂ) :
    (uOf h)⁻¹ * x ∈ nSet W₁ W₂ C ↔ x ∈ nSet W₁ W₂ C := by
  constructor
  · rintro ⟨X, c, hc, e⟩
    refine ⟨nmul hW h X, c, hc, ?_⟩
    rw [uOf_nmul, mul_assoc, e]
    simp
  · rintro ⟨X, c, hc, rfl⟩
    refine ⟨nmul hW (ninv hW h) X, c, hc, ?_⟩
    rw [uOf_nmul, uOf_ninv, mul_assoc]

/- English proof (translation)
Introduce `n _ _ W₁ W₂ hW _ _ ν _ hmp`. Use `haveI := locallyCompact_nilrad W₁ W₂`. Use `haveI := secondCountable_nilrad W₁ W₂`. Use `haveI := secondCountable_GL n`. Use `haveI := locallyCompact_GL n`.

Take `⟨U, hUo, hUc, hUcov⟩` from `exists_open_cover n`. Establish `hmeas : Measurable (fun p : nilrad W₁ W₂ × GL (Fin n) ℂ => (uOf p.1)⁻¹ * p.2)` using `(((continuous_uOf.comp continuous_fst).inv).mul continuous_snd).measurable`. Take `⟨ρ, hρm, hρ, -⟩` from `GlobalTheory.T.integral_fiber_decomposition_invariant ν (fun Y g => (uOf Y)⁻¹ * g) hmeas (nmul hW) hmp (fun h₀ h x => by simp only [uOf_nmul, _root_.mul_inv_rev, mul_assoc]) (fun i => closure (U i)) (fun i => nSet W₁ W₂ (U i)) (fun i => isClosed_closure.measurableSet) (fun i => ( …`. Take `⟨i, hi⟩` from `hUcov x`. Conclude with `⟨i, 0, x, hi, by`.

Establish `: uOf (0 : nilrad W₁ W₂) = 1` using `Units.ext (by simp)`. Simplify using `[this]⟩)`. Use the proof step `(fun i x => by`. Take `⟨C, hC, hsub⟩` from `exists_isCompact_uOf_subset W₁ W₂ x (hUc i)`. Conclude with `((measure_mono hsub).trans_lt hC.measure_lt_top).ne)`.

Use the proof step `(fun i x hx => by`. Take `⟨Y₀, c, hc, rfl⟩` from `hx`. Establish `ho : IsOpen {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i}` using `(hUo i).preimage ((continuous_uOf.inv).mul continuous_const)`. Establish `hne : ({Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i}).Nonempty` using `⟨Y₀, by simpa using hc⟩`. Establish `hpos` using `ho.measure_pos ν hne`.

Establish `hsub : {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i} ⊆ {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ closure (U i)}` using `fun Y hY => subset_closure hY`. Conclude with `(hpos.trans_le (measure_mono hsub)).ne')`. Use the proof step `∅ (by simp) (by simp) (by simp)`. Conclude with `⟨ρ, hρm, hρ⟩`.
-/
theorem exists_nilrad_normaliser : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
  (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure],
  (∀ Y : nilrad W₁ W₂, MeasurePreserving (nmul hW Y) ν ν) →
  ∃ w : GL (Fin n) ℂ → ℝ≥0∞, Measurable w ∧
    ∀ g : GL (Fin n) ℂ, ∫⁻ X, w ((uOf X)⁻¹ * g) ∂ν = 1 := by
  intro n _ _ W₁ W₂ hW _ _ ν _ hmp
  haveI := locallyCompact_nilrad W₁ W₂
  haveI := secondCountable_nilrad W₁ W₂
  haveI := secondCountable_GL n
  haveI := locallyCompact_GL n
  obtain ⟨U, hUo, hUc, hUcov⟩ := exists_open_cover n
  have hmeas : Measurable (fun p : nilrad W₁ W₂ × GL (Fin n) ℂ => (uOf p.1)⁻¹ * p.2) :=
    (((continuous_uOf.comp continuous_fst).inv).mul continuous_snd).measurable
  obtain ⟨ρ, hρm, hρ, -⟩ := GlobalTheory.T.integral_fiber_decomposition_invariant ν (fun Y g => (uOf Y)⁻¹ * g) hmeas (nmul hW) hmp
    (fun h₀ h x => by simp only [uOf_nmul, _root_.mul_inv_rev, mul_assoc])
    (fun i => closure (U i)) (fun i => nSet W₁ W₂ (U i))
    (fun i => isClosed_closure.measurableSet)
    (fun i => (isOpen_nSet W₁ W₂ (hUo i)).measurableSet)
    (fun i h x => inv_mul_mem_nSet_iff hW (U i) h x)
    (fun x => by
      obtain ⟨i, hi⟩ := hUcov x
      exact ⟨i, 0, x, hi, by
        have : uOf (0 : nilrad W₁ W₂) = 1 := Units.ext (by simp)
        simp [this]⟩)
    (fun i x => by
      obtain ⟨C, hC, hsub⟩ := exists_isCompact_uOf_subset W₁ W₂ x (hUc i)
      exact ((measure_mono hsub).trans_lt hC.measure_lt_top).ne)
    (fun i x hx => by
      obtain ⟨Y₀, c, hc, rfl⟩ := hx
      have ho : IsOpen {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i} :=
        (hUo i).preimage ((continuous_uOf.inv).mul continuous_const)
      have hne : ({Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i}).Nonempty :=
        ⟨Y₀, by simpa using hc⟩
      have hpos := ho.measure_pos ν hne
      have hsub : {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ U i} ⊆
          {Y : nilrad W₁ W₂ | (uOf Y)⁻¹ * (uOf Y₀ * c) ∈ closure (U i)} :=
        fun Y hY => subset_closure hY
      exact (hpos.trans_le (measure_mono hsub)).ne')
    ∅ (by simp) (by simp) (by simp)
  exact ⟨ρ, hρm, hρ⟩

end GlobalTheory.CompanionTheory.LocVan
