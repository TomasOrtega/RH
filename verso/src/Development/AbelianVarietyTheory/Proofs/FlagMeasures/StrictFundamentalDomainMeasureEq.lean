import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

/- English proof (translation)
Establish `h1 : μ D = μ (D ∩ NN)`. Rewrite using `[← measure_inter_add_diff D hNN]`. Establish `: μ (D \ NN) = 0` using `measure_mono_null (fun x hx => hx.2) hnull`. Rewrite using `[this, add_zero]`. Rewrite using `[h1]`.

Establish `hU : D ∩ NN = ⋃ g, D ∩ NN ∩ (ρ g)⁻¹' D'`. Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxD, hxN⟩`.

Take `⟨g, hg, -⟩` from `hu' x hxN`. Conclude with `⟨g, ⟨hxD, hxN⟩, hg⟩`. Introduce and unpack `⟨g, ⟨hxD, hxN⟩, -⟩`. Conclude with `⟨hxD, hxN⟩`. Use `conv_lhs => rw [hU]`.

Apply `measure_iUnion` to reduce the goal to its premises. Introduce `g h hgh`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce and unpack `x ⟨⟨-, hxN⟩, hg⟩ ⟨⟨-, -⟩, hh⟩`. Conclude with `hgh ((hu' x hxN).unique hg hh)`.

Introduce `g`. Conclude with `(hD.inter hNN).inter (hmeas g hD')`.
-/
theorem strictFD_measure_eq_tsum {G X : Type} [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hmeas : ∀ g, Measurable (ρ g)) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = ∑' g, μ (D ∩ NN ∩ (ρ g)⁻¹' D') := by
  have h1 : μ D = μ (D ∩ NN) := by
    rw [← measure_inter_add_diff D hNN]
    have : μ (D \ NN) = 0 := measure_mono_null (fun x hx => hx.2) hnull
    rw [this, add_zero]
  rw [h1]
  have hU : D ∩ NN = ⋃ g, D ∩ NN ∩ (ρ g)⁻¹' D' := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hxD, hxN⟩
      obtain ⟨g, hg, -⟩ := hu' x hxN
      exact ⟨g, ⟨hxD, hxN⟩, hg⟩
    · rintro ⟨g, ⟨hxD, hxN⟩, -⟩
      exact ⟨hxD, hxN⟩
  conv_lhs => rw [hU]
  apply measure_iUnion
  · intro g h hgh
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨⟨-, hxN⟩, hg⟩ ⟨⟨-, -⟩, hh⟩
    exact hgh ((hu' x hxN).unique hg hh)
  · intro g
    exact (hD.inter hNN).inter (hmeas g hD')

/- English proof (translation)
Establish `hmeas : ∀ g, Measurable (ρ g)` using `fun g => (hmp g).measurable`. Rewrite using `[strictFD_measure_eq_tsum μ ρ NN D D' hNN hnull hD hD' hmeas hu', strictFD_measure_eq_tsum μ ρ NN D' D hNN hnull hD' hD hmeas hu]`. Use `conv_rhs => rw [← (Equiv.inv G).tsum_eq]`. Use `tsum_congr fun g => ?_` and prove the remaining obligations. Simplify using `only [Equiv.inv_apply]`.

Establish `hS : MeasurableSet (D' ∩ NN ∩ (ρ g⁻¹)⁻¹' D)` using `(hD'.inter hNN).inter (hmeas g⁻¹ hD)`. Rewrite using `[← (hmp g).measure_preimage hS.nullMeasurableSet]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage]`.

Establish `hx : ρ g⁻¹ (ρ g x) = x` using `by rw [← hmul, inv_mul_cancel, hone]`. Rewrite using `[hx]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hxD, hxN⟩, hgx⟩`. Conclude with `⟨⟨hgx, hinv g x hxN⟩, hxD⟩`.

Introduce and unpack `⟨⟨hgx, hgxN⟩, hxD⟩`. Use `⟨⟨hxD, ?_⟩, hgx⟩` and prove the remaining obligations. Use `hinv g⁻¹ _ hgxN` as an intermediate fact. Rewrite `this` using `[hx]`. Then use the resulting hypothesis.
-/
theorem strictFD_measure_eq {G X : Type} [Group G] [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hone : ∀ x, ρ 1 x = x) (hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (hinv : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN) (hmp : ∀ g, MeasurePreserving (ρ g) μ μ)
    (hu : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = μ D' := by
  have hmeas : ∀ g, Measurable (ρ g) := fun g => (hmp g).measurable
  rw [strictFD_measure_eq_tsum μ ρ NN D D' hNN hnull hD hD' hmeas hu',
    strictFD_measure_eq_tsum μ ρ NN D' D hNN hnull hD' hD hmeas hu]
  conv_rhs => rw [← (Equiv.inv G).tsum_eq]
  refine tsum_congr fun g => ?_
  simp only [Equiv.inv_apply]
  have hS : MeasurableSet (D' ∩ NN ∩ (ρ g⁻¹)⁻¹' D) :=
    (hD'.inter hNN).inter (hmeas g⁻¹ hD)
  rw [← (hmp g).measure_preimage hS.nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  have hx : ρ g⁻¹ (ρ g x) = x := by rw [← hmul, inv_mul_cancel, hone]
  rw [hx]
  constructor
  · rintro ⟨⟨hxD, hxN⟩, hgx⟩
    exact ⟨⟨hgx, hinv g x hxN⟩, hxD⟩
  · rintro ⟨⟨hgx, hgxN⟩, hxD⟩
    refine ⟨⟨hxD, ?_⟩, hgx⟩
    have := hinv g⁻¹ _ hgxN
    rwa [hx] at this

/- English proof (translation)
The claim follows from `@strictFD_measure_eq`.
-/
example : ∀ {G X : Type} [Group G] [Countable G] [MeasurableSpace X] (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X), MeasurableSet NN → μ NNᶜ = 0 → MeasurableSet D → MeasurableSet D' → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ g, MeasurePreserving (ρ g) μ μ) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') → μ D = μ D' :=
  @strictFD_measure_eq

end GlobalTheory.SnMass.VolN
