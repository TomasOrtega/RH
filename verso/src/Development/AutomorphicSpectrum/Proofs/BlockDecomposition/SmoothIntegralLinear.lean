import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenFns

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier.SmIntEl

open MeasureTheory

/- English proof (translation)
Establish `: CompactSpace (tsupport φ)` using `isCompact_iff_compactSpace.mp hc`. Establish `h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite` using `(hl.comp_continuous continuous_subtype_val).range_finite`. Use `(h1.insert 0).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Distinguish the cases in `hx : x ∈ tsupport φ`.

Conclude with `Or.inr ⟨⟨x, hx⟩, rfl⟩`. Conclude with `Or.inl (image_eq_zero_of_notMem_tsupport hx)`.
-/
theorem finite_range {X W : Type} [TopologicalSpace X] [AddCommGroup W] {φ : X → W}
    (hl : IsLocallyConstant φ) (hc : HasCompactSupport φ) : (Set.range φ).Finite := by
  have : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp hc
  have h1 : (Set.range (φ ∘ ((↑) : tsupport φ → X))).Finite :=
    (hl.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport φ
  · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inl (image_eq_zero_of_notMem_tsupport hx)

/- English proof (translation)
Use `ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (IsCompact.measure_lt_top hc))` and prove the remaining obligations. Introduce `x hx`. Apply `subset_tsupport` to reduce the goal to its premises. Rewrite using `[Function.mem_support, show φ x = v from hx]`. Conclude with `hv`.
-/
theorem measure_level_ne_top {X W : Type} [TopologicalSpace X] [MeasurableSpace X] [AddCommGroup W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {φ : X → W} (hc : HasCompactSupport φ) {v : W}
    (hv : v ≠ 0) : μ (φ ⁻¹' {v}) ≠ ⊤ := by
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) (IsCompact.measure_lt_top hc))
  intro x hx
  apply subset_tsupport
  rw [Function.mem_support, show φ x = v from hx]
  exact hv

/- English proof (translation)
Establish `hsupp : (Function.support fun v : W => (((μ ((g ∘ ψ) ⁻¹' {v})).toReal : ℝ) : ℂ) • v) ⊆ ↑(S.image g)`. Introduce `v hv`. Assume the negation of the conclusion as `hvS`. Apply `hv` to reduce the goal to its premises. Establish `: (g ∘ ψ) ⁻¹' {v} = ∅`.

Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]`. Introduce `hx`. Conclude with `hvS (Finset.mem_coe.2 (Finset.mem_image.2 ⟨ψ x, hS x, hx⟩))`. Simplify using `[this]`.

Unfold `smInt`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g) (fun y hy => Finset.mem_image_of_mem g hy)]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Distinguish the cases in `hv0 : v = 0`. Substitute `hv0` using the available equality.

Rewrite using `[smul_zero]`. Use `symm`. Conclude with `Finset.sum_eq_zero fun y hy => by rw [(Finset.mem_filter.1 hy).2, smul_zero]`. Establish `hset : (g ∘ ψ) ⁻¹' {v} = ⋃ y ∈ S.filter (fun y => g y = v), ψ ⁻¹' {y}`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp, Set.mem_iUnion, Finset.mem_filter, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨ψ x, ⟨hS x, hx⟩, rfl⟩`. Introduce and unpack `⟨y, ⟨_, hy⟩, rfl⟩`.

Conclude with `hy`. Establish `hmeas : μ ((g ∘ ψ) ⁻¹' {v}) = ∑ y ∈ S.filter (fun y => g y = v), μ (ψ ⁻¹' {y})`. Rewrite using `[hset]`. Use `measure_biUnion_finset ?_ fun y hy => hm y (Finset.mem_filter.1 hy).1` and prove the remaining obligations. Introduce `a _ b _ hab`.

Conclude with `Disjoint.preimage ψ (Set.disjoint_singleton.2 hab)`. Rewrite using `[hmeas, ENNReal.toReal_sum (fun y hy => hf y (Finset.mem_filter.1 hy).1 (by rw [(Finset.mem_filter.1 hy).2]; exact hv0)), Complex.ofReal_sum, Finset.sum_smul]`. Conclude with `Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.1 hy).2]`.
-/
theorem smInt_comp {X Y W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W] (μ : Measure X)
    (ψ : X → Y) (g : Y → W) (S : Finset Y) (hS : ∀ x, ψ x ∈ S)
    (hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y})) (hf : ∀ y ∈ S, g y ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤) :
    smInt μ (g ∘ ψ) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • g y := by
  classical
  have hsupp : (Function.support fun v : W => (((μ ((g ∘ ψ) ⁻¹' {v})).toReal : ℝ) : ℂ) • v)
      ⊆ ↑(S.image g) := by
    intro v hv
    by_contra hvS
    apply hv
    have : (g ∘ ψ) ⁻¹' {v} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hvS (Finset.mem_coe.2 (Finset.mem_image.2 ⟨ψ x, hS x, hx⟩))
    simp [this]
  unfold smInt
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g)
      (fun y hy => Finset.mem_image_of_mem g hy)]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv0 : v = 0
  · subst hv0
    rw [smul_zero]
    symm
    exact Finset.sum_eq_zero fun y hy => by rw [(Finset.mem_filter.1 hy).2, smul_zero]
  · have hset : (g ∘ ψ) ⁻¹' {v} = ⋃ y ∈ S.filter (fun y => g y = v), ψ ⁻¹' {y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp, Set.mem_iUnion,
        Finset.mem_filter, exists_prop]
      constructor
      · intro hx
        exact ⟨ψ x, ⟨hS x, hx⟩, rfl⟩
      · rintro ⟨y, ⟨_, hy⟩, rfl⟩
        exact hy
    have hmeas : μ ((g ∘ ψ) ⁻¹' {v}) = ∑ y ∈ S.filter (fun y => g y = v), μ (ψ ⁻¹' {y}) := by
      rw [hset]
      refine measure_biUnion_finset ?_ fun y hy => hm y (Finset.mem_filter.1 hy).1
      intro a _ b _ hab
      exact Disjoint.preimage ψ (Set.disjoint_singleton.2 hab)
    rw [hmeas, ENNReal.toReal_sum (fun y hy => hf y (Finset.mem_filter.1 hy).1
      (by rw [(Finset.mem_filter.1 hy).2]; exact hv0)), Complex.ofReal_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun y hy => by rw [(Finset.mem_filter.1 hy).2]

/- English proof (translation)
Set `ψ : X → W × W` to `fun x => (φ₁ x, φ₂ x)`. Set `S : Finset (W × W)` to `(finite_range l₁ c₁).toFinset ×ˢ (finite_range l₂ c₂).toFinset`. Establish `hS : ∀ x, ψ x ∈ S` using `fun x => Finset.mem_product.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩, (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩⟩`. Establish `hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y})` using `fun y _ => ((l₁.prodMk l₂).isOpen_fiber y).measurableSet`. Establish `f₁ : ∀ y : W × W, y.1 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤` using `fun y hy => ne_top_of_le_ne_top (measure_level_ne_top μ c₁ hy) (measure_mono fun x hx => by show φ₁ x = y.1`.

Rewrite using `[← show ψ x = y from hx])`. Establish `f₂ : ∀ y : W × W, y.2 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤` using `fun y hy => ne_top_of_le_ne_top (measure_level_ne_top μ c₂ hy) (measure_mono fun x hx => by show φ₂ x = y.2`. Rewrite using `[← show ψ x = y from hx])`. Establish `e₀ : smInt μ (φ₁ + φ₂) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • (y.1 + y.2)` using `smInt_comp μ ψ (fun y => y.1 + y.2) S hS hm fun y _ hy => by`. Distinguish the cases in `h : y.1 = 0`.

Use `f₂ y fun h' => hy ?_ show y.1 + y.2 = 0` and prove the remaining obligations. Rewrite using `[h, h', add_zero]`. Conclude with `f₁ y h`. Establish `e₁ : smInt μ φ₁ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.1` using `smInt_comp μ ψ (fun y => y.1) S hS hm fun y _ hy => f₁ y hy`. Establish `e₂ : smInt μ φ₂ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.2` using `smInt_comp μ ψ (fun y => y.2) S hS hm fun y _ hy => f₂ y hy`.

Rewrite using `[e₀, e₁, e₂, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun y _ => smul_add _ _ _`.
-/
theorem smInt_add {X W : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup W] [Module ℂ W] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {φ₁ φ₂ : X → W}
    (l₁ : IsLocallyConstant φ₁) (c₁ : HasCompactSupport φ₁)
    (l₂ : IsLocallyConstant φ₂) (c₂ : HasCompactSupport φ₂) :
    smInt μ (φ₁ + φ₂) = smInt μ φ₁ + smInt μ φ₂ := by
  classical
  let ψ : X → W × W := fun x => (φ₁ x, φ₂ x)
  let S : Finset (W × W) := (finite_range l₁ c₁).toFinset ×ˢ (finite_range l₂ c₂).toFinset
  have hS : ∀ x, ψ x ∈ S := fun x =>
    Finset.mem_product.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩,
      (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩⟩
  have hm : ∀ y ∈ S, MeasurableSet (ψ ⁻¹' {y}) := fun y _ =>
    ((l₁.prodMk l₂).isOpen_fiber y).measurableSet
  have f₁ : ∀ y : W × W, y.1 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top (measure_level_ne_top μ c₁ hy) (measure_mono fun x hx => by
      show φ₁ x = y.1
      rw [← show ψ x = y from hx])
  have f₂ : ∀ y : W × W, y.2 ≠ 0 → μ (ψ ⁻¹' {y}) ≠ ⊤ := fun y hy =>
    ne_top_of_le_ne_top (measure_level_ne_top μ c₂ hy) (measure_mono fun x hx => by
      show φ₂ x = y.2
      rw [← show ψ x = y from hx])
  have e₀ : smInt μ (φ₁ + φ₂) = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • (y.1 + y.2) :=
    smInt_comp μ ψ (fun y => y.1 + y.2) S hS hm fun y _ hy => by
      by_cases h : y.1 = 0
      · refine f₂ y fun h' => hy ?_
        show y.1 + y.2 = 0
        rw [h, h', add_zero]
      · exact f₁ y h
  have e₁ : smInt μ φ₁ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.1 :=
    smInt_comp μ ψ (fun y => y.1) S hS hm fun y _ hy => f₁ y hy
  have e₂ : smInt μ φ₂ = ∑ y ∈ S, (((μ (ψ ⁻¹' {y})).toReal : ℝ) : ℂ) • y.2 :=
    smInt_comp μ ψ (fun y => y.2) S hS hm fun y _ hy => f₂ y hy
  rw [e₀, e₁, e₂, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => smul_add _ _ _

/- English proof (translation)
Set `S : Finset W` to `(finite_range l c).toFinset`. Establish `hS : ∀ x, φ x ∈ S` using `fun x => (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩`. Establish `hm : ∀ y ∈ S, MeasurableSet (φ ⁻¹' {y})` using `fun y _ => (l.isOpen_fiber y).measurableSet`. Establish `e₀ : smInt μ (T ∘ φ) = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • T y` using `smInt_comp μ φ T S hS hm fun y _ hy => measure_level_ne_top μ c fun h => hy (by rw [h, map_zero])`. Establish `e₁ : smInt μ φ = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • y` using `smInt_comp μ φ id S hS hm fun y _ hy => measure_level_ne_top μ c hy`.

Rewrite using `[e₀, e₁, map_sum]`. Conclude with `Finset.sum_congr rfl fun y _ => (map_smul T _ y).symm`.
-/
theorem smInt_linear {X W W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (T : W →ₗ[ℂ] W') {φ : X → W}
    (l : IsLocallyConstant φ) (c : HasCompactSupport φ) :
    smInt μ (T ∘ φ) = T (smInt μ φ) := by
  classical
  let S : Finset W := (finite_range l c).toFinset
  have hS : ∀ x, φ x ∈ S := fun x => (Set.Finite.mem_toFinset _).2 ⟨x, rfl⟩
  have hm : ∀ y ∈ S, MeasurableSet (φ ⁻¹' {y}) := fun y _ => (l.isOpen_fiber y).measurableSet
  have e₀ : smInt μ (T ∘ φ) = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • T y :=
    smInt_comp μ φ T S hS hm fun y _ hy =>
      measure_level_ne_top μ c fun h => hy (by rw [h, map_zero])
  have e₁ : smInt μ φ = ∑ y ∈ S, (((μ (φ ⁻¹' {y})).toReal : ℝ) : ℂ) • y :=
    smInt_comp μ φ id S hS hm fun y _ hy => measure_level_ne_top μ c hy
  rw [e₀, e₁, map_sum]
  exact Finset.sum_congr rfl fun y _ => (map_smul T _ y).symm

/- English proof (translation)
Unfold `smInt`. Use `finsum_congr fun v => ?_` and prove the remaining obligations. Establish `h : μ (c ⁻¹' (φ ⁻¹' {v})) = μ (φ ⁻¹' {v})` using `hc.measure_preimage (l.isOpen_fiber v).measurableSet.nullMeasurableSet`. Rewrite using `[Set.preimage_comp, h]`.
-/
theorem smInt_comp_measurePreserving {X W : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [AddCommGroup W] [Module ℂ W] (μ : Measure X) {c : X → X} {φ : X → W}
    (hc : MeasurePreserving c μ μ) (l : IsLocallyConstant φ) :
    smInt μ (φ ∘ c) = smInt μ φ := by
  unfold smInt
  refine finsum_congr fun v => ?_
  have h : μ (c ⁻¹' (φ ⁻¹' {v})) = μ (φ ⁻¹' {v}) :=
    hc.measure_preimage (l.isOpen_fiber v).measurableSet.nullMeasurableSet
  rw [Set.preimage_comp, h]

/- English proof (translation)
Unfold `smInt`. Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Rewrite using `[smul_zero]`. Use `finsum_eq_zero_of_forall_eq_zero fun w => ?_` and prove the remaining obligations.

Distinguish the cases in `hw : w = 0`. Rewrite using `[hw, smul_zero]`. Establish `: (A.indicator fun _ => (0 : W)) ⁻¹' {w} = ∅`. Use extensionality with `x`. Simplify using `[Set.indicator_zero', Ne.symm hw]`.

Rewrite using `[this, measure_empty]`. Simplify using the standard rewrite rules. Rewrite using `[finsum_eq_single _ v]`. Establish `: (A.indicator fun _ => v) ⁻¹' {v} = A`. Use extensionality with `x`.

Distinguish the cases in `hx : x ∈ A`. Simplify using `[hx]`. Simplify using `[hx, Ne.symm hv]`. Rewrite using `[this]`. Introduce `w hw`.

Distinguish the cases in `hw0 : w = 0`. Rewrite using `[hw0, smul_zero]`. Establish `: (A.indicator fun _ => v) ⁻¹' {w} = ∅`. Use extensionality with `x`. Distinguish the cases in `hx : x ∈ A`.

Simplify using `[hx, Ne.symm hw]`. Simplify using `[hx, Ne.symm hw0]`. Simplify using `[this]`.
-/
theorem smInt_indicator {X W : Type} [MeasurableSpace X] [AddCommGroup W] [Module ℂ W]
    (μ : Measure X) (A : Set X) (v : W) :
    smInt μ (A.indicator fun _ => v) = (((μ A).toReal : ℝ) : ℂ) • v := by
  classical
  unfold smInt
  by_cases hv : v = 0
  · subst hv
    rw [smul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    · have : (A.indicator fun _ => (0 : W)) ⁻¹' {w} = ∅ := by
        ext x
        simp [Set.indicator_zero', Ne.symm hw]
      rw [this, measure_empty]
      simp
  · rw [finsum_eq_single _ v]
    · have : (A.indicator fun _ => v) ⁻¹' {v} = A := by
        ext x
        by_cases hx : x ∈ A
        · simp [hx]
        · simp [hx, Ne.symm hv]
      rw [this]
    · intro w hw
      by_cases hw0 : w = 0
      · rw [hw0, smul_zero]
      · have : (A.indicator fun _ => v) ⁻¹' {w} = ∅ := by
          ext x
          by_cases hx : x ∈ A
          · simp [hx, Ne.symm hw]
          · simp [hx, Ne.symm hw0]
        simp [this]

/- English proof (translation)
Introduce `X W W' _ _ _ _ _ _ _ μ _`. Conclude with `⟨fun φ₁ φ₂ l₁ c₁ l₂ c₂ => smInt_add μ l₁ c₁ l₂ c₂, fun T φ l c => smInt_linear μ T l c, fun c φ hc l => smInt_comp_measurePreserving μ hc l, fun A v _ _ _ => smInt_indicator μ A v⟩`.
-/
theorem smInt_properties : ∀ {X W W' : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasureOnCompacts μ], (∀ φ₁ φ₂ : X → W, IsLocallyConstant φ₁ → HasCompactSupport φ₁ → IsLocallyConstant φ₂ → HasCompactSupport φ₂ → smInt μ (φ₁ + φ₂) = smInt μ φ₁ + smInt μ φ₂) ∧ (∀ (T : W →ₗ[ℂ] W') (φ : X → W), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (T ∘ φ) = T (smInt μ φ)) ∧ (∀ (c : X → X) (φ : X → W), MeasureTheory.MeasurePreserving c μ μ → IsLocallyConstant φ → smInt μ (φ ∘ c) = smInt μ φ) ∧ ∀ (A : Set X) (v : W), IsCompact A → IsOpen A → IsClosed A → smInt μ (A.indicator fun _ => v) = (((μ A).toReal : ℝ) : ℂ) • v := by
  intro X W W' _ _ _ _ _ _ _ μ _
  exact ⟨fun φ₁ φ₂ l₁ c₁ l₂ c₂ => smInt_add μ l₁ c₁ l₂ c₂,
    fun T φ l c => smInt_linear μ T l c,
    fun c φ hc l => smInt_comp_measurePreserving μ hc l,
    fun A v _ _ _ => smInt_indicator μ A v⟩

end GlobalTheory.CompanionTheory.Rodier.SmIntEl

end
