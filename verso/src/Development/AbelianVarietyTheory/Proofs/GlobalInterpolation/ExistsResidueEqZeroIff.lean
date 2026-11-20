import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.ResidueBoxVolume

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl, hy⟩`. Rewrite `hy` using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Conclude with `lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).1 y.2) hy`. Introduce `hx`.

Use `⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 hx.le⟩, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Conclude with `hx.ne`.
-/
theorem _root_.GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    (∃ y : v.adicCompletionIntegers F, x = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0) ↔ Valued.v x < 1 := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hy
    exact lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).1 y.2) hy
  · intro hx
    refine ⟨⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).2 hx.le⟩, rfl, ?_⟩
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hx.ne

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`. Rewrite using `[Valued.mem_nhds]`. Use `⟨1, fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hx hy ⊢`.

Establish `hy' : y = (y - x) + x` using `by ring`. Rewrite using `[hy']`. Conclude with `Valuation.map_add_lt _ (by simpa using hy) hx`.
-/
theorem _root_.GlobalTheory.ResidueBoxVolume.isOpen_val_lt_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen {x : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | Valued.v x < 1} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [Valued.mem_nhds]
  refine ⟨1, fun y hy => ?_⟩
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hy' : y = (y - x) + x := by ring
  rw [hy']
  exact Valuation.map_add_lt _ (by simpa using hy) hx

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
/- English proof (translation)
Simplify using `only [Set.mem_singleton_iff, funext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, h1, h2⟩ i`. Conclude with `⟨y i, h1 i, h2 i⟩`. Introduce `h choose y hy1 hy2 using h`.

Conclude with `⟨y, hy1, hy2⟩`.
-/
private theorem mem_residue_box_singleton_iff (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (s : ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)) (x : V) :
    (∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)) ↔
    ∀ i, ∃ y : v.adicCompletionIntegers F, e x i = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = s i := by
  simp only [Set.mem_singleton_iff, funext_iff]
  constructor
  · rintro ⟨y, h1, h2⟩ i
    exact ⟨y i, h1 i, h2 i⟩
  · intro h
    choose y hy1 hy2 using h
    exact ⟨y, hy1, hy2⟩

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl, hy⟩`. Conclude with `⟨y - t, rfl, by rw [map_sub, hy, ht, sub_self]⟩`. Introduce and unpack `⟨y, hy, hy0⟩`. Use `⟨y + t, ?_, by rw [map_add, hy0, ht, zero_add]⟩` and prove the remaining obligations.

Use `show a = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) + (t : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)`. Rewrite using `[← hy]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_residue_eq_iff_exists_residue_sub_eq_zero {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    (c : IsLocalRing.ResidueField (v.adicCompletionIntegers F)) (t : v.adicCompletionIntegers F)
    (ht : IsLocalRing.residue (v.adicCompletionIntegers F) t = c) :
    (∃ y : v.adicCompletionIntegers F, a = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = c) ↔
    ∃ y : v.adicCompletionIntegers F, a - t = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ∧
      IsLocalRing.residue (v.adicCompletionIntegers F) y = 0 := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    exact ⟨y - t, rfl, by rw [map_sub, hy, ht, sub_self]⟩
  · rintro ⟨y, hy, hy0⟩
    refine ⟨y + t, ?_, by rw [map_add, hy0, ht, zero_add]⟩
    show a = (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) + (t : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)
    rw [← hy]
    ring

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
/- English proof (translation)
Use `choose t ht using fun i => IsLocalRing.residue_surjective (s i)`. Use `⟨-e.symm (fun i => (t i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)), ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, mem_residue_box_singleton_iff, Pi.zero_apply, map_add, map_neg, map_sub, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, ← sub_eq_add_neg]`. Conclude with `forall_congr' fun i => exists_residue_eq_iff_exists_residue_sub_eq_zero v _ _ _ (ht i)`.
-/
private theorem exists_residueBox_eq_preimage_add_lemma_2 (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (s : ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :
    ∃ w : V, {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)} =
      (fun x => x + w) ⁻¹' {x | ∃ y : ι → v.adicCompletionIntegers F,
        (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  choose t ht using fun i => IsLocalRing.residue_surjective (s i)
  refine ⟨-e.symm (fun i => (t i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)), ?_⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_residue_box_singleton_iff, Pi.zero_apply,
    map_add, map_neg, map_sub, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply,
    Pi.neg_apply, Pi.sub_apply, ← sub_eq_add_neg]
  exact forall_congr' fun i => exists_residue_eq_iff_exists_residue_sub_eq_zero v _ _ _ (ht i)

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
/- English proof (translation)
Establish `h : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} = ⋂ i, (fun x => e x i) ⁻¹' {a : _root_.Formalism.Mai …`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, mem_residue_box_singleton_iff, Pi.zero_apply, _root_.GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff]`. Rewrite using `[h]`. Conclude with `(isOpen_iInter_of_finite fun i => (_root_.GlobalTheory.ResidueBoxVolume.isOpen_val_lt_one v).preimage ((continuous_apply i).comp e.continuous)).measurableSet`.
-/
private theorem measurableSet_residue_box_zero (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) :
    MeasurableSet {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  have h : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} =
      ⋂ i, (fun x => e x i) ⁻¹' {a : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v | Valued.v a < 1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, mem_residue_box_singleton_iff,
      Pi.zero_apply, _root_.GlobalTheory.ResidueBoxVolume.exists_residue_eq_zero_iff]
  rw [h]
  exact (isOpen_iInter_of_finite fun i =>
    (_root_.GlobalTheory.ResidueBoxVolume.isOpen_val_lt_one v).preimage ((continuous_apply i).comp e.continuous)).measurableSet

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {V : Type}
  [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] {ι : Type} [Fintype ι] in
/- English proof (translation)
Use `haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := _root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v`. Establish `hS : S.Finite` using `S.toFinite`. Establish `hunion : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} = ⋃ s ∈ hS.toFinset, {x | ∃ y : ι → v.adicCompletionIntegers …`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_singleton_iff, exists_prop]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, h1, h2⟩`. Conclude with `⟨_, h2, y, h1, rfl⟩`. Introduce and unpack `⟨s, hs, y, h1, rfl⟩`. Conclude with `⟨y, h1, hs⟩`.

Rewrite using `[hunion, measure_biUnion_finset]`. Rewrite using `[Finset.sum_congr rfl fun s _ => ?_, Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card S hS]`. Take `⟨w, hw⟩` from `exists_residueBox_eq_preimage_add_lemma_2 e s`. Rewrite using `[hw, measure_preimage_add_right]`. Introduce `s _ s' _ hss'`.

Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce and unpack `x ⟨y, h1, h2⟩ ⟨y', h1', h2'⟩`. Apply `hss'` to reduce the goal to its premises. Establish `hyy : y = y'` using `funext fun i => Subtype.ext ((h1 i).symm.trans (h1' i))`. Substitute `hyy` using the available equality.

Rewrite `h2`, `h2'` using `[Set.mem_singleton_iff]`. Rewrite using `[← h2, ← h2']`. Introduce `s _`. Take `⟨w, hw⟩` from `exists_residueBox_eq_preimage_add_lemma_2 e s`. Rewrite using `[hw]`.

Conclude with `(measurableSet_residue_box_zero e).preimage (continuous_add_right w).measurable`.
-/
private theorem measure_residueBox_lemma (μ : Measure V) [μ.IsAddHaarMeasure]
    (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))
    (S : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    μ {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} =
    S.ncard * μ {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({0} : Set _)} := by
  classical
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    _root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hS : S.Finite := S.toFinite
  have hunion : {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
      (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} =
      ⋃ s ∈ hS.toFinset, {x | ∃ y : ι → v.adicCompletionIntegers F,
        (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ ({s} : Set _)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.Finite.mem_toFinset, Set.mem_singleton_iff,
      exists_prop]
    constructor
    · rintro ⟨y, h1, h2⟩
      exact ⟨_, h2, y, h1, rfl⟩
    · rintro ⟨s, hs, y, h1, rfl⟩
      exact ⟨y, h1, hs⟩
  rw [hunion, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun s _ => ?_, Finset.sum_const, nsmul_eq_mul,
      Set.ncard_eq_toFinset_card S hS]
    obtain ⟨w, hw⟩ := exists_residueBox_eq_preimage_add_lemma_2 e s
    rw [hw, measure_preimage_add_right]
  · intro s _ s' _ hss'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y, h1, h2⟩ ⟨y', h1', h2'⟩
    apply hss'
    have hyy : y = y' := funext fun i => Subtype.ext ((h1 i).symm.trans (h1' i))
    subst hyy
    rw [Set.mem_singleton_iff] at h2 h2'
    rw [← h2, ← h2']
  · intro s _
    obtain ⟨w, hw⟩ := exists_residueBox_eq_preimage_add_lemma_2 e s
    rw [hw]
    exact (measurableSet_residue_box_zero e).preimage (continuous_add_right w).measurable

open scoped TensorProduct in
open NumberField IsDedekindDomain MeasureTheory Topology in

/- English proof (translation)
Establish `hB : {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} = {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ Set.univ}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_univ, and_true]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨fun i => ⟨e x i, h i⟩, fun i => rfl⟩`. Introduce and unpack `⟨y, hy⟩ i`. Rewrite using `[hy i]`. Conclude with `(y i).2`. Rewrite using `[hB, measureReal_def, measureReal_def, measure_residueBox_lemma μ e Set.univ, measure_residueBox_lemma μ e S, Set.ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card (α := ι), ENNReal.toReal_mul, ENNReal.toReal_mul]`.

Simplify using `only [Nat.cast_pow, ENNReal.toReal_natCast, ENNReal.toReal_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.ResidueBoxVolume.measureReal_residueBox (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ι : Type) [Fintype ι] (e : V ≃L[_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v] (ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) (S : Set (ι → IsLocalRing.ResidueField (v.adicCompletionIntegers F))) :
    μ.real {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ S} * (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) : ℝ) ^ Fintype.card ι = (S.ncard : ℝ) * μ.real {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} := by
  have hB : {x | ∀ i, e x i ∈ v.adicCompletionIntegers F} =
      {x | ∃ y : ι → v.adicCompletionIntegers F, (∀ i, e x i = (y i : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
        (fun i => IsLocalRing.residue (v.adicCompletionIntegers F) (y i)) ∈ Set.univ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, and_true]
    constructor
    · intro h
      exact ⟨fun i => ⟨e x i, h i⟩, fun i => rfl⟩
    · rintro ⟨y, hy⟩ i
      rw [hy i]
      exact (y i).2
  rw [hB, measureReal_def, measureReal_def, measure_residueBox_lemma μ e Set.univ, measure_residueBox_lemma μ e S,
    Set.ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card (α := ι), ENNReal.toReal_mul,
    ENNReal.toReal_mul]
  simp only [Nat.cast_pow, ENNReal.toReal_natCast, ENNReal.toReal_pow]
  ring

end GlobalTheory.ResidueBoxVolume
