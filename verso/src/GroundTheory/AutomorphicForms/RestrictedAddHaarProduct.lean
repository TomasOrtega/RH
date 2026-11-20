import Mathlib
import GroundTheory.AutomorphicForms.RestrictedHaarProduct

open MeasureTheory Filter Set Topology
open scoped ENNReal RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

namespace RestrictedAddHaar

set_option linter.unusedSectionVars false

variable {ι : Type*} {G : ι → Type*} [∀ i, AddGroup (G i)] (C : ∀ i, AddSubgroup (G i))

def box (T : Finset ι) : AddSubgroup (Πʳ i, [G i, (C i : Set (G i))]) where
  carrier := {x | ∀ i, i ∉ T → x i ∈ C i}
  zero_mem' i _ := by
    show (0 : Πʳ i, [G i, (C i : Set (G i))]) i ∈ C i
    rw [RestrictedProduct.zero_apply]
    exact (C i).zero_mem
  add_mem' {x y} hx hy i hi := by
    show (x + y) i ∈ C i
    rw [RestrictedProduct.add_apply]
    exact (C i).add_mem (hx i hi) (hy i hi)
  neg_mem' {x} hx i hi := by
    show (-x) i ∈ C i
    rw [RestrictedProduct.neg_apply]
    exact (C i).neg_mem (hx i hi)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_box {T : Finset ι} {x : Πʳ i, [G i, (C i : Set (G i))]} :
    x ∈ box C T ↔ ∀ i, i ∉ T → x i ∈ C i := Iff.rfl

/- English proof (translation)
The claim follows from `fun _ hx i hi ↦ hx i fun hiT ↦ hi (h hiT)`.
-/
theorem box_mono {T T' : Finset ι} (h : T ⊆ T') : box C T ≤ box C T' :=
  fun _ hx i hi ↦ hx i fun hiT ↦ hi (h hiT)

/- English proof (translation)
Establish `hx : {i | ¬ x i ∈ C i}.Finite` using `Filter.eventually_cofinite.1 x.2`. Use `⟨hx.toFinset, fun i hi ↦ ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hi (hx.mem_toFinset.2 h)`.
-/
theorem exists_mem_box (x : Πʳ i, [G i, (C i : Set (G i))]) : ∃ T : Finset ι, x ∈ box C T := by
  have hx : {i | ¬ x i ∈ C i}.Finite := Filter.eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, fun i hi ↦ ?_⟩
  by_contra h
  exact hi (hx.mem_toFinset.2 h)

def proj (T : Finset ι) : (Πʳ i, [G i, (C i : Set (G i))]) →+ ((i : T) → G i) where
  toFun x i := x i
  map_zero' := by
    funext i
    show (0 : Πʳ i, [G i, (C i : Set (G i))]) (i : ι) = 0
    rw [RestrictedProduct.zero_apply]
  map_add' x y := by
    funext i
    show (x + y) (i : ι) = x i + y i
    rw [RestrictedProduct.add_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem proj_apply (T : Finset ι) (x : Πʳ i, [G i, (C i : Set (G i))]) (i : T) : proj C T x i = x i := rfl

open Classical in

def secFun (T : Finset ι) (a : (i : T) → G i) (i : ι) : G i := if h : i ∈ T then a ⟨i, h⟩ else 0

/- English proof (translation)
Unfold `secFun`. Rewrite using `[dif_pos h]`.
-/
theorem secFun_of_mem {T : Finset ι} (a : (i : T) → G i) {i : ι} (h : i ∈ T) :
    secFun T a i = a ⟨i, h⟩ := by
  classical
  unfold secFun
  rw [dif_pos h]

/- English proof (translation)
Unfold `secFun`. Rewrite using `[dif_neg h]`.
-/
theorem secFun_of_notMem {T : Finset ι} (a : (i : T) → G i) {i : ι} (h : i ∉ T) :
    secFun T a i = 0 := by
  classical
  unfold secFun
  rw [dif_neg h]

def sec (T : Finset ι) : ((i : T) → G i) →+ (Πʳ i, [G i, (C i : Set (G i))]) where
  toFun a := ⟨secFun T a, by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with i hi
    rw [secFun_of_notMem a (show i ∉ T from hi)]
    exact (C i).zero_mem⟩
  map_zero' := by
    refine RestrictedProduct.ext _ _ fun i ↦ ?_
    show secFun T 0 i = (0 : Πʳ i, [G i, (C i : Set (G i))]) i
    rw [RestrictedProduct.zero_apply]
    by_cases h : i ∈ T
    · rw [secFun_of_mem _ h]
      rfl
    · rw [secFun_of_notMem _ h]
  map_add' a b := by
    refine RestrictedProduct.ext _ _ fun i ↦ ?_
    show secFun T (a + b) i = secFun T a i + secFun T b i
    by_cases h : i ∈ T
    · rw [secFun_of_mem _ h, secFun_of_mem _ h, secFun_of_mem _ h]
      rfl
    · rw [secFun_of_notMem _ h, secFun_of_notMem _ h, secFun_of_notMem _ h, zero_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sec_apply (T : Finset ι) (a : (i : T) → G i) (i : ι) : sec C T a i = secFun T a i := rfl

/- English proof (translation)
Introduce `i hi`. Rewrite using `[sec_apply, secFun_of_notMem a hi]`. Conclude with `(C i).zero_mem`.
-/
theorem sec_mem_box (T : Finset ι) (a : (i : T) → G i) : sec C T a ∈ box C T := by
  intro i hi
  rw [sec_apply, secFun_of_notMem a hi]
  exact (C i).zero_mem

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[proj_apply, sec_apply, secFun_of_mem a i.2]`.
-/
theorem proj_sec (T : Finset ι) (a : (i : T) → G i) : proj C T (sec C T a) = a := by
  funext i
  rw [proj_apply, sec_apply, secFun_of_mem a i.2]

variable [∀ i, TopologicalSpace (G i)]

/- English proof (translation)
The claim follows from `continuous_pi fun i ↦ RestrictedProduct.continuous_eval (i : ι)`.
-/
theorem continuous_proj (T : Finset ι) : Continuous (proj C T) :=
  continuous_pi fun i ↦ RestrictedProduct.continuous_eval (i : ι)

/- English proof (translation)
The claim follows from `RestrictedProduct.isOpen_forall_imp_mem (R := G) (A := fun i ↦ (C i : Set (G i))) hCo (p := fun i ↦ i ∉ T)`.
-/
theorem isOpen_box (hCo : ∀ i, IsOpen (C i : Set (G i))) (T : Finset ι) :
    IsOpen (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) :=
  RestrictedProduct.isOpen_forall_imp_mem (R := G) (A := fun i ↦ (C i : Set (G i))) hCo
    (p := fun i ↦ i ∉ T)

/- English proof (translation)
Use `set S : Set ι := (↑T)ᶜ with hSdef`. Establish `hS : cofinite ≤ 𝓟 S` using `le_principal_iff.2 T.finite_toSet.compl_mem_cofinite`. Use `set W : Set ((i : ι) → G i) := {x | (fun i : T ↦ x i) ∈ E} ∩ {x | ∀ i ∈ S, x i ∈ C i} with hW`. Establish `hWc : IsCompact W`. Establish `hbig : IsCompact (Set.univ.pi fun i ↦ if h : i ∈ T then (fun a : (j : T) → G j ↦ a ⟨i, h⟩) '' E else (C i : Set (G i)))`.

Use `isCompact_univ_pi fun i ↦ ?_` and prove the remaining obligations. Use `split_ifs with h`. Conclude with `hE.image (continuous_apply _)`. Conclude with `hCc i`. Use `hbig.of_isClosed_subset ?_ ?_` and prove the remaining obligations.

Use `IsClosed.inter (hE.isClosed.preimage (continuous_pi fun i ↦ continuous_apply _)) ?_` and prove the remaining obligations. Simplify using `only [Set.ofPred_forall]`. Conclude with `isClosed_biInter fun i _ ↦ (AddSubgroup.isClosed_of_isOpen (C i) (hCo i)).preimage (continuous_apply i)`. Introduce and unpack `x ⟨hxE, hxS⟩ i -`. Distinguish the cases in `h : i ∈ T`.

Simplify using `only`. Rewrite using `[dif_pos h]`. Conclude with `⟨_, hxE, rfl⟩`. Simplify using `only`. Rewrite using `[dif_neg h]`.

Conclude with `hxS i h`. Use `set Z : Set (Πʳ i, [G i, (C i : Set (G i))]_[𝓟 S]) := (fun y ↦ (y : (i : ι) → G i)) ⁻¹' W with hZ`. Establish `hZc : IsCompact Z`. Rewrite using `[(RestrictedProduct.isEmbedding_coe_of_principal (R := G) (A := fun i ↦ (C i : Set (G i))) (S := S)).isCompact_iff, hZ, image_preimage_eq_inter_range, RestrictedProduct.range_coe_principal]`. Rewrite using `[inter_eq_left.2 fun x hx ↦ hx.2]`.

Conclude with `hWc`. Establish `heq : (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' E = RestrictedProduct.inclusion G (fun i ↦ (C i : Set (G i))) hS '' Z`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxb, hxE⟩`.

Use `⟨⟨x.1, Filter.eventually_principal.2 fun i hi ↦ hxb i hi⟩, ⟨hxE, fun i hi ↦ hxb i hi⟩, ?_⟩` and prove the remaining obligations. Conclude with `RestrictedProduct.ext _ _ fun i ↦ rfl`. Introduce and unpack `⟨y, ⟨hyE, hyS⟩, rfl⟩`. Conclude with `⟨fun i hi ↦ hyS i hi, hyE⟩`. Rewrite using `[heq]`.

Conclude with `hZc.image (RestrictedProduct.continuous_inclusion hS)`.
-/
theorem isCompact_box_inter_preimage [∀ i, IsTopologicalAddGroup (G i)] [∀ i, T2Space (G i)] (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) (T : Finset ι) {E : Set ((i : T) → G i)}
    (hE : IsCompact E) :
    IsCompact ((box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' E) := by
  classical
  set S : Set ι := (↑T)ᶜ with hSdef
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 T.finite_toSet.compl_mem_cofinite
  set W : Set ((i : ι) → G i) := {x | (fun i : T ↦ x i) ∈ E} ∩ {x | ∀ i ∈ S, x i ∈ C i} with hW
  have hWc : IsCompact W := by
    have hbig : IsCompact (Set.univ.pi fun i ↦
        if h : i ∈ T then (fun a : (j : T) → G j ↦ a ⟨i, h⟩) '' E else (C i : Set (G i))) := by
      refine isCompact_univ_pi fun i ↦ ?_
      split_ifs with h
      · exact hE.image (continuous_apply _)
      · exact hCc i
    refine hbig.of_isClosed_subset ?_ ?_
    · refine IsClosed.inter (hE.isClosed.preimage (continuous_pi fun i ↦ continuous_apply _)) ?_
      simp only [Set.ofPred_forall]
      exact isClosed_biInter fun i _ ↦
        (AddSubgroup.isClosed_of_isOpen (C i) (hCo i)).preimage (continuous_apply i)
    · rintro x ⟨hxE, hxS⟩ i -
      by_cases h : i ∈ T
      · dsimp only
        rw [dif_pos h]
        exact ⟨_, hxE, rfl⟩
      · dsimp only
        rw [dif_neg h]
        exact hxS i h
  set Z : Set (Πʳ i, [G i, (C i : Set (G i))]_[𝓟 S]) := (fun y ↦ (y : (i : ι) → G i)) ⁻¹' W with hZ
  have hZc : IsCompact Z := by
    rw [(RestrictedProduct.isEmbedding_coe_of_principal (R := G) (A := fun i ↦ (C i : Set (G i)))
      (S := S)).isCompact_iff, hZ, image_preimage_eq_inter_range, RestrictedProduct.range_coe_principal]
    rw [inter_eq_left.2 fun x hx ↦ hx.2]
    exact hWc
  have heq : (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' E =
      RestrictedProduct.inclusion G (fun i ↦ (C i : Set (G i))) hS '' Z := by
    ext x
    constructor
    · rintro ⟨hxb, hxE⟩
      refine ⟨⟨x.1, Filter.eventually_principal.2 fun i hi ↦ hxb i hi⟩, ⟨hxE, fun i hi ↦ hxb i hi⟩, ?_⟩
      exact RestrictedProduct.ext _ _ fun i ↦ rfl
    · rintro ⟨y, ⟨hyE, hyS⟩, rfl⟩
      exact ⟨fun i hi ↦ hyS i hi, hyE⟩
  rw [heq]
  exact hZc.image (RestrictedProduct.continuous_inclusion hS)

section Measure

variable [∀ i, IsTopologicalAddGroup (G i)] [∀ i, T2Space (G i)] [∀ i, SecondCountableTopology (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [MeasurableSpace (Πʳ i, [G i, (C i : Set (G i))])] [BorelSpace (Πʳ i, [G i, (C i : Set (G i))])]

def projMeasure (μ : Measure (Πʳ i, [G i, (C i : Set (G i))])) (T : Finset ι) :
    Measure ((i : T) → G i) :=
  (μ.restrict (box C T : Set (Πʳ i, [G i, (C i : Set (G i))]))).map (proj C T)

/- English proof (translation)
Establish `hm : Measurable (proj C T)` using `(continuous_proj C T).measurable`. Rewrite using `[projMeasure, Measure.map_apply hm hE, Measure.restrict_apply (hm hE), inter_comm]`.
-/
theorem projMeasure_apply (μ : Measure (Πʳ i, [G i, (C i : Set (G i))]))
    (T : Finset ι) {E : Set ((i : T) → G i)} (hE : MeasurableSet E) :
    projMeasure C μ T E = μ ((box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' E) := by
  have hm : Measurable (proj C T) := (continuous_proj C T).measurable
  rw [projMeasure, Measure.map_apply hm hE, Measure.restrict_apply (hm hE), inter_comm]

/- English proof (translation)
Use `{ lt_top_of_isCompact := fun K hK ↦ ?_, map_add_left_eq_self := fun a ↦ ?_, open_pos := fun U hU hne ↦ ?_ }` and prove the remaining obligations. Rewrite using `[projMeasure_apply C μ T hK.isClosed.measurableSet]`. Conclude with `(isCompact_box_inter_preimage C hCo hCc T hK).measure_lt_top`. Use extensionality with `E hE`. Rewrite using `[Measure.map_apply (measurable_const_add a) hE, projMeasure_apply C μ T (measurable_const_add a hE), projMeasure_apply C μ T hE]`.

Establish `hset : (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' ((a + ·) ⁻¹' E) = (sec C T a + ·) ⁻¹' ((box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' E)`. Use extensionality with `x`. Simplify using `only [mem_inter_iff, mem_preimage, SetLike.mem_coe, map_add, proj_sec]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hxE⟩`.

Conclude with `⟨(box C T).add_mem (sec_mem_box C T a) hx, hxE⟩`. Introduce and unpack `⟨hx, hxE⟩`. Use `⟨?_, hxE⟩` and prove the remaining obligations. Use `(box C T).add_mem ((box C T).neg_mem (sec_mem_box C T a)) hx` as an intermediate fact. Rewrite `this` using `[neg_add_cancel_left]`. Then use the resulting hypothesis.

Establish `: Fact (∀ i, IsOpen (C i : Set (G i)))` using `⟨hCo⟩`. Establish `: MeasurableAdd (Πʳ i, [G i, (C i : Set (G i))])` using `⟨fun c ↦ (continuous_const_add c).measurable, fun c ↦ (continuous_add_const c).measurable⟩`. Rewrite using `[hset, measure_preimage_add]`. Rewrite using `[projMeasure_apply C μ T hU.measurableSet]`. Take `⟨a, ha⟩` from `hne`.

Use `((isOpen_box C hCo T).inter (hU.preimage (continuous_proj C T))).measure_ne_zero μ ⟨sec C T a, sec_mem_box C T a, ?_⟩` and prove the remaining obligations. Use `show proj C T (sec C T a) ∈ U`. Rewrite using `[proj_sec]`. Conclude with `ha`.
-/
theorem isHaarMeasure_projMeasure (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) (μ : Measure (Πʳ i, [G i, (C i : Set (G i))]))
    [μ.IsAddHaarMeasure] (T : Finset ι) : (projMeasure C μ T).IsAddHaarMeasure := by
  refine { lt_top_of_isCompact := fun K hK ↦ ?_, map_add_left_eq_self := fun a ↦ ?_,
           open_pos := fun U hU hne ↦ ?_ }
  · rw [projMeasure_apply C μ T hK.isClosed.measurableSet]
    exact (isCompact_box_inter_preimage C hCo hCc T hK).measure_lt_top
  · ext E hE
    rw [Measure.map_apply (measurable_const_add a) hE,
      projMeasure_apply C μ T (measurable_const_add a hE), projMeasure_apply C μ T hE]
    have hset : (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' ((a + ·) ⁻¹' E) =
        (sec C T a + ·) ⁻¹' ((box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' E) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, SetLike.mem_coe, map_add, proj_sec]
      constructor
      · rintro ⟨hx, hxE⟩
        exact ⟨(box C T).add_mem (sec_mem_box C T a) hx, hxE⟩
      · rintro ⟨hx, hxE⟩
        refine ⟨?_, hxE⟩
        have := (box C T).add_mem ((box C T).neg_mem (sec_mem_box C T a)) hx
        rwa [neg_add_cancel_left] at this
    have : Fact (∀ i, IsOpen (C i : Set (G i))) := ⟨hCo⟩
    have : MeasurableAdd (Πʳ i, [G i, (C i : Set (G i))]) :=
      ⟨fun c ↦ (continuous_const_add c).measurable, fun c ↦ (continuous_add_const c).measurable⟩
    rw [hset, measure_preimage_add]
  · rw [projMeasure_apply C μ T hU.measurableSet]
    obtain ⟨a, ha⟩ := hne
    refine ((isOpen_box C hCo T).inter (hU.preimage (continuous_proj C T))).measure_ne_zero μ
      ⟨sec C T a, sec_mem_box C T a, ?_⟩
    show proj C T (sec C T a) ∈ U
    rw [proj_sec]
    exact ha

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_ofPred_eq, mem_inter_iff, SetLike.mem_coe, mem_box, Finset.notMem_empty, not_false_eq_true, true_implies, mem_preimage, mem_univ, and_true]`.
-/
theorem setOf_forall_mem_eq :
    {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} =
      (box C ∅ : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C ∅ ⁻¹' univ := by
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, SetLike.mem_coe, mem_box, Finset.notMem_empty,
    not_false_eq_true, true_implies, mem_preimage, mem_univ, and_true]

/- English proof (translation)
Rewrite using `[setOf_forall_mem_eq]`. Use `isCompact_box_inter_preimage C hCo hCc ∅ ?_` and prove the remaining obligations. Conclude with `Set.Subsingleton.isCompact fun a _ b _ ↦ funext fun i ↦ absurd i.2 (Finset.notMem_empty _)`.
-/
theorem isCompact_setOf_forall_mem (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) :
    IsCompact {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} := by
  rw [setOf_forall_mem_eq]
  refine isCompact_box_inter_preimage C hCo hCc ∅ ?_
  exact Set.Subsingleton.isCompact fun a _ b _ ↦ funext fun i ↦ absurd i.2 (Finset.notMem_empty _)

/- English proof (translation)
Establish `h : {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} = (box C ∅ : Set (Πʳ i, [G i, (C i : Set (G i))]))`. Use extensionality with `x`. Simplify using `[mem_box]`. Rewrite using `[h]`. Conclude with `(isOpen_box C hCo ∅).measure_pos μ ⟨0, (box C ∅).zero_mem⟩`.
-/
theorem measure_setOf_forall_mem_pos (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (μ : Measure (Πʳ i, [G i, (C i : Set (G i))])) [μ.IsAddHaarMeasure] :
    0 < μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} := by
  have h : {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} =
      (box C ∅ : Set (Πʳ i, [G i, (C i : Set (G i))])) := by
    ext x
    simp [mem_box]
  rw [h]
  exact (isOpen_box C hCo ∅).measure_pos μ ⟨0, (box C ∅).zero_mem⟩

/- English proof (translation)
The claim follows from `ENNReal.toReal_pos (measure_setOf_forall_mem_pos C hCo μ).ne' (isCompact_setOf_forall_mem C hCo hCc).measure_lt_top.ne`.
-/
theorem measureReal_setOf_forall_mem_pos (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) (μ : Measure (Πʳ i, [G i, (C i : Set (G i))]))
    [μ.IsAddHaarMeasure] :
    0 < μ.real {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} :=
  ENNReal.toReal_pos (measure_setOf_forall_mem_pos C hCo μ).ne'
    (isCompact_setOf_forall_mem C hCo hCc).measure_lt_top.ne

variable [∀ i, LocallyCompactSpace (G i)]

/- English proof (translation)
Use `isHaarMeasure_projMeasure C hCo hCc μ T` as an intermediate fact. Establish `h` using `Measure.isAddLeftInvariant_eq_smul (projMeasure C μ T) (Measure.pi fun i : T ↦ ν i)`. Use `set B : Set ((i : T) → G i) := Set.univ.pi fun i ↦ (C i : Set (G i)) with hBdef`. Establish `hB : MeasurableSet B` using `MeasurableSet.univ_pi fun i ↦ (hCo i).measurableSet`. Establish `hpi : Measure.pi (fun i : T ↦ ν i) B = 1`.

Rewrite using `[hBdef, Measure.pi_pi]`. Simplify using `[hν]`. Establish `hproj : projMeasure C μ T B = μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i}`. Rewrite using `[projMeasure_apply C μ T hB]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [hBdef, mem_inter_iff, mem_preimage, Set.mem_pi, mem_univ, true_implies, SetLike.mem_coe, mem_ofPred_eq, mem_box, proj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩ i`. Distinguish the cases in `hi : i ∈ T`.

Conclude with `h2 ⟨i, hi⟩`. Conclude with `h1 i hi`. Introduce `h`. Conclude with `⟨fun i _ ↦ h i, fun i ↦ h i⟩`. Establish `hc : ((projMeasure C μ T).addHaarScalarFactor (Measure.pi fun i : T ↦ ν i) : ℝ≥0∞) = μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i}`.

Use `congrArg (fun m : Measure ((i : T) → G i) ↦ m B) h` as an intermediate fact. Simplify using `only [Measure.smul_apply, hpi, ENNReal.smul_def, smul_eq_mul, mul_one] at this`. Rewrite using `[← hproj, this]`. Use `conv_lhs => rw [h]`. Rewrite using `[← hc]`.

Both sides reduce to the same expression.
-/
theorem projMeasure_eq (hCo : ∀ i, IsOpen (C i : Set (G i))) (hCc : ∀ i, IsCompact (C i : Set (G i)))
    (μ : Measure (Πʳ i, [G i, (C i : Set (G i))])) [μ.IsAddHaarMeasure] (ν : ∀ i, Measure (G i))
    [∀ i, (ν i).IsAddHaarMeasure] (hν : ∀ i, ν i (C i) = 1) (T : Finset ι) :
    projMeasure C μ T =
      μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} • Measure.pi (fun i : T ↦ ν i) := by
  have := isHaarMeasure_projMeasure C hCo hCc μ T
  have h := Measure.isAddLeftInvariant_eq_smul (projMeasure C μ T) (Measure.pi fun i : T ↦ ν i)
  set B : Set ((i : T) → G i) := Set.univ.pi fun i ↦ (C i : Set (G i)) with hBdef
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun i ↦ (hCo i).measurableSet
  have hpi : Measure.pi (fun i : T ↦ ν i) B = 1 := by
    rw [hBdef, Measure.pi_pi]
    simp [hν]
  have hproj : projMeasure C μ T B = μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} := by
    rw [projMeasure_apply C μ T hB]
    congr 1
    ext x
    simp only [hBdef, mem_inter_iff, mem_preimage, Set.mem_pi, mem_univ, true_implies, SetLike.mem_coe,
      mem_ofPred_eq, mem_box, proj_apply]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ T
      · exact h2 ⟨i, hi⟩
      · exact h1 i hi
    · intro h
      exact ⟨fun i _ ↦ h i, fun i ↦ h i⟩
  have hc : ((projMeasure C μ T).addHaarScalarFactor (Measure.pi fun i : T ↦ ν i) : ℝ≥0∞) =
      μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} := by
    have := congrArg (fun m : Measure ((i : T) → G i) ↦ m B) h
    simp only [Measure.smul_apply, hpi, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    rw [← hproj, this]
  conv_lhs => rw [h]
  rw [← hc]
  rfl

/- English proof (translation)
Establish `hb` using `(isOpen_box C hCo T).measurableSet`. Establish `hmeas : Measurable fun a : (i : T) → G i ↦ ∏ i : T, F i (a i)` using `Finset.measurable_prod _ fun i _ ↦ (hF i).comp (measurable_pi_apply i)`. Combine the equalities or inequalities in the displayed calculation. Use `setIntegral_congr_fun hb fun x hx ↦ ?_` and prove the remaining obligations. Rewrite using `[hΦ x hx, ← Finset.prod_coe_sort T]`.

Both sides reduce to the same expression. Use `_ = ∫ a, ∏ i : T, F i (a i) ∂projMeasure C μ T := by`. Rewrite using `[projMeasure, integral_map (continuous_proj C T).measurable.aemeasurable hmeas.aestronglyMeasurable]`. Use `_ = _ := by`. Rewrite using `[projMeasure_eq C hCo hCc μ ν hν T, integral_smul_measure, integral_fintype_prod_eq_prod, Finset.prod_coe_sort T (fun i ↦ ∫ y, F i y ∂ν i), Complex.real_smul, measureReal_def]`.
-/
theorem setIntegral_box (hCo : ∀ i, IsOpen (C i : Set (G i))) (hCc : ∀ i, IsCompact (C i : Set (G i)))
    (μ : Measure (Πʳ i, [G i, (C i : Set (G i))])) [μ.IsAddHaarMeasure] (ν : ∀ i, Measure (G i))
    [∀ i, (ν i).IsAddHaarMeasure] (hν : ∀ i, ν i (C i) = 1) (F : ∀ i, G i → ℂ)
    (hF : ∀ i, Measurable (F i)) (T : Finset ι) (Φ : Πʳ i, [G i, (C i : Set (G i))] → ℂ)
    (hΦ : ∀ x ∈ box C T, Φ x = ∏ i ∈ T, F i (x i)) :
    ∫ x in (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])), Φ x ∂μ =
      μ.real {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} * ∏ i ∈ T, ∫ y, F i y ∂ν i := by
  have hb := (isOpen_box C hCo T).measurableSet
  have hmeas : Measurable fun a : (i : T) → G i ↦ ∏ i : T, F i (a i) :=
    Finset.measurable_prod _ fun i _ ↦ (hF i).comp (measurable_pi_apply i)
  calc ∫ x in (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])), Φ x ∂μ =
        ∫ x in (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])),
          (fun a : (i : T) → G i ↦ ∏ i : T, F i (a i)) (proj C T x) ∂μ := by
        refine setIntegral_congr_fun hb fun x hx ↦ ?_
        rw [hΦ x hx, ← Finset.prod_coe_sort T]
        rfl
    _ = ∫ a, ∏ i : T, F i (a i) ∂projMeasure C μ T := by
        rw [projMeasure, integral_map (continuous_proj C T).measurable.aemeasurable
          hmeas.aestronglyMeasurable]
    _ = _ := by
        rw [projMeasure_eq C hCo hCc μ ν hν T, integral_smul_measure, integral_fintype_prod_eq_prod,
          Finset.prod_coe_sort T (fun i ↦ ∫ y, F i y ∂ν i), Complex.real_smul, measureReal_def]

end Measure

end RestrictedAddHaar

end

end GroundTheory.Automorphic
