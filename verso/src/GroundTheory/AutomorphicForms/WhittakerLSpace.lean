import Mathlib
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.LocallyConstantCompact

namespace GroundTheory.Automorphic

namespace Whittaker

open Set Topology

variable {X : Type*} [TopologicalSpace X]

def supportedIn (U : Set X) : Submodule ℂ (X → ℂ) where
  carrier := {f | f ∈ locallyConstantCompactSupport X ℂ ℂ ∧ Function.support f ⊆ U}
  add_mem' {f g} hf hg := ⟨(locallyConstantCompactSupport X ℂ ℂ).add_mem hf.1 hg.1,
    (Function.support_add f g).trans (union_subset hf.2 hg.2)⟩
  zero_mem' := ⟨(locallyConstantCompactSupport X ℂ ℂ).zero_mem, by simp⟩
  smul_mem' c f hf := ⟨(locallyConstantCompactSupport X ℂ ℂ).smul_mem c hf.1,
    (Function.support_const_smul_subset c f).trans hf.2⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_supportedIn {U : Set X} {f : X → ℂ} :
    f ∈ supportedIn U ↔ f ∈ locallyConstantCompactSupport X ℂ ℂ ∧ Function.support f ⊆ U :=
  Iff.rfl

/- English proof (translation)
Introduce `_ hf` and use `⟨hf.1, hf.2.trans h⟩`.
-/
theorem supportedIn_mono {U V : Set X} (h : U ⊆ V) : supportedIn U ≤ supportedIn V :=
  fun _ hf => ⟨hf.1, hf.2.trans h⟩

def vanishingOn (Z : Set X) : Submodule ℂ (X → ℂ) where
  carrier := {f | ∀ x ∈ Z, f x = 0}
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx]
  zero_mem' x _ := rfl
  smul_mem' c f hf x hx := by simp [hf x hx]

omit [TopologicalSpace X] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_vanishingOn {Z : Set X} {f : X → ℂ} : f ∈ vanishingOn Z ↔ ∀ x ∈ Z, f x = 0 :=
  Iff.rfl

omit [TopologicalSpace X] in
/- English proof (translation)
Introduce `_ hf x hx` and use `hf x (h hx)`.
-/
theorem vanishingOn_anti {Z Z' : Set X} (h : Z ⊆ Z') : vanishingOn Z' ≤ vanishingOn Z :=
  fun _ hf x hx => hf x (h hx)

/- English proof (translation)
Establish `: Function.support f = (f ⁻¹' {0})ᶜ`. Use extensionality with `x`. Simplify using `[Function.mem_support]`. Rewrite using `[this]`. Conclude with `(hf.isOpen_fiber 0).isClosed_compl`.
-/
theorem isClosed_support_of_isLocallyConstant {f : X → ℂ} (hf : IsLocallyConstant f) :
    IsClosed (Function.support f) := by
  have : Function.support f = (f ⁻¹' {0})ᶜ := by
    ext x
    simp [Function.mem_support]
  rw [this]
  exact (hf.isOpen_fiber 0).isClosed_compl

/- English proof (translation)
The claim follows from `hf.2.of_isClosed_subset (isClosed_support_of_isLocallyConstant hf.1) (subset_tsupport f)`.
-/
theorem isCompact_support {f : X → ℂ} (hf : f ∈ locallyConstantCompactSupport X ℂ ℂ) :
    IsCompact (Function.support f) :=
  hf.2.of_isClosed_subset (isClosed_support_of_isLocallyConstant hf.1) (subset_tsupport f)

/- English proof (translation)
Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : IsLocallyConstant (A.indicator (1 : X → ℂ))` using `(LocallyConstant.indicator (LocallyConstant.const X (1 : ℂ)) hA).isLocallyConstant`. Conclude with `h1.comp₂ hf.1.1 (· * ·)`. Use `hf.1.2.mono fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `hx (by simp [Function.notMem_support.1 h])`. Introduce `x hx`. Use `hf.2 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hx (by simp [Function.notMem_support.1 h])`.
-/
theorem indicator_mul_mem {U A : Set X} (hA : IsClopen A) {f : X → ℂ}
    (hf : f ∈ supportedIn U) : (fun x => A.indicator 1 x * f x) ∈ supportedIn U := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 : IsLocallyConstant (A.indicator (1 : X → ℂ)) :=
      (LocallyConstant.indicator (LocallyConstant.const X (1 : ℂ)) hA).isLocallyConstant
    exact h1.comp₂ hf.1.1 (· * ·)
  · refine hf.1.2.mono fun x hx => ?_
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])
  · intro x hx
    refine hf.2 ?_
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])

omit [TopologicalSpace X] in
/- English proof (translation)
Introduce `x hx`. Use `⟨?_, fun h => hx (by simp [h])⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hx (by simp [Set.indicator_of_notMem h])`.
-/
theorem support_indicator_mul_subset {A : Set X} {f : X → ℂ} :
    Function.support (fun x => A.indicator 1 x * f x) ⊆ A ∩ Function.support f := by
  intro x hx
  refine ⟨?_, fun h => hx (by simp [h])⟩
  by_contra h
  exact hx (by simp [Set.indicator_of_notMem h])

section LSpace

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

/- English proof (translation)
Establish `h : ∀ x ∈ A, ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ x ∈ B ∧ B ⊆ V` using `fun x hx => exists_isCompact_isOpen_subset (hV.mem_nhds (hAV hx))`. Use `choose B hBc hBo hxB hBV using h`. Take `⟨s, hs⟩` from `hA.elim_finite_subcover (fun x : A => B x x.2) (fun x => hBo x x.2) (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxB x hx⟩)`. Use `⟨⋃ x ∈ s, B x x.2, s.isCompact_biUnion fun x _ => hBc x x.2, isOpen_biUnion fun x _ => hBo x x.2, hs, iUnion₂_subset fun x _ => hBV x x.2⟩` and prove the remaining obligations.
-/
theorem exists_isCompact_isOpen_between {A V : Set X} (hA : IsCompact A) (hV : IsOpen V)
    (hAV : A ⊆ V) : ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ A ⊆ B ∧ B ⊆ V := by
  have h : ∀ x ∈ A, ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ x ∈ B ∧ B ⊆ V := fun x hx =>
    exists_isCompact_isOpen_subset (hV.mem_nhds (hAV hx))
  choose B hBc hBo hxB hBV using h
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover (fun x : A => B x x.2) (fun x => hBo x x.2)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxB x hx⟩)
  refine ⟨⋃ x ∈ s, B x x.2, s.isCompact_biUnion fun x _ => hBc x x.2,
    isOpen_biUnion fun x _ => hBo x x.2, hs, iUnion₂_subset fun x _ => hBV x x.2⟩

/- English proof (translation)
Take `⟨V, hVo, hV⟩` from `isOpen_induced_iff.1 hAo`. Establish `hAV : A ⊆ V` using `fun x hx => by`. Establish `: (⟨x, hAO hx⟩ : O) ∈ (Subtype.val : O → X) ⁻¹' V` using `by rw [hV]; exact hx`. Conclude with `this`. Take `⟨B, hBc, hBo, hAB, hBV⟩` from `exists_isCompact_isOpen_between hAc (hVo.inter hU) (subset_inter hAV (hAO.trans hOU))`.

Use `⟨B, hBc, hBo, hBV.trans inter_subset_right, subset_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce and unpack `x ⟨hxB, hxO⟩`. Establish `: (⟨x, hxO⟩ : O) ∈ (Subtype.val : O → X) ⁻¹' V` using `(hBV hxB).1`. Rewrite `this` using `[hV]`. Conclude with `this`.

Conclude with `fun x hx => ⟨hAB hx, hAO hx⟩`.
-/
theorem exists_isCompact_isOpen_inter_eq {U O A : Set X} (hU : IsOpen U) (hOU : O ⊆ U)
    (hAO : A ⊆ O) (hAc : IsCompact A) (hAo : IsOpen ((Subtype.val : O → X) ⁻¹' A)) :
    ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ B ⊆ U ∧ B ∩ O = A := by
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hAo
  have hAV : A ⊆ V := fun x hx => by
    have : (⟨x, hAO hx⟩ : O) ∈ (Subtype.val : O → X) ⁻¹' V := by rw [hV]; exact hx
    exact this
  obtain ⟨B, hBc, hBo, hAB, hBV⟩ :=
    exists_isCompact_isOpen_between hAc (hVo.inter hU) (subset_inter hAV (hAO.trans hOU))
  refine ⟨B, hBc, hBo, hBV.trans inter_subset_right, subset_antisymm ?_ ?_⟩
  · rintro x ⟨hxB, hxO⟩
    have : (⟨x, hxO⟩ : O) ∈ (Subtype.val : O → X) ⁻¹' V := (hBV hxB).1
    rw [hV] at this
    exact this
  · exact fun x hx => ⟨hAB hx, hAO hx⟩

/- English proof (translation)
Establish `key : ∀ c : ℂ, ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ B ⊆ U ∧ (c ≠ 0 → ∀ x : O, (x : X) ∈ B ↔ φ x = c)`. Introduce `c`. Distinguish the cases in `hc : c = 0`. Conclude with `⟨∅, isCompact_empty, isOpen_empty, empty_subset _, fun h => absurd hc h⟩`. Take `⟨hFc, hFo⟩` from `isCompact_isOpen_fiber hφ hc`.

Establish `hAc : IsCompact ((Subtype.val : O → X) '' {x | φ x = c})` using `hFc.image continuous_subtype_val`. Establish `hAo : IsOpen ((Subtype.val : O → X) ⁻¹' ((Subtype.val : O → X) '' {x | φ x = c}))`. Rewrite using `[preimage_image_eq _ Subtype.val_injective]` and apply the resulting hypothesis. Take `⟨B, hBc, hBo, hBU, hBO⟩` from `exists_isCompact_isOpen_inter_eq hU hOU (by rintro _ ⟨x, -, rfl⟩; exact x.2) hAc hAo`. Use `⟨B, hBc, hBo, hBU, fun _ x => ?_⟩` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `: (x : X) ∈ B ∩ O` using `⟨hx, x.2⟩`. Rewrite `this` using `[hBO]`. Take `⟨y, hy, hyx⟩` from `this`.

Rewrite using `[← Subtype.ext hyx]`. Conclude with `hy`. Introduce `hx`. Establish `: (x : X) ∈ (Subtype.val : O → X) '' {x | φ x = c}` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[← hBO]`.

Conclude with `this.1`. Use `choose B hBc hBo hBU hBO using key`. Establish `hfin` using `range_finite_of_mem_locallyConstantCompactSupport hφ`. Use `⟨∑ c ∈ hfin.toFinset.filter (· ≠ 0), (B c).indicator (fun _ => c), ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.sum_mem _ fun c _ => ⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `indicator_mem_locallyConstantCompactSupport (hBc c) (hBo c) c`. Conclude with `(Set.support_indicator_subset).trans (hBU c)`. Introduce `x`. Rewrite using `[Finset.sum_apply]`. Distinguish the cases in `hx : φ x = 0`.

Rewrite using `[hx]`. Use `Finset.sum_eq_zero fun c hc => ?_` and prove the remaining obligations. Establish `hc0 : c ≠ 0` using `(Finset.mem_filter.1 hc).2`. Use `Set.indicator_of_notMem (fun h => hc0 ?_) _` and prove the remaining obligations. Rewrite using `[← hx]`.

Conclude with `((hBO c hc0 x).1 h).symm`. Rewrite using `[Finset.sum_eq_single (φ x)]`. Conclude with `Set.indicator_of_mem ((hBO _ hx x).2 rfl) _`. Introduce `c hc hcx`. Conclude with `Set.indicator_of_notMem (fun h => hcx ((hBO c (Finset.mem_filter.1 hc).2 x).1 h).symm) _`.

Introduce `h`. Conclude with `absurd (Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 (mem_range_self x), hx⟩) h`.
-/
theorem exists_lift {U O : Set X} (hU : IsOpen U) (hOU : O ⊆ U) {φ : O → ℂ}
    (hφ : φ ∈ locallyConstantCompactSupport O ℂ ℂ) :
    ∃ f ∈ supportedIn U, ∀ x : O, f x = φ x := by
  classical
  have key : ∀ c : ℂ, ∃ B : Set X, IsCompact B ∧ IsOpen B ∧ B ⊆ U ∧
      (c ≠ 0 → ∀ x : O, (x : X) ∈ B ↔ φ x = c) := by
    intro c
    by_cases hc : c = 0
    · exact ⟨∅, isCompact_empty, isOpen_empty, empty_subset _, fun h => absurd hc h⟩
    obtain ⟨hFc, hFo⟩ := isCompact_isOpen_fiber hφ hc
    have hAc : IsCompact ((Subtype.val : O → X) '' {x | φ x = c}) :=
      hFc.image continuous_subtype_val
    have hAo : IsOpen ((Subtype.val : O → X) ⁻¹' ((Subtype.val : O → X) '' {x | φ x = c})) := by
      rwa [preimage_image_eq _ Subtype.val_injective]
    obtain ⟨B, hBc, hBo, hBU, hBO⟩ := exists_isCompact_isOpen_inter_eq hU hOU
      (by rintro _ ⟨x, -, rfl⟩; exact x.2) hAc hAo
    refine ⟨B, hBc, hBo, hBU, fun _ x => ?_⟩
    constructor
    · intro hx
      have : (x : X) ∈ B ∩ O := ⟨hx, x.2⟩
      rw [hBO] at this
      obtain ⟨y, hy, hyx⟩ := this
      rw [← Subtype.ext hyx]
      exact hy
    · intro hx
      have : (x : X) ∈ (Subtype.val : O → X) '' {x | φ x = c} := ⟨x, hx, rfl⟩
      rw [← hBO] at this
      exact this.1
  choose B hBc hBo hBU hBO using key
  have hfin := range_finite_of_mem_locallyConstantCompactSupport hφ
  refine ⟨∑ c ∈ hfin.toFinset.filter (· ≠ 0), (B c).indicator (fun _ => c), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun c _ => ⟨?_, ?_⟩
    · exact indicator_mem_locallyConstantCompactSupport (hBc c) (hBo c) c
    · exact (Set.support_indicator_subset).trans (hBU c)
  · intro x
    rw [Finset.sum_apply]
    by_cases hx : φ x = 0
    · rw [hx]
      refine Finset.sum_eq_zero fun c hc => ?_
      have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      refine Set.indicator_of_notMem (fun h => hc0 ?_) _
      rw [← hx]
      exact ((hBO c hc0 x).1 h).symm
    · rw [Finset.sum_eq_single (φ x)]
      · exact Set.indicator_of_mem ((hBO _ hx x).2 rfl) _
      · intro c hc hcx
        exact Set.indicator_of_notMem
          (fun h => hcx ((hBO c (Finset.mem_filter.1 hc).2 x).1 h).symm) _
      · intro h
        exact absurd (Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 (mem_range_self x), hx⟩) h

/- English proof (translation)
Take `⟨B, hBc, hBo, hBU, hBO⟩` from `exists_isCompact_isOpen_inter_eq hU hOU hAO hAc hAo`. Use `⟨B.indicator 1, ⟨indicator_mem_locallyConstantCompactSupport hBc hBo 1, Set.support_indicator_subset.trans hBU⟩, fun x hx => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hxA : x ∈ A`. Establish `hxB : x ∈ B`. Establish `: x ∈ B ∩ O` using `by rw [hBO]; exact hxA`.

Conclude with `this.1`. Rewrite using `[Set.indicator_of_mem hxA, Set.indicator_of_mem hxB]`. Rewrite using `[Set.indicator_of_notMem hxA, Set.indicator_of_notMem]`. Introduce `hxB`. Conclude with `hxA (hBO ▸ (⟨hxB, hx⟩ : x ∈ B ∩ O))`.
-/
theorem exists_lift_indicator {U O A : Set X} (hU : IsOpen U) (hOU : O ⊆ U) (hAO : A ⊆ O)
    (hAc : IsCompact A) (hAo : IsOpen ((Subtype.val : O → X) ⁻¹' A)) :
    ∃ f ∈ supportedIn U, ∀ x ∈ O, f x = A.indicator 1 x := by
  obtain ⟨B, hBc, hBo, hBU, hBO⟩ := exists_isCompact_isOpen_inter_eq hU hOU hAO hAc hAo
  refine ⟨B.indicator 1, ⟨indicator_mem_locallyConstantCompactSupport hBc hBo 1,
    Set.support_indicator_subset.trans hBU⟩, fun x hx => ?_⟩
  by_cases hxA : x ∈ A
  · have hxB : x ∈ B := by
      have : x ∈ B ∩ O := by rw [hBO]; exact hxA
      exact this.1
    rw [Set.indicator_of_mem hxA, Set.indicator_of_mem hxB]
  · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem]
    intro hxB
    exact hxA (hBO ▸ (⟨hxB, hx⟩ : x ∈ B ∩ O))

/- English proof (translation)
Take `⟨V, hVc, hVo, hyV, hVQ⟩` from `exists_isCompact_isOpen_subset (hQ.isClosed.isOpen_compl.mem_nhds hy)`. Conclude with `⟨V, ⟨hVc.isClosed, hVo⟩, hyV, Set.subset_compl_iff_disjoint_right.mp hVQ⟩`.
-/
theorem exists_isClopen_mem_disjoint {Q : Set X} (hQ : IsCompact Q) {y : X} (hy : y ∉ Q) :
    ∃ V : Set X, IsClopen V ∧ y ∈ V ∧ Disjoint V Q := by
  obtain ⟨V, hVc, hVo, hyV, hVQ⟩ :=
    exists_isCompact_isOpen_subset (hQ.isClosed.isOpen_compl.mem_nhds hy)
  exact ⟨V, ⟨hVc.isClosed, hVo⟩, hyV, Set.subset_compl_iff_disjoint_right.mp hVQ⟩

omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in

/- English proof (translation)
Set `good : Set Y → Prop` to `fun V => (fun x => (p ⁻¹' V).indicator 1 x * g x) ∈ W`. Establish `hloc : ∀ y, ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ good V`. Introduce `y`. Take `⟨c, hcW, k, hk, hck⟩` from `Submodule.mem_sup.1 (hfib y)`. Establish `hQ : IsCompact (p '' (C ∩ Function.support k))` using `((isCompact_support hk.1.1).inter_left hC).image hp`.

Establish `hyQ : y ∉ p '' (C ∩ Function.support k)`. Introduce and unpack `⟨x, ⟨hxC, hxk⟩, hxy⟩`. Conclude with `hxk (hk.2 x ⟨hxC, hxy⟩)`. Take `⟨V, hV, hyV, hVQ⟩` from `exists_isClopen_mem_disjoint hQ hyQ`. Use `⟨V, hV, hyV, ?_⟩` and prove the remaining obligations.

Establish `hsplit : (fun x => (p ⁻¹' V).indicator 1 x * g x) = (fun x => (p ⁻¹' V).indicator 1 x * c x) + (fun x => (p ⁻¹' V).indicator 1 x * k x)`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply, ← mul_add, ← hck]`. Use `show _ ∈ W`. Rewrite using `[hsplit]`.

Use `W.add_mem (hWmul V hV c hcW) (hWK ⟨indicator_mul_mem (hV.preimage hp) hk.1, ?_⟩)` and prove the remaining obligations. Introduce `x hxC`. Distinguish the cases in `hxV : x ∈ p ⁻¹' V`. Establish `: k x = 0`. Assume the negation of the conclusion as `hkx`.

Conclude with `Set.disjoint_left.1 hVQ hxV ⟨x, ⟨hxC, hkx⟩, rfl⟩`. Simplify using `[this]`. Simplify using `[Set.indicator_of_notMem hxV]`. Use `choose V hVc hyV hVg using hloc`. Establish `hQ : IsCompact (p '' (C ∩ Function.support g))` using `((isCompact_support hg.1).inter_left hC).image hp`.

Take `⟨s, hs⟩` from `hQ.elim_finite_subcover V (fun y => (hVc y).isOpen) (fun y _ => mem_iUnion.2 ⟨y, hyV y⟩)`. Establish `hunion : ∀ t : Finset Y, IsClopen (⋃ y ∈ t, V y) ∧ good (⋃ y ∈ t, V y)`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`.

Use `⟨by simp [isClopen_empty], ?_⟩` and prove the remaining obligations. Use `show _ ∈ W`. Simplify using `only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, preimage_empty, Set.indicator_empty, zero_mul]`. Conclude with `W.zero_mem`. Consider the case `insert a t hat ih`.

Take `⟨ht, hgt⟩` from `ih`. Establish `hcl : IsClopen (V a ∪ ⋃ y ∈ t, V y)` using `(hVc a).union ht`. Use `⟨by simpa [Finset.set_biUnion_insert] using hcl, ?_⟩` and prove the remaining obligations. Use `show _ ∈ W`. Establish `hmul` using `hWmul (V a) (hVc a) _ hgt`.

Establish `e : (fun x => (p ⁻¹' ⋃ y ∈ insert a t, V y).indicator 1 x * g x) = (fun x => (p ⁻¹' V a).indicator 1 x * g x) + (fun x => (p ⁻¹' ⋃ y ∈ t, V y).indicator 1 x * g x) - (fun x => (p ⁻¹' V a).indicator 1 x * ((p ⁻¹' ⋃ y ∈ t, V y).indicator 1 x * g x))`. Use function extensionality and compare the values at `x`. Simplify using `only [Finset.set_biUnion_insert, Pi.add_apply, Pi.sub_apply, preimage_union]`. Apply the tactic sequence `by_cases h1 : x ∈ p ⁻¹' V a <;> by_cases h2 : x ∈ p ⁻¹' ⋃ y ∈ t, V y <;>`. Simplify using `[Set.indicator_of_mem, Set.indicator_of_notMem]`.

Rewrite using `[e]`. Conclude with `W.sub_mem (W.add_mem (hVg a) hgt) hmul`. Take `⟨-, hgood⟩` from `hunion s`. Establish `hrest : (g - fun x => (p ⁻¹' ⋃ y ∈ s, V y).indicator 1 x * g x) ∈ W`. Use `hWK ⟨(supportedIn U).sub_mem hg (indicator_mul_mem ((hunion s).1.preimage hp) hg), ?_⟩` and prove the remaining obligations.

Introduce `x hxC`. Distinguish the cases in `hgx : g x = 0`. Simplify using `[hgx]`. Establish `hx : x ∈ p ⁻¹' ⋃ y ∈ s, V y` using `hs ⟨x, ⟨hxC, hgx⟩, rfl⟩`. Simplify using `only [Pi.sub_apply]`.

Rewrite using `[Set.indicator_of_mem hx, Pi.one_apply, one_mul, sub_self]`. Use `W.add_mem hrest hgood` as an intermediate fact. Simplify using `using this`.
-/
theorem mem_of_forall_fiber {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] {U C : Set X} (hC : IsClosed C) {p : X → Y}
    (hp : Continuous p) {W : Submodule ℂ (X → ℂ)}
    (hWK : supportedIn U ⊓ vanishingOn C ≤ W)
    (hWmul : ∀ V : Set Y, IsClopen V → ∀ w ∈ W, (fun x => (p ⁻¹' V).indicator 1 x * w x) ∈ W)
    {g : X → ℂ} (hg : g ∈ supportedIn U)
    (hfib : ∀ y, g ∈ W ⊔ (supportedIn U ⊓ vanishingOn (C ∩ p ⁻¹' {y}))) : g ∈ W := by
  classical

  let good : Set Y → Prop := fun V => (fun x => (p ⁻¹' V).indicator 1 x * g x) ∈ W
  have hloc : ∀ y, ∃ V : Set Y, IsClopen V ∧ y ∈ V ∧ good V := by
    intro y
    obtain ⟨c, hcW, k, hk, hck⟩ := Submodule.mem_sup.1 (hfib y)
    have hQ : IsCompact (p '' (C ∩ Function.support k)) :=
      ((isCompact_support hk.1.1).inter_left hC).image hp
    have hyQ : y ∉ p '' (C ∩ Function.support k) := by
      rintro ⟨x, ⟨hxC, hxk⟩, hxy⟩
      exact hxk (hk.2 x ⟨hxC, hxy⟩)
    obtain ⟨V, hV, hyV, hVQ⟩ := exists_isClopen_mem_disjoint hQ hyQ
    refine ⟨V, hV, hyV, ?_⟩
    have hsplit : (fun x => (p ⁻¹' V).indicator 1 x * g x) =
        (fun x => (p ⁻¹' V).indicator 1 x * c x) + (fun x => (p ⁻¹' V).indicator 1 x * k x) := by
      funext x
      simp only [Pi.add_apply, ← mul_add, ← hck]
    show _ ∈ W
    rw [hsplit]
    refine W.add_mem (hWmul V hV c hcW) (hWK ⟨indicator_mul_mem (hV.preimage hp) hk.1, ?_⟩)
    intro x hxC
    by_cases hxV : x ∈ p ⁻¹' V
    · have : k x = 0 := by
        by_contra hkx
        exact Set.disjoint_left.1 hVQ hxV ⟨x, ⟨hxC, hkx⟩, rfl⟩
      simp [this]
    · simp [Set.indicator_of_notMem hxV]
  choose V hVc hyV hVg using hloc

  have hQ : IsCompact (p '' (C ∩ Function.support g)) :=
    ((isCompact_support hg.1).inter_left hC).image hp
  obtain ⟨s, hs⟩ := hQ.elim_finite_subcover V (fun y => (hVc y).isOpen)
    (fun y _ => mem_iUnion.2 ⟨y, hyV y⟩)

  have hunion : ∀ t : Finset Y, IsClopen (⋃ y ∈ t, V y) ∧ good (⋃ y ∈ t, V y) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨by simp [isClopen_empty], ?_⟩
      show _ ∈ W
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, preimage_empty,
        Set.indicator_empty, zero_mul]
      exact W.zero_mem
    | insert a t hat ih =>
      obtain ⟨ht, hgt⟩ := ih
      have hcl : IsClopen (V a ∪ ⋃ y ∈ t, V y) := (hVc a).union ht
      refine ⟨by simpa [Finset.set_biUnion_insert] using hcl, ?_⟩
      show _ ∈ W
      have hmul := hWmul (V a) (hVc a) _ hgt
      have e : (fun x => (p ⁻¹' ⋃ y ∈ insert a t, V y).indicator 1 x * g x) =
          (fun x => (p ⁻¹' V a).indicator 1 x * g x) +
            (fun x => (p ⁻¹' ⋃ y ∈ t, V y).indicator 1 x * g x) -
            (fun x => (p ⁻¹' V a).indicator 1 x *
              ((p ⁻¹' ⋃ y ∈ t, V y).indicator 1 x * g x)) := by
        funext x
        simp only [Finset.set_biUnion_insert, Pi.add_apply, Pi.sub_apply, preimage_union]
        by_cases h1 : x ∈ p ⁻¹' V a <;> by_cases h2 : x ∈ p ⁻¹' ⋃ y ∈ t, V y <;>
          simp_all [Set.indicator_of_mem, Set.indicator_of_notMem]
      rw [e]
      exact W.sub_mem (W.add_mem (hVg a) hgt) hmul
  obtain ⟨-, hgood⟩ := hunion s
  have hrest : (g - fun x => (p ⁻¹' ⋃ y ∈ s, V y).indicator 1 x * g x) ∈ W := by
    refine hWK ⟨(supportedIn U).sub_mem hg
      (indicator_mul_mem ((hunion s).1.preimage hp) hg), ?_⟩
    intro x hxC
    by_cases hgx : g x = 0
    · simp [hgx]
    · have hx : x ∈ p ⁻¹' ⋃ y ∈ s, V y := hs ⟨x, ⟨hxC, hgx⟩, rfl⟩
      simp only [Pi.sub_apply]
      rw [Set.indicator_of_mem hx, Pi.one_apply, one_mul, sub_self]
  have := W.add_mem hrest hgood
  simpa using this

/- English proof (translation)
Introduce `f hf`. Establish `hB : ∀ x ∈ V, ∃ B : Set X, IsClopen B ∧ x ∈ B ∧ supportedIn B ≤ M`. Introduce `x hx`. Take `⟨V', hV'o, hxV', hV'M⟩` from `hloc x hx`. Take `⟨B, hBc, hBo, hxB, hBV'⟩` from `exists_isCompact_isOpen_subset (hV'o.mem_nhds hxV')`.

Conclude with `⟨B, ⟨hBc.isClosed, hBo⟩, hxB, (supportedIn_mono hBV').trans hV'M⟩`. Use `choose! B hBc hxB hBM using hB`. Take `⟨s, hsV, hsfin, hs⟩` from `(isCompact_support hf.1).elim_finite_subcover_image (b := V) (c := B) (fun x hx => (hBc x hx).isOpen) (fun x hx => mem_iUnion₂.2 ⟨x, hf.2 hx, hxB x (hf.2 hx)⟩)`. Establish `key : ∀ t : Finset X, (↑t : Set X) ⊆ V → ∀ g ∈ supportedIn V, Function.support g ⊆ ⋃ x ∈ t, B x → g ∈ M`. Introduce `t`.

Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `_ g _ hg`. Establish `: g = 0`. Use function extensionality and compare the values at `x`.

Assume the negation of the conclusion as `h`. Simplify using `using hg h`. Rewrite using `[this]`. Conclude with `M.zero_mem`. Consider the case `insert a t hat ih`.

Introduce `htV g hg hgs`. Establish `haV : a ∈ V` using `htV (by simp)`. Establish `e : g = (fun x => (B a).indicator 1 x * g x) + (fun x => (B a)ᶜ.indicator 1 x * g x)`. Use function extensionality and compare the values at `x`. Apply the tactic sequence `by_cases h : x ∈ B a <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]`.

Rewrite using `[e]`. Use `M.add_mem (hBM a haV ⟨(indicator_mul_mem (hBc a haV) hg).1, ?_⟩) (ih (fun x hx => htV (by simp [hx])) _ (indicator_mul_mem (hBc a haV).compl hg) ?_)` and prove the remaining obligations. Conclude with `support_indicator_mul_subset.trans inter_subset_left`. Introduce `x hx`. Take `⟨hxB, hxg⟩` from `support_indicator_mul_subset hx`.

Use `hgs hxg` as an intermediate fact. Rewrite `this` using `[Finset.set_biUnion_insert]`. Break down `this with h | h` into its components or cases. Conclude with `absurd h hxB`. Simplify using `using h`.

Conclude with `key hsfin.toFinset (fun x hx => hsV (by simpa using hx)) f hf (by simpa using hs)`.
-/
theorem supportedIn_le_of_local {V : Set X} {M : Submodule ℂ (X → ℂ)}
    (hloc : ∀ x ∈ V, ∃ V' : Set X, IsOpen V' ∧ x ∈ V' ∧ supportedIn V' ≤ M) :
    supportedIn V ≤ M := by
  classical
  intro f hf
  have hB : ∀ x ∈ V, ∃ B : Set X, IsClopen B ∧ x ∈ B ∧ supportedIn B ≤ M := by
    intro x hx
    obtain ⟨V', hV'o, hxV', hV'M⟩ := hloc x hx
    obtain ⟨B, hBc, hBo, hxB, hBV'⟩ := exists_isCompact_isOpen_subset (hV'o.mem_nhds hxV')
    exact ⟨B, ⟨hBc.isClosed, hBo⟩, hxB, (supportedIn_mono hBV').trans hV'M⟩
  choose! B hBc hxB hBM using hB
  obtain ⟨s, hsV, hsfin, hs⟩ := (isCompact_support hf.1).elim_finite_subcover_image
    (b := V) (c := B) (fun x hx => (hBc x hx).isOpen)
    (fun x hx => mem_iUnion₂.2 ⟨x, hf.2 hx, hxB x (hf.2 hx)⟩)
  have key : ∀ t : Finset X, (↑t : Set X) ⊆ V → ∀ g ∈ supportedIn V,
      Function.support g ⊆ ⋃ x ∈ t, B x → g ∈ M := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ g _ hg
      have : g = 0 := by
        funext x
        by_contra h
        simpa using hg h
      rw [this]
      exact M.zero_mem
    | insert a t hat ih =>
      intro htV g hg hgs
      have haV : a ∈ V := htV (by simp)
      have e : g = (fun x => (B a).indicator 1 x * g x) +
          (fun x => (B a)ᶜ.indicator 1 x * g x) := by
        funext x
        by_cases h : x ∈ B a <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      rw [e]
      refine M.add_mem (hBM a haV ⟨(indicator_mul_mem (hBc a haV) hg).1, ?_⟩)
        (ih (fun x hx => htV (by simp [hx])) _ (indicator_mul_mem (hBc a haV).compl hg) ?_)
      · exact support_indicator_mul_subset.trans inter_subset_left
      · intro x hx
        obtain ⟨hxB, hxg⟩ := support_indicator_mul_subset hx
        have := hgs hxg
        rw [Finset.set_biUnion_insert] at this
        rcases this with h | h
        · exact absurd h hxB
        · simpa using h
  exact key hsfin.toFinset (fun x hx => hsV (by simpa using hx)) f hf (by simpa using hs)

end LSpace

end Whittaker

end GroundTheory.Automorphic
