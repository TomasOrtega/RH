import Mathlib
import GroundTheory.AutomorphicForms.LocallyProfinite

noncomputable section

namespace GroundTheory.Automorphic

open Set Filter Topology
open scoped Pointwise

section Space

variable (X : Type*) [TopologicalSpace X] (R E : Type*) [Semiring R] [AddCommMonoid E]
  [Module R E]

def locallyConstantCompactSupport : Submodule R (X → E) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  add_mem' {f g} hf hg := ⟨hf.1.comp₂ hg.1 (· + ·), hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c f hf := ⟨hf.1.comp (c • ·), hf.2.mono fun x hx => by
    by_contra h
    exact hx (by simp [Function.notMem_support.1 h])⟩

variable {X R E}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_locallyConstantCompactSupport {f : X → E} :
    f ∈ locallyConstantCompactSupport X R E ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  Iff.rfl

/- English proof (translation)
Use `⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩` and prove the remaining obligations. Conclude with `(LocallyConstant.indicator (LocallyConstant.const X e) ⟨hc.isClosed, ho⟩).isLocallyConstant`.
-/
theorem indicator_mem_locallyConstantCompactSupport [T2Space X] {U : Set X} (hc : IsCompact U)
    (ho : IsOpen U) (e : E) :
    U.indicator (fun _ => e) ∈ locallyConstantCompactSupport X R E := by
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  exact (LocallyConstant.indicator (LocallyConstant.const X e) ⟨hc.isClosed, ho⟩).isLocallyConstant

/- English proof (translation)
Establish `: CompactSpace (tsupport f)` using `isCompact_iff_compactSpace.1 hf.2`. Establish `h1 : (range fun x : tsupport f => f x).Finite` using `(hf.1.comp_continuous continuous_subtype_val).range_finite`. Use `(h1.insert 0).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Distinguish the cases in `hx : x ∈ tsupport f`.

Conclude with `mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩`. Rewrite using `[image_eq_zero_of_notMem_tsupport hx]`. Conclude with `mem_insert _ _`.
-/
theorem range_finite_of_mem_locallyConstantCompactSupport {f : X → E}
    (hf : f ∈ locallyConstantCompactSupport X R E) : (range f).Finite := by
  have : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hf.2
  have h1 : (range fun x : tsupport f => f x).Finite :=
    (hf.1.comp_continuous continuous_subtype_val).range_finite
  refine (h1.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport f
  · exact mem_insert_of_mem _ ⟨⟨x, hx⟩, rfl⟩
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact mem_insert _ _

/- English proof (translation)
Use `⟨hf.2.of_isClosed_subset (hf.1.isClosed_fiber v) fun x hx => ?_, hf.1.isOpen_fiber v⟩` and prove the remaining obligations. Use `subset_tsupport f ?_` and prove the remaining obligations. Establish `hx : f x = v` using `hx`. Simplify using `[Function.mem_support, hx, hv]`.
-/
theorem isCompact_isOpen_fiber {f : X → E} (hf : f ∈ locallyConstantCompactSupport X R E)
    {v : E} (hv : v ≠ 0) : IsCompact {x | f x = v} ∧ IsOpen {x | f x = v} := by
  refine ⟨hf.2.of_isClosed_subset (hf.1.isClosed_fiber v) fun x hx => ?_, hf.1.isOpen_fiber v⟩
  refine subset_tsupport f ?_
  have hx : f x = v := hx
  simp [Function.mem_support, hx, hv]

end Space

section Group

variable {G : Type*} [Group G] {E : Type*}

/- English proof (translation)
Use `conv_lhs => rw [← QuotientGroup.out_eq' x]`. Rewrite using `[eq_comm, QuotientGroup.eq, mem_leftCoset_iff, SetLike.mem_coe]`.
-/
theorem mk_eq_iff_mem_out_smul (K : Subgroup G) (x : G ⧸ K) (y : G) :
    (y : G ⧸ K) = x ↔ y ∈ x.out • (K : Set G) := by
  conv_lhs => rw [← QuotientGroup.out_eq' x]
  rw [eq_comm, QuotientGroup.eq, mem_leftCoset_iff, SetLike.mem_coe]

/- English proof (translation)
Take `⟨k, hk, rfl⟩` from `Set.mem_smul_set.1 hy`. Conclude with `hK g k hk`.
-/
theorem apply_eq_of_mem_smul {K : Subgroup G} {f : G → E}
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) {g y : G} (hy : y ∈ g • (K : Set G)) : f y = f g := by
  obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hy
  exact hK g k hk

variable [TopologicalSpace G] [IsTopologicalGroup G] {R : Type*} [Semiring R] [AddCommMonoid E]
  [Module R E]

/- English proof (translation)
Use `⟨(IsLocallyConstant.iff_exists_open f).2 fun g => ?_, hf⟩` and prove the remaining obligations. Use `⟨g • (K : Set G), K.isOpen.smul g, ?_, fun y hy => apply_eq_of_mem_smul hK hy⟩` and prove the remaining obligations. Conclude with `Set.mem_smul_set.2 ⟨1, K.one_mem, mul_one g⟩`.
-/
theorem mem_locallyConstantCompactSupport_of_forall_mul_right (K : OpenSubgroup G)
    {f : G → E} (hf : HasCompactSupport f) (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f ∈ locallyConstantCompactSupport G R E := by
  refine ⟨(IsLocallyConstant.iff_exists_open f).2 fun g => ?_, hf⟩
  refine ⟨g • (K : Set G), K.isOpen.smul g, ?_, fun y hy => apply_eq_of_mem_smul hK hy⟩
  exact Set.mem_smul_set.2 ⟨1, K.one_mem, mul_one g⟩

/- English proof (translation)
The claim follows from `(hf.image QuotientGroup.continuous_mk).finite_of_discrete`.
-/
theorem finite_image_mk_tsupport (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f) :
    (QuotientGroup.mk '' tsupport f : Set (G ⧸ (K : Subgroup G))).Finite :=
  (hf.image QuotientGroup.continuous_mk).finite_of_discrete

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[Finset.sum_apply]`. Distinguish the cases in `hy : (y : G ⧸ (K : Subgroup G)) ∈ (finite_image_mk_tsupport K hf).toFinset`. Rewrite using `[Finset.sum_eq_single (y : G ⧸ (K : Subgroup G))]`. Establish `hmem : y ∈ (y : G ⧸ (K : Subgroup G)).out • (K : Set G)` using `(mk_eq_iff_mem_out_smul (K : Subgroup G) _ y).1 rfl`.

Rewrite using `[Set.indicator_of_mem hmem]`. Conclude with `apply_eq_of_mem_smul hK hmem`. Introduce `b _ hb`. Conclude with `Set.indicator_of_notMem (fun h => hb ((mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h).symm) _`. Introduce `h`.

Conclude with `absurd hy h`. Rewrite using `[Finset.sum_eq_zero]`. Assume the negation of the conclusion as `h`. Conclude with `hy ((Set.Finite.mem_toFinset _).2 ⟨y, subset_tsupport f h, rfl⟩)`. Introduce `b hb`.

Use `Set.indicator_of_notMem (fun h => hy ?_) _` and prove the remaining obligations. Rewrite using `[(mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h]` and apply the resulting hypothesis.
-/
theorem eq_sum_indicator_coset (K : OpenSubgroup G) {f : G → E} (hf : HasCompactSupport f)
    (hK : ∀ g, ∀ k ∈ K, f (g * k) = f g) :
    f = ∑ x ∈ (finite_image_mk_tsupport K hf).toFinset,
      (x.out • (K : Set G)).indicator (fun _ => f x.out) := by
  classical
  funext y
  rw [Finset.sum_apply]
  by_cases hy : (y : G ⧸ (K : Subgroup G)) ∈ (finite_image_mk_tsupport K hf).toFinset
  · rw [Finset.sum_eq_single (y : G ⧸ (K : Subgroup G))]
    · have hmem : y ∈ (y : G ⧸ (K : Subgroup G)).out • (K : Set G) :=
        (mk_eq_iff_mem_out_smul (K : Subgroup G) _ y).1 rfl
      rw [Set.indicator_of_mem hmem]
      exact apply_eq_of_mem_smul hK hmem
    · intro b _ hb
      exact Set.indicator_of_notMem
        (fun h => hb ((mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h).symm) _
    · intro h
      exact absurd hy h
  · rw [Finset.sum_eq_zero]
    · by_contra h
      exact hy ((Set.Finite.mem_toFinset _).2 ⟨y, subset_tsupport f h, rfl⟩)
    · intro b hb
      refine Set.indicator_of_notMem (fun h => hy ?_) _
      rwa [(mk_eq_iff_mem_out_smul (K : Subgroup G) b y).2 h]

variable [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/- English proof (translation)
Set `W : Set (G × G)` to `{p | f (p.1 * p.2) = f p.1}`. Establish `hW : IsOpen W`. Establish `hF : IsLocallyConstant fun p : G × G => (f (p.1 * p.2), f p.1)` using `(hf.1.comp_continuous continuous_mul).prodMk (hf.1.comp_continuous continuous_fst)`. Conclude with `hF {q | q.1 = q.2}`. Establish `hsub : tsupport f ×ˢ ({1} : Set G) ⊆ W`.

Introduce and unpack `⟨g, k⟩ ⟨-, hk⟩`. Simplify using `only [mem_singleton_iff] at hk`. Simplify using `[W, hk]`. Take `⟨u, v, -, hv, hSu, h1v, huv⟩` from `generalized_tube_lemma hf.2 isCompact_singleton hW hsub`. Take `⟨K, hKc, hKv⟩` from `exists_openSubgroup_isCompact_subset (hv.mem_nhds (h1v rfl))`.

Establish `key : ∀ s ∈ tsupport f, ∀ k ∈ K, f (s * k) = f s` using `fun s hs k hk => huv (show (s, k) ∈ u ×ˢ v from ⟨hSu hs, hKv hk⟩)`. Use `⟨K, hKc, fun g k hk => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ tsupport f`. Conclude with `key g hg k hk`. Rewrite using `[image_eq_zero_of_notMem_tsupport hg]`.

Assume the negation of the conclusion as `h`. Use `key (g * k) (subset_tsupport f h) k⁻¹ (inv_mem hk)` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_right, image_eq_zero_of_notMem_tsupport hg]`. Conclude with `h this.symm`.
-/
theorem exists_forall_mul_right {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ g, ∀ k ∈ K, f (g * k) = f g := by
  let W : Set (G × G) := {p | f (p.1 * p.2) = f p.1}
  have hW : IsOpen W := by
    have hF : IsLocallyConstant fun p : G × G => (f (p.1 * p.2), f p.1) :=
      (hf.1.comp_continuous continuous_mul).prodMk (hf.1.comp_continuous continuous_fst)
    exact hF {q | q.1 = q.2}
  have hsub : tsupport f ×ˢ ({1} : Set G) ⊆ W := by
    rintro ⟨g, k⟩ ⟨-, hk⟩
    simp only [mem_singleton_iff] at hk
    simp [W, hk]
  obtain ⟨u, v, -, hv, hSu, h1v, huv⟩ := generalized_tube_lemma hf.2 isCompact_singleton hW hsub
  obtain ⟨K, hKc, hKv⟩ := exists_openSubgroup_isCompact_subset (hv.mem_nhds (h1v rfl))
  have key : ∀ s ∈ tsupport f, ∀ k ∈ K, f (s * k) = f s := fun s hs k hk =>
    huv (show (s, k) ∈ u ×ˢ v from ⟨hSu hs, hKv hk⟩)
  refine ⟨K, hKc, fun g k hk => ?_⟩
  by_cases hg : g ∈ tsupport f
  · exact key g hg k hk
  · rw [image_eq_zero_of_notMem_tsupport hg]
    by_contra h
    have := key (g * k) (subset_tsupport f h) k⁻¹ (inv_mem hk)
    rw [mul_inv_cancel_right, image_eq_zero_of_notMem_tsupport hg] at this
    exact h this.symm

/- English proof (translation)
Establish `hf' : (fun g => f g⁻¹) ∈ locallyConstantCompactSupport G R E` using `⟨hf.1.comp_continuous continuous_inv, hf.2.comp_homeomorph (Homeomorph.inv G)⟩`. Take `⟨K, hKc, hK⟩` from `exists_forall_mul_right hf'`. Use `⟨K, hKc, fun k hk g => ?_⟩` and prove the remaining obligations. Use `hK g⁻¹ k⁻¹ (inv_mem hk)` as an intermediate fact. Simplify `this` using `[mul_inv_rev]`.
-/
theorem exists_forall_mul_left {f : G → E} (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, ∀ g, f (k * g) = f g := by
  have hf' : (fun g => f g⁻¹) ∈ locallyConstantCompactSupport G R E :=
    ⟨hf.1.comp_continuous continuous_inv, hf.2.comp_homeomorph (Homeomorph.inv G)⟩
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_right hf'
  refine ⟨K, hKc, fun k hk g => ?_⟩
  have := hK g⁻¹ k⁻¹ (inv_mem hk)
  simpa [mul_inv_rev] using this

/- English proof (translation)
Take `⟨K₁, h₁, hK₁⟩` from `exists_forall_mul_right hf`. Take `⟨K₂, -, hK₂⟩` from `exists_forall_mul_left hf`. Use `⟨K₁ ⊓ K₂, isCompact_inf_left h₁, fun k hk g k' hk' => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, hK₂ k (OpenSubgroup.mem_inf.1 hk).2, hK₁ g k' (OpenSubgroup.mem_inf.1 hk').1]`.
-/
theorem exists_forall_mul_left_mul_right {f : G → E}
    (hf : f ∈ locallyConstantCompactSupport G R E) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      ∀ k ∈ K, ∀ g, ∀ k' ∈ K, f (k * g * k') = f g := by
  obtain ⟨K₁, h₁, hK₁⟩ := exists_forall_mul_right hf
  obtain ⟨K₂, -, hK₂⟩ := exists_forall_mul_left hf
  refine ⟨K₁ ⊓ K₂, isCompact_inf_left h₁, fun k hk g k' hk' => ?_⟩
  rw [mul_assoc, hK₂ k (OpenSubgroup.mem_inf.1 hk).2, hK₁ g k' (OpenSubgroup.mem_inf.1 hk').1]

end Group

end GroundTheory.Automorphic
