import Mathlib

open Submodule MulAction

namespace GlobalTheory.GradedFixed

variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

def WA (V : ι → Submodule ℂ M) (A : Set ι) : Submodule ℂ M := ⨆ (j) (_ : j ∈ A), V j

/- English proof (translation)
The claim follows from `biSup_mono fun _ hj => h hj`.
-/
theorem WA_mono (V : ι → Submodule ℂ M) {A B : Set ι} (h : A ⊆ B) : WA V A ≤ WA V B :=
  biSup_mono fun _ hj => h hj

/- English proof (translation)
The claim follows from `le_iSup₂_of_le j hj le_rfl`.
-/
theorem le_WA (V : ι → Submodule ℂ M) {A : Set ι} {j : ι} (hj : j ∈ A) : V j ≤ WA V A :=
  le_iSup₂_of_le j hj le_rfl

/- English proof (translation)
The claim follows from `iSup_union`.
-/
theorem WA_union (V : ι → Submodule ℂ M) (A B : Set ι) : WA V (A ∪ B) = WA V A ⊔ WA V B :=
  iSup_union

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `iSup_le fun g => le_WA V (mem_orbit i g)`. Use `iSup₂_le fun j hj => ?_` and prove the remaining obligations. Take `⟨g, rfl⟩` from `hj`. Conclude with `le_iSup (fun g : G => V (g • i)) g`.
-/
theorem iSup_orbit (V : ι → Submodule ℂ M) (i : ι) :
    (⨆ g : G, V (g • i)) = WA V (orbit G i) := by
  apply le_antisymm
  · exact iSup_le fun g => le_WA V (mem_orbit i g)
  · refine iSup₂_le fun j hj => ?_
    obtain ⟨g, rfl⟩ := hj
    exact le_iSup (fun g : G => V (g • i)) g

/- English proof (translation)
Take `⟨h, rfl⟩` from `hj`. Conclude with `⟨g * h, mul_smul g h i⟩`.
-/
theorem orbit_stable (i : ι) (g : G) {j : ι} (hj : j ∈ orbit G i) : g • j ∈ orbit G i := by
  obtain ⟨h, rfl⟩ := hj
  exact ⟨g * h, mul_smul g h i⟩

/- English proof (translation)
Establish `: (WA V A).map (π g) ≤ WA V A`. Unfold `WA`. Rewrite using `[Submodule.map_iSup]`. Use `iSup_le fun j => ?_` and prove the remaining obligations. Rewrite using `[Submodule.map_iSup]`.

Conclude with `iSup_le fun hj => (hπ g j).trans (le_WA V (hA g j hj))`. Conclude with `this (Submodule.mem_map_of_mem hx)`.
-/
theorem map_WA_le (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) {A : Set ι}
    (hA : ∀ (g : G), ∀ j ∈ A, g • j ∈ A) (g : G) {x : M} (hx : x ∈ WA V A) :
    π g x ∈ WA V A := by
  have : (WA V A).map (π g) ≤ WA V A := by
    unfold WA
    rw [Submodule.map_iSup]
    refine iSup_le fun j => ?_
    rw [Submodule.map_iSup]
    exact iSup_le fun hj => (hπ g j).trans (le_WA V (hA g j hj))
  exact this (Submodule.mem_map_of_mem hx)

/- English proof (translation)
Introduce `g`. Establish `h1 : π g a - a ∈ WA V A` using `sub_mem (map_WA_le π V hπ hA g ha) ha`. Establish `h2 : π g a - a ∈ WA V B`. Establish `e : π g a - a = b - π g b`. Rewrite using `[sub_eq_sub_iff_add_eq_add, ← map_add, hfix g, add_comm]`.

Rewrite using `[e]`. Conclude with `sub_mem hb (map_WA_le π V hπ hB g hb)`. Establish `hd : Disjoint (WA V A) (WA V B)` using `hV.disjoint_biSup_biSup hAB`. Conclude with `sub_eq_zero.mp (Submodule.disjoint_def.mp hd _ h1 h2)`.
-/
theorem fixed_part (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (hV : iSupIndep V)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) {A B : Set ι}
    (hA : ∀ (g : G), ∀ j ∈ A, g • j ∈ A) (hB : ∀ (g : G), ∀ j ∈ B, g • j ∈ B)
    (hAB : Disjoint A B) {a b : M} (ha : a ∈ WA V A) (hb : b ∈ WA V B)
    (hfix : ∀ g, π g (a + b) = a + b) : ∀ g, π g a = a := by
  intro g
  have h1 : π g a - a ∈ WA V A := sub_mem (map_WA_le π V hπ hA g ha) ha
  have h2 : π g a - a ∈ WA V B := by
    have e : π g a - a = b - π g b := by
      rw [sub_eq_sub_iff_add_eq_add, ← map_add, hfix g, add_comm]
    rw [e]
    exact sub_mem hb (map_WA_le π V hπ hB g hb)
  have hd : Disjoint (WA V A) (WA V B) := hV.disjoint_biSup_biSup hAB
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp hd _ h1 h2)

/- English proof (translation)
Use `letI := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hV htop).chooseDecomposition`. Use `⟨fun i => (V i).subtype ∘ₗ (DirectSum.component ℂ ι (fun i => ↥(V i)) i) ∘ₗ (DirectSum.decomposeLinearEquiv V).toLinearMap, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i w`. Simplify using the standard rewrite rules. Introduce `i v hv`.

Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply, ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]`. Conclude with `DirectSum.decompose_of_mem_same V hv`. Introduce `i j v hij hv`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply, ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]`. Conclude with `DirectSum.decompose_of_mem_ne V hv hij.symm`.

Introduce `w`. Use `⟨(DirectSum.decompose V w).support, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply, ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]`. Conclude with `(DirectSum.sum_support_decompose V w).symm`.
-/
theorem exists_comp (V : ι → Submodule ℂ M) (hV : iSupIndep V) (htop : (⨆ i, V i) = ⊤) :
    ∃ c : ι → M →ₗ[ℂ] M, (∀ i w, c i w ∈ V i) ∧ (∀ i v, v ∈ V i → c i v = v) ∧
      (∀ i j v, i ≠ j → v ∈ V j → c i v = 0) ∧ (∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w) := by
  classical
  letI := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hV htop).chooseDecomposition
  refine ⟨fun i => (V i).subtype ∘ₗ (DirectSum.component ℂ ι (fun i => ↥(V i)) i) ∘ₗ
    (DirectSum.decomposeLinearEquiv V).toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro i w; simp
  · intro i v hv
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact DirectSum.decompose_of_mem_same V hv
  · intro i j v hij hv
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact DirectSum.decompose_of_mem_ne V hv hij.symm
  · intro w
    refine ⟨(DirectSum.decompose V w).support, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
      ← DirectSum.apply_eq_component, DirectSum.decomposeLinearEquiv_apply]
    exact (DirectSum.sum_support_decompose V w).symm

end GlobalTheory.GradedFixed

namespace GlobalTheory.GradedFixed

variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

section comp

variable (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (c : ι → M →ₗ[ℂ] M)
  (hc1 : ∀ i w, c i w ∈ V i) (hc2 : ∀ i v, v ∈ V i → c i v = v)
  (hc3 : ∀ i j v, i ≠ j → v ∈ V j → c i v = 0) (hc4 : ∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w)
include hc1 hc2 hc3 hc4

/- English proof (translation)
Take `⟨F, hF⟩` from `hc4 w`. Rewrite using `[hF, map_sum, map_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hmem : π g (c j w) ∈ V (g • j)` using `hπ g j (Submodule.mem_map_of_mem (hc1 j w))`. Distinguish the cases in `hij : j = i`.

Substitute `hij` using the available equality. Rewrite using `[hc2 _ _ hmem, hc2 _ _ (hc1 j w)]`. Rewrite using `[hc3 _ _ _ (fun h => hij (smul_left_cancel g h).symm) hmem, hc3 _ _ _ (Ne.symm hij) (hc1 j w), map_zero]`.
-/
theorem comp_equivariant (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i))
    (g : G) (i : ι) (w : M) : c (g • i) (π g w) = π g (c i w) := by
  obtain ⟨F, hF⟩ := hc4 w
  rw [hF, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmem : π g (c j w) ∈ V (g • j) := hπ g j (Submodule.mem_map_of_mem (hc1 j w))
  by_cases hij : j = i
  · subst hij
    rw [hc2 _ _ hmem, hc2 _ _ (hc1 j w)]
  · rw [hc3 _ _ _ (fun h => hij (smul_left_cancel g h).symm) hmem, hc3 _ _ _ (Ne.symm hij) (hc1 j w),
      map_zero]

omit hc1 hc2 hc4 in
/- English proof (translation)
Establish `: WA V A ≤ LinearMap.ker (c l)` using `iSup₂_le fun j hj v hv => LinearMap.mem_ker.mpr (hc3 l j v (fun h => hl (h ▸ hj)) hv)`. Conclude with `LinearMap.mem_ker.mp (this hx)`.
-/
theorem comp_outside {A : Set ι} {x : M} (hx : x ∈ WA V A) {l : ι} (hl : l ∉ A) : c l x = 0 := by
  have : WA V A ≤ LinearMap.ker (c l) :=
    iSup₂_le fun j hj v hv => LinearMap.mem_ker.mpr (hc3 l j v (fun h => hl (h ▸ hj)) hv)
  exact LinearMap.mem_ker.mp (this hx)

omit hc1 hc2 hc3 in
/- English proof (translation)
Take `⟨F, hF⟩` from `hc4 x`. Rewrite using `[hF]`. Conclude with `Finset.sum_eq_zero fun l _ => h l`.
-/
theorem eq_zero_of_comp {x : M} (h : ∀ l, c l x = 0) : x = 0 := by
  obtain ⟨F, hF⟩ := hc4 x
  rw [hF]
  exact Finset.sum_eq_zero fun l _ => h l

omit hc2 hc4 in
/- English proof (translation)
Rewrite using `[hw]`. Conclude with `Submodule.sum_mem _ fun j hj => le_WA V (hF j hj) (hc1 j w)`.
-/
theorem mem_WA_of_sum {A : Set ι} {F : Finset ι} (hF : ∀ j ∈ F, j ∈ A) (w : M)
    (hw : w = ∑ i ∈ F, c i w) : w ∈ WA V A := by
  rw [hw]
  exact Submodule.sum_mem _ fun j hj => le_WA V (hF j hj) (hc1 j w)

/- English proof (translation)
Take `⟨F, hF⟩` from `hc4 y`. Take `⟨k, -, hk⟩ : ∃ k ∈ F, c k y ≠ 0` from `by by_contra! h`. Conclude with `hy0 (by rw [hF]; exact Finset.sum_eq_zero h)`. Establish `hkO : k ∈ orbit G i`. Assume the negation of the conclusion as `hkO`.

Conclude with `hk (comp_outside V c hc3 hyO hkO)`. Take `⟨v, hv⟩` from `hline k`. Take `⟨b, hb⟩` from `Submodule.mem_span_singleton.mp (hv (hc1 k y))`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.mp (hv (hc1 k x))`. Establish `hb0 : b ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hk (by rw [← hb, zero_smul])`. Use `set z := x - (a / b) • y with hz`. Establish `hzk : c k z = 0`. Rewrite using `[hz, map_sub, map_smul, ← ha, ← hb, smul_smul, div_mul_cancel₀ a hb0, sub_self]`.

Establish `hzfix : ∀ g, π g z = z` using `fun g => by rw [hz, map_sub, map_smul, hx, hy]`. Establish `hzO : z ∈ WA V (orbit G i)` using `sub_mem hxO (Submodule.smul_mem _ _ hyO)`. Establish `hz0 : z = 0`. Use `eq_zero_of_comp c hc4 fun l => ?_` and prove the remaining obligations. Distinguish the cases in `hl : l ∈ orbit G i`.

Take `⟨g0, rfl⟩` from `hkO`. Take `⟨g1, rfl⟩` from `hl`. Establish `e : g1 • i = (g1 * g0⁻¹) • (g0 • i)` using `by rw [smul_smul, inv_mul_cancel_right]`. Simplify using `only at hzk ⊢`. Rewrite using `[e, ← hzfix (g1 * g0⁻¹), comp_equivariant π V c hc1 hc2 hc3 hc4 hπ, hzk, map_zero]`.

Conclude with `comp_outside V c hc3 hzO hl`. Rewrite `hz0` using `[hz, sub_eq_zero]`. Rewrite using `[hz0]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)`.
-/
theorem mem_span_of_fixed (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i))
    (hline : ∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) (i : ι) {x y : M}
    (hx : ∀ g, π g x = x) (hy : ∀ g, π g y = y) (hxO : x ∈ WA V (orbit G i))
    (hyO : y ∈ WA V (orbit G i)) (hy0 : y ≠ 0) : x ∈ Submodule.span ℂ {y} := by
  obtain ⟨F, hF⟩ := hc4 y
  obtain ⟨k, -, hk⟩ : ∃ k ∈ F, c k y ≠ 0 := by
    by_contra! h
    exact hy0 (by rw [hF]; exact Finset.sum_eq_zero h)
  have hkO : k ∈ orbit G i := by
    by_contra hkO
    exact hk (comp_outside V c hc3 hyO hkO)
  obtain ⟨v, hv⟩ := hline k
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hv (hc1 k y))
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hv (hc1 k x))
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hk (by rw [← hb, zero_smul])
  set z := x - (a / b) • y with hz
  have hzk : c k z = 0 := by
    rw [hz, map_sub, map_smul, ← ha, ← hb, smul_smul, div_mul_cancel₀ a hb0, sub_self]
  have hzfix : ∀ g, π g z = z := fun g => by rw [hz, map_sub, map_smul, hx, hy]
  have hzO : z ∈ WA V (orbit G i) := sub_mem hxO (Submodule.smul_mem _ _ hyO)
  have hz0 : z = 0 := by
    refine eq_zero_of_comp c hc4 fun l => ?_
    by_cases hl : l ∈ orbit G i
    · obtain ⟨g0, rfl⟩ := hkO
      obtain ⟨g1, rfl⟩ := hl
      have e : g1 • i = (g1 * g0⁻¹) • (g0 • i) := by rw [smul_smul, inv_mul_cancel_right]
      simp only at hzk ⊢
      rw [e, ← hzfix (g1 * g0⁻¹), comp_equivariant π V c hc1 hc2 hc3 hc4 hπ, hzk, map_zero]
    · exact comp_outside V c hc3 hzO hl
  rw [hz, sub_eq_zero] at hz0
  rw [hz0]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y)

end comp

end GlobalTheory.GradedFixed

namespace GlobalTheory.GradedFixed

variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Proceed by induction on `F using Finset.induction_on with`. Consider the case `empty`. Introduce `_ u _ hu`. Establish `: u = 0` using `by simpa [WA] using hu`. Rewrite using `[this]`.

Conclude with `zero_mem S`. Consider the case `insert i F hi ih`. Introduce `hT u hu huF`. Establish `hset : (⋃ j ∈ insert i F, orbit G j) = orbit G i ∪ ((⋃ j ∈ F, orbit G j) \ orbit G i)`. Rewrite using `[Finset.set_biUnion_insert, Set.union_diff_self]`.

Rewrite `huF` using `[hset, WA_union, Submodule.mem_sup]`. Take `⟨a, ha, b, hb, rfl⟩` from `huF`. Establish `hA : ∀ (g : G), ∀ j ∈ orbit G i, g • j ∈ orbit G i` using `fun g j hj => orbit_stable i g hj`. Establish `hU : ∀ (g : G), ∀ j ∈ (⋃ k ∈ F, orbit G k), g • j ∈ (⋃ k ∈ F, orbit G k)`. Introduce `g j hj`.

Take `⟨k, hk, hjk⟩` from `Set.mem_iUnion₂.mp hj`. Conclude with `Set.mem_iUnion₂.mpr ⟨k, hk, orbit_stable k g hjk⟩`. Establish `hB : ∀ (g : G), ∀ j ∈ ((⋃ k ∈ F, orbit G k) \ orbit G i), g • j ∈ ((⋃ k ∈ F, orbit G k) \ orbit G i)`. Introduce `g j hj`. Conclude with `⟨hU g j hj.1, fun h => hj.2 (by simpa using orbit_stable i g⁻¹ h)⟩`.

Establish `hAB : Disjoint (orbit G i) ((⋃ k ∈ F, orbit G k) \ orbit G i)` using `Set.disjoint_sdiff_right`. Establish `hafix` using `fixed_part π V hV hπ hA hB hAB ha hb hu`. Establish `hbfix : ∀ g, π g b = b` using `fixed_part π V hV hπ hB hA hAB.symm hb ha (fun g => by rw [add_comm]; exact hu g)`. Conclude with `add_mem (hT i (Finset.mem_insert_self i F) a hafix ha) (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)) b hbfix (WA_mono V Set.diff_subset hb))`.
-/
theorem mem_of_orbits (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M) (hV : iSupIndep V)
    (hπ : ∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) (S : Submodule ℂ M) (F : Finset ι) :
    (∀ i ∈ F, ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S) →
    ∀ u, (∀ g, π g u = u) → u ∈ WA V (⋃ i ∈ F, orbit G i) → u ∈ S := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro _ u _ hu
    have : u = 0 := by simpa [WA] using hu
    rw [this]; exact zero_mem S
  | insert i F hi ih =>
    intro hT u hu huF
    have hset : (⋃ j ∈ insert i F, orbit G j) = orbit G i ∪ ((⋃ j ∈ F, orbit G j) \ orbit G i) := by
      rw [Finset.set_biUnion_insert, Set.union_diff_self]
    rw [hset, WA_union, Submodule.mem_sup] at huF
    obtain ⟨a, ha, b, hb, rfl⟩ := huF
    have hA : ∀ (g : G), ∀ j ∈ orbit G i, g • j ∈ orbit G i := fun g j hj => orbit_stable i g hj
    have hU : ∀ (g : G), ∀ j ∈ (⋃ k ∈ F, orbit G k), g • j ∈ (⋃ k ∈ F, orbit G k) := by
      intro g j hj
      obtain ⟨k, hk, hjk⟩ := Set.mem_iUnion₂.mp hj
      exact Set.mem_iUnion₂.mpr ⟨k, hk, orbit_stable k g hjk⟩
    have hB : ∀ (g : G), ∀ j ∈ ((⋃ k ∈ F, orbit G k) \ orbit G i),
        g • j ∈ ((⋃ k ∈ F, orbit G k) \ orbit G i) := by
      intro g j hj
      exact ⟨hU g j hj.1, fun h => hj.2 (by simpa using orbit_stable i g⁻¹ h)⟩
    have hAB : Disjoint (orbit G i) ((⋃ k ∈ F, orbit G k) \ orbit G i) := Set.disjoint_sdiff_right
    have hafix := fixed_part π V hV hπ hA hB hAB ha hb hu
    have hbfix : ∀ g, π g b = b :=
      fixed_part π V hV hπ hB hA hAB.symm hb ha (fun g => by rw [add_comm]; exact hu g)
    exact add_mem (hT i (Finset.mem_insert_self i F) a hafix ha)
      (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)) b hbfix (WA_mono V Set.diff_subset hb))

end GlobalTheory.GradedFixed

namespace GlobalTheory

open GlobalTheory.GradedFixed in

/- English proof (translation)
Introduce `G ι M _ _ _ _ π V hV htop hline hπ μ hμ S hS hstep`. Take `⟨c, hc1, hc2, hc3, hc4⟩` from `exists_comp V hV htop`. Establish `hsum : ∀ (p : ι → Prop) (u : M), (∀ l, ¬ p l → c l u = 0) → (∀ i, p i → ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S) → (∀ g, π g u = u) → u ∈ S` using `by classical`. Introduce `p u hp hgood hu`. Take `⟨F, hF⟩` from `hc4 u`.

Establish `hF' : u = ∑ j ∈ F.filter p, c j u`. Rewrite using `[Finset.sum_filter_of_ne (fun j _ h => by_contra fun hpj => h (hp j hpj))]`. Conclude with `hF`. Use `mem_of_orbits π V hV hπ S (F.filter p) (fun j hj => hgood j (Finset.mem_filter.mp hj).2) u hu ?_` and prove the remaining obligations. Conclude with `mem_WA_of_sum V c hc1 hc3 (fun j hj => Set.mem_iUnion₂.mpr ⟨j, hj, (mem_orbit_self j : j ∈ orbit G j)⟩) u hF'`.

Establish `key : ∀ m i, μ i = m → ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `i hi x hx hxO`.

Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`. Conclude with `zero_mem S`. Take `⟨v, hvS, u, hu, hvu, hvu0⟩` from `hstep i ⟨x, hx0, hx, by rw [iSup_orbit]; exact hxO⟩`. Rewrite `hvu` using `[iSup_orbit]`.

Establish `huW : u ∈ WA V {j | μ j < μ i}` using `hu`. Establish `hsub : {j | μ j < μ i} ⊆ (orbit G i)ᶜ`. Introduce `j hj hjO`. Take `⟨g, rfl⟩` from `hjO`. Simplify using `[hμ] at hj`.

Establish `hcompl : ∀ (g : G), ∀ j ∈ (orbit G i)ᶜ, g • j ∈ (orbit G i)ᶜ` using `fun g j hj hgj => hj (by simpa using orbit_stable i g⁻¹ hgj)`. Establish `hfa : ∀ g, π g (v - u) = v - u` using `fixed_part π V hV hπ (fun g j hj => orbit_stable i g hj) hcompl disjoint_compl_right hvu (WA_mono V hsub huW) (fun g => by rw [sub_add_cancel]; exact hS v hvS g)`. Establish `hufix : ∀ g, π g u = u` using `fun g => by`. Establish `h1` using `hfa g`. Rewrite `h1` using `[map_sub, hS v hvS g]`.

Conclude with `sub_right_injective h1`. Establish `huS : u ∈ S` using `hsum (fun j => μ j < μ i) u (fun l hl => comp_outside V c hc3 huW hl) (fun j hj => ih (μ j) (hi ▸ hj) j rfl) hufix`. Establish `hvuS : v - u ∈ S` using `sub_mem hvS huS`. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.mp (mem_span_of_fixed π V c hc1 hc2 hc3 hc4 hπ hline i hx hfa hxO hvu hvu0)`. Rewrite using `[← hr]`.

Conclude with `S.smul_mem r hvuS`. Introduce `w hw`. Conclude with `hsum (fun _ => True) w (fun l hl => absurd trivial hl) (fun i _ => key (μ i) i rfl) hw`.
-/
theorem fixed_mem_of_orbit_height : ∀ {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M), iSupIndep V → (⨆ i, V i) = ⊤ →
    (∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) → (∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) →
    ∀ (μ : ι → ℕ), (∀ (g : G) (i : ι), μ (g • i) = μ i) → ∀ (S : Submodule ℂ M), (∀ v ∈ S, ∀ g, π g v = v) →
    (∀ i, (∃ w : M, w ≠ 0 ∧ (∀ g, π g w = w) ∧ w ∈ ⨆ g : G, V (g • i)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ i), V j, v - u ∈ (⨆ g : G, V (g • i)) ∧ v - u ≠ 0) →
    ∀ w : M, (∀ g, π g w = w) → w ∈ S := by
  intro G ι M _ _ _ _ π V hV htop hline hπ μ hμ S hS hstep
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := exists_comp V hV htop
  have hsum : ∀ (p : ι → Prop) (u : M), (∀ l, ¬ p l → c l u = 0) →
      (∀ i, p i → ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S) →
      (∀ g, π g u = u) → u ∈ S := by
    classical
    intro p u hp hgood hu
    obtain ⟨F, hF⟩ := hc4 u
    have hF' : u = ∑ j ∈ F.filter p, c j u := by
      rw [Finset.sum_filter_of_ne (fun j _ h => by_contra fun hpj => h (hp j hpj))]
      exact hF
    refine mem_of_orbits π V hV hπ S (F.filter p)
      (fun j hj => hgood j (Finset.mem_filter.mp hj).2) u hu ?_
    exact mem_WA_of_sum V c hc1 hc3
      (fun j hj => Set.mem_iUnion₂.mpr ⟨j, hj, (mem_orbit_self j : j ∈ orbit G j)⟩) u hF'
  have key : ∀ m i, μ i = m → ∀ x, (∀ g, π g x = x) → x ∈ WA V (orbit G i) → x ∈ S := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro i hi x hx hxO
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem S
    obtain ⟨v, hvS, u, hu, hvu, hvu0⟩ := hstep i ⟨x, hx0, hx, by rw [iSup_orbit]; exact hxO⟩
    rw [iSup_orbit] at hvu
    have huW : u ∈ WA V {j | μ j < μ i} := hu
    have hsub : {j | μ j < μ i} ⊆ (orbit G i)ᶜ := by
      intro j hj hjO
      obtain ⟨g, rfl⟩ := hjO
      simp [hμ] at hj
    have hcompl : ∀ (g : G), ∀ j ∈ (orbit G i)ᶜ, g • j ∈ (orbit G i)ᶜ :=
      fun g j hj hgj => hj (by simpa using orbit_stable i g⁻¹ hgj)
    have hfa : ∀ g, π g (v - u) = v - u :=
      fixed_part π V hV hπ (fun g j hj => orbit_stable i g hj) hcompl disjoint_compl_right hvu
        (WA_mono V hsub huW) (fun g => by rw [sub_add_cancel]; exact hS v hvS g)
    have hufix : ∀ g, π g u = u := fun g => by
      have h1 := hfa g
      rw [map_sub, hS v hvS g] at h1
      exact sub_right_injective h1
    have huS : u ∈ S := hsum (fun j => μ j < μ i) u (fun l hl => comp_outside V c hc3 huW hl)
      (fun j hj => ih (μ j) (hi ▸ hj) j rfl) hufix
    have hvuS : v - u ∈ S := sub_mem hvS huS
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp
      (mem_span_of_fixed π V c hc1 hc2 hc3 hc4 hπ hline i hx hfa hxO hvu hvu0)
    rw [← hr]
    exact S.smul_mem r hvuS
  intro w hw
  exact hsum (fun _ => True) w (fun l hl => absurd trivial hl) (fun i _ => key (μ i) i rfl) hw

end GlobalTheory
