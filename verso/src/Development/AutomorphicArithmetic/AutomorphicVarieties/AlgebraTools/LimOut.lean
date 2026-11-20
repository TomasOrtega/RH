import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Introduce `G Z ι _ _ _ _ _ _ _ _ _ _ hG U K _ f hf hK`. Take `⟨s, hsfin, hsgen⟩` from `hG`. Choose the witnesses or unpack the hypotheses as in `⟨F0, hF0⟩ : ∃ F0 : G → Z, ∀ g, Tendsto (fun i => f i g) (U : Filter ι) (nhds (F0 g)) := by`. Use `⟨fun g => (U.map (fun i => f i g)).lim, fun g => ?_⟩` and prove the remaining obligations. Establish `h` using `(U.map (fun i => f i g)).le_nhds_lim`.

Rewrite `h` using `[Ultrafilter.coe_map]`. Conclude with `h`. Establish `hone : F0 1 = 1` using `tendsto_nhds_unique (hF0 1) (by simp only [map_one]; exact tendsto_const_nhds)`. Establish `hmul : ∀ a b, F0 (a * b) = F0 a * F0 b` using `fun a b => tendsto_nhds_unique (hF0 (a * b)) (by simp only [map_mul]; exact (hF0 a).mul (hF0 b))`. Take `⟨F, hF⟩ : ∃ F : G →* Z, ∀ g, Tendsto (fun i => f i g) (U : Filter ι) (nhds (F g))` from `⟨{ toFun := F0, map_one' := hone, map_mul' := hmul }, hF0⟩`.

Establish `agree : ∀ (V : OpenNormalSubgroup Z) (i j : ι), (∀ x ∈ s, (F x)⁻¹ * f i x ∈ V.toSubgroup) → (∀ x ∈ s, (F x)⁻¹ * f j x ∈ V.toSubgroup) → ∀ g, (f j g)⁻¹ * f i g ∈ V.toSubgroup`. Introduce `V i j hi hj g`. Set `H : Subgroup G` to `{ carrier := {g | (f j g)⁻¹ * f i g ∈ V.toSubgroup} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_mul] at *`.

Use `V.toSubgroup.mul_mem (V.isNormal'.conj_mem _ ha (f j b)⁻¹) hb` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`.

Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq, map_inv] at *`. Use `V.isNormal'.conj_mem _ (V.toSubgroup.inv_mem ha) (f j a)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group }`.

Establish `hHc : IsClosed (H : Set G)` using `V.toOpenSubgroup.isClosed.preimage (((hf j).inv).mul (hf i))`. Establish `hsH : Subgroup.closure s ≤ H`. Rewrite using `[Subgroup.closure_le]`. Introduce `x hx`. Use `show (f j x)⁻¹ * f i x ∈ V.toSubgroup`.

Use `V.toSubgroup.mul_mem (V.toSubgroup.inv_mem (hj x hx)) (hi x hx)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`. Establish `hg : g ∈ (Subgroup.closure s).topologicalClosure`. Rewrite using `[← SetLike.mem_coe, Subgroup.topologicalClosure_coe, hsgen.closure_eq]`.

Discharge the goal by the elementary cases of `trivial`. Conclude with `Subgroup.topologicalClosure_minimal _ hsH hHc hg`. Establish `key : ∀ V : OpenNormalSubgroup Z, ∀ᶠ i in (U : Filter ι), ∀ g, (F g)⁻¹ * f i g ∈ V.toSubgroup`. Introduce `V`. Establish `hs : ∀ᶠ i in (U : Filter ι), ∀ x ∈ s, (F x)⁻¹ * f i x ∈ V.toSubgroup`.

Use `(Filter.eventually_all_finite hsfin).2 (fun x _ => ?_)` and prove the remaining obligations. Establish `hopen : IsOpen {z : Z | (F x)⁻¹ * z ∈ V.toSubgroup}` using `V.toOpenSubgroup.isOpen.preimage (continuous_mul_left _)`. Conclude with `(hF x).eventually (hopen.mem_nhds (by simp))`. Take `⟨j, hj⟩` from `hs.exists`. Use `filter_upwards [hs] with i hi g`.

Establish `hC : IsClosed {z : Z | (f j g)⁻¹ * z ∈ V.toSubgroup}` using `V.toOpenSubgroup.isClosed.preimage (continuous_mul_left _)`. Establish `h1 : (f j g)⁻¹ * F g ∈ V.toSubgroup` using `hC.mem_of_tendsto (hF g) (hs.mono fun k hk => agree V k j hk hj g)`. Establish `h2` using `agree V i j hi hj g`. Use `V.toSubgroup.mul_mem (V.toSubgroup.inv_mem h1) h2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `group`. Establish `hFc : Continuous F`. Apply `continuous_of_continuousAt_one F` to reduce the goal to its premises. Rewrite using `[ContinuousAt, map_one]`. Introduce `W hW`.

Take `⟨t, htW, hto, h1t⟩` from `mem_nhds_iff.1 hW`. Take `⟨V, hV⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hto h1t`. Take `⟨i, hi⟩` from `(key V).exists`. Establish `hmem : {g : G | f i g ∈ V.toSubgroup} ∈ nhds (1 : G)` using `(V.toOpenSubgroup.isOpen.preimage (hf i)).mem_nhds (by simp)`. Use `Filter.mem_map.2 (Filter.mem_of_superset hmem (fun g hg => ?_))` and prove the remaining obligations.

Apply `htW` to reduce the goal to its premises. Apply `hV` to reduce the goal to its premises. Use `V.toSubgroup.mul_mem hg (V.toSubgroup.inv_mem (hi g))` as an intermediate fact. Express the relevant statement in the definitionally equal form `F g ∈ V.toSubgroup`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `group`. Use `⟨F, hFc, ?_, key, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Rewrite using `[MonoidHom.mem_ker]`. Establish `hall : ∀ V : OpenNormalSubgroup Z, F g ∈ V.toSubgroup`.

Introduce `V`. Set `O : OpenNormalSubgroup G` to `{ toSubgroup := V.toSubgroup.comap F isOpen' := V.toOpenSubgroup.isOpen.preimage hFc isNormal' := V.isNormal'.comap F }`. Rewrite `hg` using `[mem_limKer]`. Take `⟨i, hi1, hi2⟩` from `((hg O).and (key V)).exists`. Establish `hle : K i ⊔ (O.toOpenSubgroup : Subgroup G) ≤ V.toSubgroup.comap (f i)`.

Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hx'` using `hK i hx`. Rewrite `hx'` using `[MonoidHom.mem_ker]`. Use `show f i x ∈ V.toSubgroup`.

Rewrite using `[hx']`. Conclude with `one_mem _`. Introduce `x hx`. Establish `hx' : F x ∈ V.toSubgroup` using `hx`. Use `show f i x ∈ V.toSubgroup`.

Use `V.toSubgroup.mul_mem hx' (hi2 x)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`. Establish `hfg : f i g ∈ V.toSubgroup` using `hle hi1`. Use `V.toSubgroup.mul_mem hfg (V.toSubgroup.inv_mem (hi2 g))` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`. Assume the negation of the conclusion as `hne`. Take `⟨V, hV⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_compl_singleton (x := F g)) (Set.mem_compl_singleton_iff.2 (Ne.symm hne))`. Conclude with `hV (hall V) rfl`.

Introduce `hsurj z`. Establish `hcl : IsClosed (Set.range F)` using `(isCompact_range hFc).isClosed`. Establish `hz : z ∈ closure (Set.range F)`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `t ht`.

Establish `hW : (fun y => z * y) ⁻¹' t ∈ nhds (1 : Z)` using `(continuous_mul_left z).continuousAt.preimage_mem_nhds (by rwa [mul_one])`. Take `⟨u, huW, huo, h1u⟩` from `mem_nhds_iff.1 hW`. Take `⟨V, hV⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one huo h1u`. Take `⟨i, hi⟩` from `(key V).exists`. Take `⟨g, hg⟩` from `hsurj i z`.

Use `⟨F g, ?_, g, rfl⟩` and prove the remaining obligations. Establish `hv : z⁻¹ * F g ∈ V.toSubgroup`. Use `V.toSubgroup.inv_mem (hi g)` as an intermediate fact. Rewrite `this` using `[hg]`. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `group`. Use `huW (hV hv)` as an intermediate fact. Simplify using `using this`. Rewrite `hz` using `[hcl.closure_eq]`. Conclude with `hz`.
-/
theorem UpperTheory.V.AlgebraTools.exists_lim_hom_out :
    ∀ (G Z ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z], TopFG G → ∀ (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal] (f : ι → G →* Z),
      (∀ i, Continuous (f i)) → (∀ i, K i ≤ (f i).ker) →
      ∃ F : G →* Z, Continuous F ∧ limKer (U : Filter ι) K ≤ F.ker ∧
        (∀ V : OpenNormalSubgroup Z, ∀ᶠ i in (U : Filter ι), ∀ g, (F g)⁻¹ * f i g ∈ V.toSubgroup) ∧
        ((∀ i, Function.Surjective (f i)) → Function.Surjective F) := by
  intro G Z ι _ _ _ _ _ _ _ _ _ _ hG U K _ f hf hK
  obtain ⟨s, hsfin, hsgen⟩ := hG
  obtain ⟨F0, hF0⟩ : ∃ F0 : G → Z, ∀ g, Tendsto (fun i => f i g) (U : Filter ι) (nhds (F0 g)) := by
    refine ⟨fun g => (U.map (fun i => f i g)).lim, fun g => ?_⟩
    have h := (U.map (fun i => f i g)).le_nhds_lim
    rw [Ultrafilter.coe_map] at h
    exact h
  have hone : F0 1 = 1 :=
    tendsto_nhds_unique (hF0 1) (by simp only [map_one]; exact tendsto_const_nhds)
  have hmul : ∀ a b, F0 (a * b) = F0 a * F0 b := fun a b =>
    tendsto_nhds_unique (hF0 (a * b)) (by simp only [map_mul]; exact (hF0 a).mul (hF0 b))
  obtain ⟨F, hF⟩ : ∃ F : G →* Z, ∀ g, Tendsto (fun i => f i g) (U : Filter ι) (nhds (F g)) :=
    ⟨{ toFun := F0, map_one' := hone, map_mul' := hmul }, hF0⟩
  have agree : ∀ (V : OpenNormalSubgroup Z) (i j : ι),
      (∀ x ∈ s, (F x)⁻¹ * f i x ∈ V.toSubgroup) → (∀ x ∈ s, (F x)⁻¹ * f j x ∈ V.toSubgroup) →
      ∀ g, (f j g)⁻¹ * f i g ∈ V.toSubgroup := by
    intro V i j hi hj g
    let H : Subgroup G :=
      { carrier := {g | (f j g)⁻¹ * f i g ∈ V.toSubgroup}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul] at *
          have := V.toSubgroup.mul_mem (V.isNormal'.conj_mem _ ha (f j b)⁻¹) hb
          convert this using 1
          group
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq, map_inv] at *
          have := V.isNormal'.conj_mem _ (V.toSubgroup.inv_mem ha) (f j a)
          convert this using 1
          group }
    have hHc : IsClosed (H : Set G) :=
      V.toOpenSubgroup.isClosed.preimage (((hf j).inv).mul (hf i))
    have hsH : Subgroup.closure s ≤ H := by
      rw [Subgroup.closure_le]
      intro x hx
      show (f j x)⁻¹ * f i x ∈ V.toSubgroup
      have := V.toSubgroup.mul_mem (V.toSubgroup.inv_mem (hj x hx)) (hi x hx)
      convert this using 1
      group
    have hg : g ∈ (Subgroup.closure s).topologicalClosure := by
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe, hsgen.closure_eq]
      trivial
    exact Subgroup.topologicalClosure_minimal _ hsH hHc hg
  have key : ∀ V : OpenNormalSubgroup Z, ∀ᶠ i in (U : Filter ι), ∀ g, (F g)⁻¹ * f i g ∈ V.toSubgroup := by
    intro V
    have hs : ∀ᶠ i in (U : Filter ι), ∀ x ∈ s, (F x)⁻¹ * f i x ∈ V.toSubgroup := by
      refine (Filter.eventually_all_finite hsfin).2 (fun x _ => ?_)
      have hopen : IsOpen {z : Z | (F x)⁻¹ * z ∈ V.toSubgroup} :=
        V.toOpenSubgroup.isOpen.preimage (continuous_mul_left _)
      exact (hF x).eventually (hopen.mem_nhds (by simp))
    obtain ⟨j, hj⟩ := hs.exists
    filter_upwards [hs] with i hi g
    have hC : IsClosed {z : Z | (f j g)⁻¹ * z ∈ V.toSubgroup} :=
      V.toOpenSubgroup.isClosed.preimage (continuous_mul_left _)
    have h1 : (f j g)⁻¹ * F g ∈ V.toSubgroup :=
      hC.mem_of_tendsto (hF g) (hs.mono fun k hk => agree V k j hk hj g)
    have h2 := agree V i j hi hj g
    have := V.toSubgroup.mul_mem (V.toSubgroup.inv_mem h1) h2
    convert this using 1
    group
  have hFc : Continuous F := by
    apply continuous_of_continuousAt_one F
    rw [ContinuousAt, map_one]
    intro W hW
    obtain ⟨t, htW, hto, h1t⟩ := mem_nhds_iff.1 hW
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hto h1t
    obtain ⟨i, hi⟩ := (key V).exists
    have hmem : {g : G | f i g ∈ V.toSubgroup} ∈ nhds (1 : G) :=
      (V.toOpenSubgroup.isOpen.preimage (hf i)).mem_nhds (by simp)
    refine Filter.mem_map.2 (Filter.mem_of_superset hmem (fun g hg => ?_))
    apply htW
    apply hV
    have := V.toSubgroup.mul_mem hg (V.toSubgroup.inv_mem (hi g))
    change F g ∈ V.toSubgroup
    convert this using 1
    group
  refine ⟨F, hFc, ?_, key, ?_⟩
  · intro g hg
    rw [MonoidHom.mem_ker]
    have hall : ∀ V : OpenNormalSubgroup Z, F g ∈ V.toSubgroup := by
      intro V
      let O : OpenNormalSubgroup G :=
        { toSubgroup := V.toSubgroup.comap F
          isOpen' := V.toOpenSubgroup.isOpen.preimage hFc
          isNormal' := V.isNormal'.comap F }
      rw [mem_limKer] at hg
      obtain ⟨i, hi1, hi2⟩ := ((hg O).and (key V)).exists
      have hle : K i ⊔ (O.toOpenSubgroup : Subgroup G) ≤ V.toSubgroup.comap (f i) := by
        refine sup_le ?_ ?_
        · intro x hx
          have hx' := hK i hx
          rw [MonoidHom.mem_ker] at hx'
          show f i x ∈ V.toSubgroup
          rw [hx']
          exact one_mem _
        · intro x hx
          have hx' : F x ∈ V.toSubgroup := hx
          show f i x ∈ V.toSubgroup
          have := V.toSubgroup.mul_mem hx' (hi2 x)
          convert this using 1
          group
      have hfg : f i g ∈ V.toSubgroup := hle hi1
      have := V.toSubgroup.mul_mem hfg (V.toSubgroup.inv_mem (hi2 g))
      convert this using 1
      group
    by_contra hne
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isOpen_compl_singleton (x := F g)) (Set.mem_compl_singleton_iff.2 (Ne.symm hne))
    exact hV (hall V) rfl
  · intro hsurj z
    have hcl : IsClosed (Set.range F) := (isCompact_range hFc).isClosed
    have hz : z ∈ closure (Set.range F) := by
      rw [mem_closure_iff_nhds]
      intro t ht
      have hW : (fun y => z * y) ⁻¹' t ∈ nhds (1 : Z) :=
        (continuous_mul_left z).continuousAt.preimage_mem_nhds (by rwa [mul_one])
      obtain ⟨u, huW, huo, h1u⟩ := mem_nhds_iff.1 hW
      obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one huo h1u
      obtain ⟨i, hi⟩ := (key V).exists
      obtain ⟨g, hg⟩ := hsurj i z
      refine ⟨F g, ?_, g, rfl⟩
      have hv : z⁻¹ * F g ∈ V.toSubgroup := by
        have := V.toSubgroup.inv_mem (hi g)
        rw [hg] at this
        convert this using 1
        group
      have := huW (hV hv)
      simpa using this
    rw [hcl.closure_eq] at hz
    exact hz
