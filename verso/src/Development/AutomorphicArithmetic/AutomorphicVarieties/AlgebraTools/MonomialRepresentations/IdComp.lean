import Mathlib

open Polynomial Matrix

/- English proof (translation)
Use `⟨hZ.1.image e e.continuous.continuousOn, fun y hy hsub => ?_⟩` and prove the remaining obligations. Establish `h1 : Z ⊆ e.symm '' y`. Introduce `z hz`. Conclude with `⟨e z, hsub ⟨z, hz, rfl⟩, e.symm_apply_apply z⟩`. Establish `h2` using `hZ.2 (hy.image e.symm e.symm.continuous.continuousOn) h1`.

Introduce `w hw`. Conclude with `⟨e.symm w, h2 ⟨w, hw, rfl⟩, e.apply_symm_apply w⟩`.
-/
private theorem comp_image {G : Type} [TopologicalSpace G] (e : G ≃ₜ G) {Z : Set G}
    (hZ : Z ∈ irreducibleComponents G) : e '' Z ∈ irreducibleComponents G := by
  refine ⟨hZ.1.image e e.continuous.continuousOn, fun y hy hsub => ?_⟩
  have h1 : Z ⊆ e.symm '' y := by
    intro z hz
    exact ⟨e z, hsub ⟨z, hz, rfl⟩, e.symm_apply_apply z⟩
  have h2 := hZ.2 (hy.image e.symm e.symm.continuous.continuousOn) h1
  intro w hw
  exact ⟨e.symm w, h2 ⟨w, hw, rfl⟩, e.apply_symm_apply w⟩

/- English proof (translation)
Take `⟨Z, hZ, haZ⟩ : ∃ Z ∈ irreducibleComponents G, a ∈ Z` from `⟨_, irreducibleComponent_mem_irreducibleComponents a, mem_irreducibleComponent⟩`. Establish `hfin : (irreducibleComponents G \ {Z}).Finite` using `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.diff`. Establish `hnot : ¬ Z ⊆ ⋃₀ (irreducibleComponents G \ {Z})`. Introduce `hsub`. Take `⟨W, hW, hZW⟩` from `(isIrreducible_iff_sUnion_isClosed.1 hZ.1) hfin.toFinset (fun W hW => isClosed_of_mem_irreducibleComponents W (hfin.mem_toFinset.1 hW).1) (by simpa using hsub)`.

Rewrite `hW` using `[hfin.mem_toFinset]`. Conclude with `hW.2 (Set.mem_singleton_iff.2 (le_antisymm (hZ.2 hW.1.1 hZW) hZW))`. Take `⟨x, hxZ, hxn⟩` from `Set.not_subset.1 hnot`. Establish `key : ∀ Y ∈ irreducibleComponents G, x ∈ Y → Y = Z`. Introduce `Y hY hxY`.

Assume the negation of the conclusion as `hne`. Conclude with `hxn ⟨Y, ⟨hY, hne⟩, hxY⟩`. Use `⟨x, fun Z' hZ' W' hW' hx1 hx2 => ?_⟩` and prove the remaining obligations. Rewrite using `[key Z' hZ' hx1, key W' hW' hx2]`.
-/
private theorem exists_unique_pt {G : Type} [TopologicalSpace G] [TopologicalSpace.NoetherianSpace G]
    (a : G) : ∃ x : G, ∀ Z ∈ irreducibleComponents G, ∀ W ∈ irreducibleComponents G,
      x ∈ Z → x ∈ W → Z = W := by
  classical
  obtain ⟨Z, hZ, haZ⟩ : ∃ Z ∈ irreducibleComponents G, a ∈ Z :=
    ⟨_, irreducibleComponent_mem_irreducibleComponents a, mem_irreducibleComponent⟩
  have hfin : (irreducibleComponents G \ {Z}).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.diff
  have hnot : ¬ Z ⊆ ⋃₀ (irreducibleComponents G \ {Z}) := by
    intro hsub
    obtain ⟨W, hW, hZW⟩ := (isIrreducible_iff_sUnion_isClosed.1 hZ.1) hfin.toFinset
      (fun W hW => isClosed_of_mem_irreducibleComponents W (hfin.mem_toFinset.1 hW).1)
      (by simpa using hsub)
    rw [hfin.mem_toFinset] at hW
    exact hW.2 (Set.mem_singleton_iff.2 (le_antisymm (hZ.2 hW.1.1 hZW) hZW))
  obtain ⟨x, hxZ, hxn⟩ := Set.not_subset.1 hnot
  have key : ∀ Y ∈ irreducibleComponents G, x ∈ Y → Y = Z := by
    intro Y hY hxY
    by_contra hne
    exact hxn ⟨Y, ⟨hY, hne⟩, hxY⟩
  refine ⟨x, fun Z' hZ' W' hW' hx1 hx2 => ?_⟩
  rw [key Z' hZ' hx1, key W' hW' hx2]

/- English proof (translation)
Introduce `G _ _ _ hL hR`. Set `hl : G → G ≃ₜ G` to `fun g => { toFun := fun x => g * x, invFun := fun x => g⁻¹ * x, left_inv := fun x => by simp, right_inv := fun x => by simp, continuous_toFun := hL g, continuous_invFun := hL g⁻¹ }`. Set `hr : G → G ≃ₜ G` to `fun g => { toFun := fun x => x * g, invFun := fun x => x * g⁻¹, left_inv := fun x => by simp, right_inv := fun x => by simp, continuous_toFun := hR g, continuous_invFun := hR g⁻¹ }`. Take `⟨x, hx⟩` from `exists_unique_pt (1 : G)`. Establish `uniq : ∀ y : G, ∀ Z ∈ irreducibleComponents G, ∀ W ∈ irreducibleComponents G, y ∈ Z → y ∈ W → Z = W`.

Introduce `y Z hZ W hW hyZ hyW`. Establish `hxy : (hl (x * y⁻¹)) y = x` using `by show x * y⁻¹ * y = x`. Simplify using the standard rewrite rules. Establish `h` using `hx _ (comp_image (hl (x * y⁻¹)) hZ) _ (comp_image (hl (x * y⁻¹)) hW) ⟨y, hyZ, hxy⟩ ⟨y, hyW, hxy⟩`. Conclude with `Set.image_injective.2 (hl (x * y⁻¹)).injective h`.

Take `⟨C, hC, h1C⟩ : ∃ C ∈ irreducibleComponents G, (1 : G) ∈ C` from `⟨_, irreducibleComponent_mem_irreducibleComponents 1, mem_irreducibleComponent⟩`. Set `N : Subgroup G` to `{ carrier := C one_mem' := h1C mul_mem' := fun {a b} ha hb => by`. Establish `e1 : (hl a) '' C = C` using `uniq a _ (comp_image (hl a) hC) _ hC ⟨1, h1C, by show a * 1 = a; simp⟩ ha`. Establish `h2 : a * b ∈ (hl a) '' C` using `⟨b, hb, rfl⟩`. Rewrite `h2` using `[e1]`. Then use the resulting hypothesis.

Use the proof step `inv_mem' := fun {a} ha => by`. Establish `e1 : (hl a⁻¹) '' C = C` using `uniq 1 _ (comp_image (hl a⁻¹) hC) _ hC ⟨a, ha, by show a⁻¹ * a = 1; simp⟩ h1C`. Establish `h2 : a⁻¹ ∈ (hl a⁻¹) '' C` using `⟨1, h1C, by show a⁻¹ * 1 = a⁻¹; simp⟩`. Rewrite using `[e1] at h2 }` and apply the resulting hypothesis. Establish `hNC : ∀ y, y ∈ N ↔ y ∈ C` using `fun y => Iff.rfl`.

Establish `hfinQ : Finite (G ⧸ N)`. Set `F : G ⧸ N → irreducibleComponents G` to `Quotient.lift (fun g => (⟨(hl g) '' C, comp_image (hl g) hC⟩ : irreducibleComponents G)) (by`. Introduce `a b hab`. Establish `hab' : a⁻¹ * b ∈ N` using `QuotientGroup.leftRel_apply.1 hab`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `uniq b _ (comp_image (hl a) hC) _ (comp_image (hl b) hC) ⟨a⁻¹ * b, hab', by show a * (a⁻¹ * b) = b; simp⟩ ⟨1, h1C, by show b * 1 = b; simp⟩)`. Establish `hFinj : Function.Injective F`. Introduce `p q hpq`. Take `⟨a, rfl⟩` from `QuotientGroup.mk_surjective p`. Take `⟨b, rfl⟩` from `QuotientGroup.mk_surjective q`.

Establish `h` using `congrArg Subtype.val hpq`. Express the relevant statement in the definitionally equal form `(hl a) '' C = (hl b) '' C at h`. Establish `hb : b ∈ (hl a) '' C`. Rewrite using `[h]`. Conclude with `⟨1, h1C, by show b * 1 = b; simp⟩`.

Take `⟨c, hc, hcb⟩` from `hb`. Express the relevant statement in the definitionally equal form `a * c = b at hcb`. Apply `QuotientGroup.eq.2` to reduce the goal to its premises. Rewrite using `[← hcb, inv_mul_cancel_left]`. Conclude with `hc`.

Use `haveI : Finite (irreducibleComponents G) := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype`. Conclude with `Finite.of_injective F hFinj`. Use `⟨N, ⟨fun n hn g => ?_⟩, Subgroup.finiteIndex_of_finite_quotient, isClosed_of_mem_irreducibleComponents C hC, hC.1, fun U hU => ?_⟩` and prove the remaining obligations. Establish `e1 : ((hl g).trans (hr g⁻¹)) '' C = C` using `uniq 1 _ (comp_image _ hC) _ hC ⟨1, h1C, by show g * 1 * g⁻¹ = 1; simp⟩ h1C`. Establish `h2 : g * n * g⁻¹ ∈ ((hl g).trans (hr g⁻¹)) '' C` using `⟨n, hn, rfl⟩`.

Rewrite `h2` using `[e1]`. Conclude with `h2`. Use `haveI : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex haveI := Fintype.ofFinite (G ⧸ U)`. Set `S : G ⧸ U → Set G` to `fun q => {y | y ∈ C ∧ (y : G ⧸ U) = q}`. Take `⟨z, hz, hCz⟩` from `(isIrreducible_iff_sUnion_isClosed.1 hC.1) (Finset.univ.image fun q => closure (S q)) (by simp [isClosed_closure]) (by`.

Introduce `y hy`. Simplify using `only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.sUnion_range, Set.mem_iUnion]`. Conclude with `⟨(y : G ⧸ U), subset_closure ⟨hy, rfl⟩⟩)`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hz`. Choose the witnesses or unpack the hypotheses as in `⟨n, hnC, hnq⟩ : (S q).Nonempty := by`.

Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[Set.not_nonempty_iff_eq_empty]`. Rewrite `hCz` using `[hne, closure_empty]`. Conclude with `hCz h1C`. Establish `hSsub : S q ⊆ (hl n) '' ((U ⊓ N : Subgroup G) : Set G)`.

Introduce and unpack `y ⟨hyC, hyq⟩`. Use `⟨n⁻¹ * y, Subgroup.mem_inf.2 ⟨?_, ?_⟩, by show n * (n⁻¹ * y) = y; simp⟩` and prove the remaining obligations. Conclude with `QuotientGroup.eq.1 (hnq.trans hyq.symm)`. Conclude with `N.mul_mem (N.inv_mem hnC) hyC`. Introduce `y hy`.

Establish `h3 : n * y ∈ closure ((hl n) '' ((U ⊓ N : Subgroup G) : Set G))` using `closure_mono hSsub (hCz (N.mul_mem hnC hy))`. Rewrite `h3` using `[← Homeomorph.image_closure]`. Take `⟨k, hk, hky⟩` from `h3`. Express the relevant statement in the definitionally equal form `n * k = n * y at hky`. Rewrite `hk` using `[mul_left_cancel hky]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.AlgebraTools.idComp :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [TopologicalSpace.NoetherianSpace G],
      (∀ g : G, Continuous (fun x => g * x)) → (∀ g : G, Continuous (fun x => x * g)) →
      ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ IsClosed (N : Set G) ∧ IsIrreducible (N : Set G) ∧
        ∀ U : Subgroup G, U.FiniteIndex → (N : Set G) ⊆ closure ((U ⊓ N : Subgroup G) : Set G) := by
  intro G _ _ _ hL hR
  classical
  let hl : G → G ≃ₜ G := fun g =>
    { toFun := fun x => g * x, invFun := fun x => g⁻¹ * x,
      left_inv := fun x => by simp, right_inv := fun x => by simp,
      continuous_toFun := hL g, continuous_invFun := hL g⁻¹ }
  let hr : G → G ≃ₜ G := fun g =>
    { toFun := fun x => x * g, invFun := fun x => x * g⁻¹,
      left_inv := fun x => by simp, right_inv := fun x => by simp,
      continuous_toFun := hR g, continuous_invFun := hR g⁻¹ }
  obtain ⟨x, hx⟩ := exists_unique_pt (1 : G)
  have uniq : ∀ y : G, ∀ Z ∈ irreducibleComponents G, ∀ W ∈ irreducibleComponents G,
      y ∈ Z → y ∈ W → Z = W := by
    intro y Z hZ W hW hyZ hyW
    have hxy : (hl (x * y⁻¹)) y = x := by
      show x * y⁻¹ * y = x
      simp
    have h := hx _ (comp_image (hl (x * y⁻¹)) hZ) _ (comp_image (hl (x * y⁻¹)) hW)
      ⟨y, hyZ, hxy⟩ ⟨y, hyW, hxy⟩
    exact Set.image_injective.2 (hl (x * y⁻¹)).injective h
  obtain ⟨C, hC, h1C⟩ : ∃ C ∈ irreducibleComponents G, (1 : G) ∈ C :=
    ⟨_, irreducibleComponent_mem_irreducibleComponents 1, mem_irreducibleComponent⟩
  let N : Subgroup G :=
    { carrier := C
      one_mem' := h1C
      mul_mem' := fun {a b} ha hb => by
        have e1 : (hl a) '' C = C := uniq a _ (comp_image (hl a) hC) _ hC
          ⟨1, h1C, by show a * 1 = a; simp⟩ ha
        have h2 : a * b ∈ (hl a) '' C := ⟨b, hb, rfl⟩
        rwa [e1] at h2
      inv_mem' := fun {a} ha => by
        have e1 : (hl a⁻¹) '' C = C := uniq 1 _ (comp_image (hl a⁻¹) hC) _ hC
          ⟨a, ha, by show a⁻¹ * a = 1; simp⟩ h1C
        have h2 : a⁻¹ ∈ (hl a⁻¹) '' C := ⟨1, h1C, by show a⁻¹ * 1 = a⁻¹; simp⟩
        rwa [e1] at h2 }
  have hNC : ∀ y, y ∈ N ↔ y ∈ C := fun y => Iff.rfl
  have hfinQ : Finite (G ⧸ N) := by
    let F : G ⧸ N → irreducibleComponents G :=
      Quotient.lift (fun g => (⟨(hl g) '' C, comp_image (hl g) hC⟩ : irreducibleComponents G))
        (by
          intro a b hab
          have hab' : a⁻¹ * b ∈ N := QuotientGroup.leftRel_apply.1 hab
          apply Subtype.ext
          exact uniq b _ (comp_image (hl a) hC) _ (comp_image (hl b) hC)
            ⟨a⁻¹ * b, hab', by show a * (a⁻¹ * b) = b; simp⟩ ⟨1, h1C, by show b * 1 = b; simp⟩)
    have hFinj : Function.Injective F := by
      intro p q hpq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      have h := congrArg Subtype.val hpq
      change (hl a) '' C = (hl b) '' C at h
      have hb : b ∈ (hl a) '' C := by
        rw [h]
        exact ⟨1, h1C, by show b * 1 = b; simp⟩
      obtain ⟨c, hc, hcb⟩ := hb
      change a * c = b at hcb
      apply QuotientGroup.eq.2
      rw [← hcb, inv_mul_cancel_left]
      exact hc
    haveI : Finite (irreducibleComponents G) :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.to_subtype
    exact Finite.of_injective F hFinj
  refine ⟨N, ⟨fun n hn g => ?_⟩, Subgroup.finiteIndex_of_finite_quotient,
    isClosed_of_mem_irreducibleComponents C hC, hC.1, fun U hU => ?_⟩
  · have e1 : ((hl g).trans (hr g⁻¹)) '' C = C := uniq 1 _ (comp_image _ hC) _ hC
      ⟨1, h1C, by show g * 1 * g⁻¹ = 1; simp⟩ h1C
    have h2 : g * n * g⁻¹ ∈ ((hl g).trans (hr g⁻¹)) '' C := ⟨n, hn, rfl⟩
    rw [e1] at h2
    exact h2
  · haveI : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
    haveI := Fintype.ofFinite (G ⧸ U)
    let S : G ⧸ U → Set G := fun q => {y | y ∈ C ∧ (y : G ⧸ U) = q}
    obtain ⟨z, hz, hCz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hC.1)
      (Finset.univ.image fun q => closure (S q)) (by simp [isClosed_closure]) (by
        intro y hy
        simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.sUnion_range,
          Set.mem_iUnion]
        exact ⟨(y : G ⧸ U), subset_closure ⟨hy, rfl⟩⟩)
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨n, hnC, hnq⟩ : (S q).Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, closure_empty] at hCz
      exact hCz h1C
    have hSsub : S q ⊆ (hl n) '' ((U ⊓ N : Subgroup G) : Set G) := by
      rintro y ⟨hyC, hyq⟩
      refine ⟨n⁻¹ * y, Subgroup.mem_inf.2 ⟨?_, ?_⟩, by show n * (n⁻¹ * y) = y; simp⟩
      · exact QuotientGroup.eq.1 (hnq.trans hyq.symm)
      · exact N.mul_mem (N.inv_mem hnC) hyC
    intro y hy
    have h3 : n * y ∈ closure ((hl n) '' ((U ⊓ N : Subgroup G) : Set G)) :=
      closure_mono hSsub (hCz (N.mul_mem hnC hy))
    rw [← Homeomorph.image_closure] at h3
    obtain ⟨k, hk, hky⟩ := h3
    change n * k = n * y at hky
    rwa [mul_left_cancel hky] at hk
