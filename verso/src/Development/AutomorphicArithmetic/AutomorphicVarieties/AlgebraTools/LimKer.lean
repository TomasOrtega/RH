import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Use `haveI := O.isNormal'`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hex : ∀ᶠ i in (U : Filter ι), ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup`. Use `h.mono fun i hi => ?_` and prove the remaining obligations.

Take `⟨y, hy, z, hz, hyz⟩` from `Subgroup.mem_sup_of_normal_right.1 hi`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← hyz]`. Simplify using `using hz`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k : ι → G, ∀ᶠ i in (U : Filter ι), k i ∈ K i ∧ (k i)⁻¹ * x ∈ O.toSubgroup := by`.

Use `⟨fun i => if hi : ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup then hi.choose else 1, ?_⟩` and prove the remaining obligations. Use `hex.mono fun i hi => ?_` and prove the remaining obligations. Simplify using `only [dif_pos hi]`. Conclude with `hi.choose_spec`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : G, Tendsto k (U : Filter ι) (nhds l) := by`.

Use `⟨(U.map k).lim, ?_⟩` and prove the remaining obligations. Establish `h'` using `(U.map k).le_nhds_lim`. Rewrite `h'` using `[Ultrafilter.coe_map]`. Conclude with `h'`. Establish `hlL : l ∈ limKer (U : Filter ι) K`.

Rewrite using `[mem_limKer]`. Introduce `O'`. Establish `hopen : IsOpen {y : G | l⁻¹ * y ∈ O'.toSubgroup}` using `O'.toOpenSubgroup.isOpen.preimage (continuous_mul_left _)`. Use `filter_upwards [hl.eventually (hopen.mem_nhds (by simp)), hk] with i h1 h2`. Establish `heq : l = k i * (l⁻¹ * k i)⁻¹` using `by group`.

Rewrite using `[heq]`. Conclude with `Subgroup.mul_mem _ (Subgroup.mem_sup_left h2.1) (Subgroup.mem_sup_right (Subgroup.inv_mem _ h1))`. Establish `hC : IsClosed {y : G | y⁻¹ * x ∈ O.toSubgroup}` using `O.toOpenSubgroup.isClosed.preimage (continuous_inv.mul continuous_const)`. Establish `hlx : l⁻¹ * x ∈ O.toSubgroup` using `hC.mem_of_tendsto hl (hk.mono fun i h => h.2)`. Establish `heq : x = l * (l⁻¹ * x)` using `by group`.

Rewrite using `[heq]`. Conclude with `Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right hlx)`. Introduce `h`. Set `S : Subgroup G` to `{ carrier := {g | ∀ᶠ i in (U : Filter ι), g ∈ K i ⊔ O.toSubgroup} mul_mem' := fun ha hb => Filter.Eventually.mono (Filter.Eventually.and ha hb) fun i hi => Subgroup.mul_mem _ hi.1 hi.2 one_mem' := Filter.Eventually.of_forall fun i => Subgroup.one_mem _ inv_mem' := fun ha => Filte …`. Establish `hle : limKer (U : Filter ι) K ⊔ O.toSubgroup ≤ S` using `sup_le (fun g hg => (mem_limKer.1 hg) O) (fun g hg => Filter.Eventually.of_forall fun i => Subgroup.mem_sup_right hg)`.

Conclude with `hle h`.
-/
private theorem limKer_key {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) (O : OpenNormalSubgroup G) (x : G) :
    (∀ᶠ i in (U : Filter ι), x ∈ K i ⊔ O.toSubgroup) ↔
      x ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup := by
  haveI := O.isNormal'
  constructor
  · intro h
    have hex : ∀ᶠ i in (U : Filter ι), ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup := by
      refine h.mono fun i hi => ?_
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hi
      refine ⟨y, hy, ?_⟩
      rw [← hyz]
      simpa using hz
    classical
    obtain ⟨k, hk⟩ : ∃ k : ι → G, ∀ᶠ i in (U : Filter ι), k i ∈ K i ∧ (k i)⁻¹ * x ∈ O.toSubgroup := by
      refine ⟨fun i => if hi : ∃ k ∈ K i, k⁻¹ * x ∈ O.toSubgroup then hi.choose else 1, ?_⟩
      refine hex.mono fun i hi => ?_
      simp only [dif_pos hi]
      exact hi.choose_spec
    obtain ⟨l, hl⟩ : ∃ l : G, Tendsto k (U : Filter ι) (nhds l) := by
      refine ⟨(U.map k).lim, ?_⟩
      have h' := (U.map k).le_nhds_lim
      rw [Ultrafilter.coe_map] at h'
      exact h'
    have hlL : l ∈ limKer (U : Filter ι) K := by
      rw [mem_limKer]
      intro O'
      have hopen : IsOpen {y : G | l⁻¹ * y ∈ O'.toSubgroup} :=
        O'.toOpenSubgroup.isOpen.preimage (continuous_mul_left _)
      filter_upwards [hl.eventually (hopen.mem_nhds (by simp)), hk] with i h1 h2
      have heq : l = k i * (l⁻¹ * k i)⁻¹ := by group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h2.1) (Subgroup.mem_sup_right (Subgroup.inv_mem _ h1))
    have hC : IsClosed {y : G | y⁻¹ * x ∈ O.toSubgroup} :=
      O.toOpenSubgroup.isClosed.preimage (continuous_inv.mul continuous_const)
    have hlx : l⁻¹ * x ∈ O.toSubgroup := hC.mem_of_tendsto hl (hk.mono fun i h => h.2)
    have heq : x = l * (l⁻¹ * x) := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL) (Subgroup.mem_sup_right hlx)
  · intro h
    let S : Subgroup G :=
      { carrier := {g | ∀ᶠ i in (U : Filter ι), g ∈ K i ⊔ O.toSubgroup}
        mul_mem' := fun ha hb =>
          Filter.Eventually.mono (Filter.Eventually.and ha hb) fun i hi => Subgroup.mul_mem _ hi.1 hi.2
        one_mem' := Filter.Eventually.of_forall fun i => Subgroup.one_mem _
        inv_mem' := fun ha => Filter.Eventually.mono ha fun i hi => Subgroup.inv_mem _ hi }
    have hle : limKer (U : Filter ι) K ⊔ O.toSubgroup ≤ S :=
      sup_le (fun g hg => (mem_limKer.1 hg) O)
        (fun g hg => Filter.Eventually.of_forall fun i => Subgroup.mem_sup_right hg)
    exact hle h

/- English proof (translation)
Introduce `G ι _ _ _ _ _ U K _`. Establish `h2 : ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup`. Introduce `O`. Take `⟨T, hT⟩` from `isCompact_univ.elim_finite_subcover (fun g : G => {y : G | g⁻¹ * y ∈ O.toSubgroup}) (fun g => O.toOpenSubgroup.isOpen.preimage (continuous_mul_left _)) (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)`. Establish `hev : ∀ᶠ i in (U : Filter ι), ∀ t ∈ T, (t ∈ K i ⊔ O.toSubgroup ↔ t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup)`.

Use `(Filter.eventually_all_finset T).2 (fun t _ => ?_)` and prove the remaining obligations. Distinguish the cases in `ht : t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup`. Conclude with `((limKer_key U K O t).2 ht).mono fun i hi => iff_of_true hi ht`. Establish `hn : ¬ ∀ᶠ i in (U : Filter ι), t ∈ K i ⊔ O.toSubgroup` using `fun h => ht ((limKer_key U K O t).1 h)`. Conclude with `(Ultrafilter.eventually_not.2 hn).mono fun i hi => iff_of_false hi ht`.

Use `filter_upwards [hev] with i hi`. Use extensionality with `g`. Choose the witnesses or unpack the hypotheses as in `⟨t, htT, hgt⟩ : ∃ t ∈ T, t⁻¹ * g ∈ O.toSubgroup := by`. Use `hT (Set.mem_univ g)` as an intermediate fact. Simplify using `only [Set.mem_iUnion] at this`.

Take `⟨t, htT, hgt⟩` from `this`. Conclude with `⟨t, htT, hgt⟩`. Establish `mem_iff : ∀ M : Subgroup G, O.toSubgroup ≤ M → (g ∈ M ↔ t ∈ M)`. Introduce `M hM`. Establish `hg : g = t * (t⁻¹ * g)` using `by group`.

Rewrite using `[hg]`. Conclude with `mul_mem_cancel_right (hM hgt)`. Rewrite using `[mem_iff _ le_sup_right, mem_iff _ le_sup_right]`. Conclude with `hi t htT`. Establish `hclosed : IsClosed (limKer (U : Filter ι) K : Set G)`.

Establish `hset : (limKer (U : Filter ι) K : Set G) = ⋂ O : OpenNormalSubgroup G, ((limKer (U : Filter ι) K ⊔ O.toSubgroup : Subgroup G) : Set G)`. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, Set.mem_iInter]`. Prove the components needed by the constructor for the conclusion. Introduce `hx O`.

Conclude with `Subgroup.mem_sup_left hx`. Introduce `hx`. Rewrite using `[mem_limKer]`. Introduce `O`. Conclude with `(limKer_key U K O x).2 (hx O)`.

Rewrite using `[hset]`. Conclude with `isClosed_iInter fun O => Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right O.toOpenSubgroup.isOpen)`. Use `⟨hclosed, h2, fun O => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Use `filter_upwards [h2 O] with i hi`. Rewrite `hi` using `[sup_eq_right.2 h]`.

Conclude with `sup_eq_right.1 hi`. Introduce `x hx`. Take `⟨i, hi1, hi2⟩` from `((mem_limKer.1 hx O).and h).exists`. Conclude with `(sup_le hi2 le_rfl) hi1`.
-/
theorem UpperTheory.V.AlgebraTools.limKer_sup :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (U : Ultrafilter ι) (K : ι → Subgroup G) [∀ i, (K i).Normal],
      IsClosed (limKer (U : Filter ι) K : Set G) ∧
      (∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι), K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup) ∧
      (∀ O : OpenNormalSubgroup G, limKer (U : Filter ι) K ≤ O.toSubgroup ↔ ∀ᶠ i in (U : Filter ι), K i ≤ O.toSubgroup) := by
  intro G ι _ _ _ _ _ U K _
  have h2 : ∀ O : OpenNormalSubgroup G, ∀ᶠ i in (U : Filter ι),
      K i ⊔ O.toSubgroup = limKer (U : Filter ι) K ⊔ O.toSubgroup := by
    intro O
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover
      (fun g : G => {y : G | g⁻¹ * y ∈ O.toSubgroup})
      (fun g => O.toOpenSubgroup.isOpen.preimage (continuous_mul_left _))
      (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
    have hev : ∀ᶠ i in (U : Filter ι), ∀ t ∈ T,
        (t ∈ K i ⊔ O.toSubgroup ↔ t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup) := by
      refine (Filter.eventually_all_finset T).2 (fun t _ => ?_)
      by_cases ht : t ∈ limKer (U : Filter ι) K ⊔ O.toSubgroup
      · exact ((limKer_key U K O t).2 ht).mono fun i hi => iff_of_true hi ht
      · have hn : ¬ ∀ᶠ i in (U : Filter ι), t ∈ K i ⊔ O.toSubgroup :=
          fun h => ht ((limKer_key U K O t).1 h)
        exact (Ultrafilter.eventually_not.2 hn).mono fun i hi => iff_of_false hi ht
    filter_upwards [hev] with i hi
    ext g
    obtain ⟨t, htT, hgt⟩ : ∃ t ∈ T, t⁻¹ * g ∈ O.toSubgroup := by
      have := hT (Set.mem_univ g)
      simp only [Set.mem_iUnion] at this
      obtain ⟨t, htT, hgt⟩ := this
      exact ⟨t, htT, hgt⟩
    have mem_iff : ∀ M : Subgroup G, O.toSubgroup ≤ M → (g ∈ M ↔ t ∈ M) := by
      intro M hM
      have hg : g = t * (t⁻¹ * g) := by group
      rw [hg]
      exact mul_mem_cancel_right (hM hgt)
    rw [mem_iff _ le_sup_right, mem_iff _ le_sup_right]
    exact hi t htT
  have hclosed : IsClosed (limKer (U : Filter ι) K : Set G) := by
    have hset : (limKer (U : Filter ι) K : Set G) =
        ⋂ O : OpenNormalSubgroup G, ((limKer (U : Filter ι) K ⊔ O.toSubgroup : Subgroup G) : Set G) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_iInter]
      constructor
      · intro hx O
        exact Subgroup.mem_sup_left hx
      · intro hx
        rw [mem_limKer]
        intro O
        exact (limKer_key U K O x).2 (hx O)
    rw [hset]
    exact isClosed_iInter fun O =>
      Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right O.toOpenSubgroup.isOpen)
  refine ⟨hclosed, h2, fun O => ⟨fun h => ?_, fun h => ?_⟩⟩
  · filter_upwards [h2 O] with i hi
    rw [sup_eq_right.2 h] at hi
    exact sup_eq_right.1 hi
  · intro x hx
    obtain ⟨i, hi1, hi2⟩ := ((mem_limKer.1 hx O).and h).exists
    exact (sup_le hi2 le_rfl) hi1
