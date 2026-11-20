import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Use `⟨fun h g => ?_, fun h x => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `h (g : G ⧸ N)`. Conclude with `⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨k, hk⟩` from `h g`.

Conclude with `⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩`.
-/
private theorem pq_iff (l : ℕ) (G : Type) [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_proLRes]`. Introduce `N hN`. Set `M : OpenNormalSubgroup G` to `{ toSubgroup := (N.toOpenSubgroup : Subgroup G).comap f isOpen' := N.toOpenSubgroup.isOpen.preimage hf isNormal' := Subgroup.Normal.comap inferInstance f }`. Establish `hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G))`. Rewrite `hN`, the goal using `[pq_iff]`.

Introduce `g`. Take `⟨k, hk⟩` from `hN (f g)`. Conclude with `⟨k, by simpa [M, map_pow] using hk⟩`. Use `hx M hM` as an intermediate fact. Simplify `this` using `[M]`.
-/
private theorem res_map (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] (f : G →* G)
    (hf : Continuous f) {x : G} (hx : x ∈ proLRes l G) : f x ∈ proLRes l G := by
  rw [mem_proLRes] at hx ⊢
  intro N hN
  let M : OpenNormalSubgroup G :=
    { toSubgroup := (N.toOpenSubgroup : Subgroup G).comap f
      isOpen' := N.toOpenSubgroup.isOpen.preimage hf
      isNormal' := Subgroup.Normal.comap inferInstance f }
  have hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G)) := by
    rw [pq_iff] at hN ⊢
    intro g
    obtain ⟨k, hk⟩ := hN (f g)
    exact ⟨k, by simpa [M, map_pow] using hk⟩
  have := hx M hM
  simpa [M] using this

/- English proof (translation)
Set `ι` to `{N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))}`. Set `t : ι → Set G` to `fun i => ((i.1.toOpenSubgroup : Subgroup G) : Set G)`. Establish `ht : ∀ i, IsClosed (t i)` using `fun i => i.1.toOpenSubgroup.isClosed`. Establish `hs : IsCompact ((K : Set G)ᶜ)` using `(hK.isClosed_compl).isCompact`. Establish `hempty : (K : Set G)ᶜ ∩ ⋂ i, t i = ∅`.

Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce `hy hall`. Apply `hy` to reduce the goal to its premises. Apply `h` to reduce the goal to its premises.

Rewrite using `[mem_proLRes]`. Introduce `N hN`. Conclude with `hall ⟨N, hN⟩`. Take `⟨u, hu⟩` from `hs.elim_finite_subfamily_closed t ht hempty`. Establish `hk : ∀ i : ι, ∃ k : ℕ, g ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G)` using `fun i => (pq_iff l G _).mp i.2 g`.

Use `choose kf hkf using hk`. Use `⟨∑ i ∈ u, kf i, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hg`. Establish `hmem : g ^ l ^ (∑ i ∈ u, kf i) ∈ (K : Set G)ᶜ ∩ ⋂ i ∈ u, t i`. Use `⟨hg, ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_iInter]`. Introduce `i hi`. Establish `hle : kf i ≤ ∑ j ∈ u, kf j` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi`. Establish `heq : l ^ (∑ j ∈ u, kf j) = l ^ kf i * l ^ (∑ j ∈ u, kf j - kf i)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hle]`.

Use `show g ^ l ^ (∑ j ∈ u, kf j) ∈ ((i.1.toOpenSubgroup : Subgroup G) : Set G)`. Rewrite using `[heq, pow_mul]`. Conclude with `Subgroup.pow_mem _ (hkf i) _`. Rewrite `hmem` using `[hu]`. Conclude with `hmem`.
-/
private theorem res_pow (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (K : Subgroup G) (hK : IsOpen (K : Set G)) (h : proLRes l G ≤ K) (g : G) :
    ∃ k : ℕ, g ^ l ^ k ∈ K := by
  classical
  let ι := {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))}
  let t : ι → Set G := fun i => ((i.1.toOpenSubgroup : Subgroup G) : Set G)
  have ht : ∀ i, IsClosed (t i) := fun i => i.1.toOpenSubgroup.isClosed
  have hs : IsCompact ((K : Set G)ᶜ) := (hK.isClosed_compl).isCompact
  have hempty : (K : Set G)ᶜ ∩ ⋂ i, t i = ∅ := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro hy hall
    apply hy
    apply h
    rw [mem_proLRes]
    intro N hN
    exact hall ⟨N, hN⟩
  obtain ⟨u, hu⟩ := hs.elim_finite_subfamily_closed t ht hempty
  have hk : ∀ i : ι, ∃ k : ℕ, g ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G) := fun i =>
    (pq_iff l G _).mp i.2 g
  choose kf hkf using hk
  refine ⟨∑ i ∈ u, kf i, ?_⟩
  by_contra hg
  have hmem : g ^ l ^ (∑ i ∈ u, kf i) ∈ (K : Set G)ᶜ ∩ ⋂ i ∈ u, t i := by
    refine ⟨hg, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    have hle : kf i ≤ ∑ j ∈ u, kf j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
    have heq : l ^ (∑ j ∈ u, kf j) = l ^ kf i * l ^ (∑ j ∈ u, kf j - kf i) := by
      rw [← pow_add, Nat.add_sub_cancel' hle]
    show g ^ l ^ (∑ j ∈ u, kf j) ∈ ((i.1.toOpenSubgroup : Subgroup G) : Set G)
    rw [heq, pow_mul]
    exact Subgroup.pow_mem _ (hkf i) _
  rw [hu] at hmem
  exact hmem

/- English proof (translation)
Introduce `l _ G _ _ _ _ _ H _ hH`. Use `haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `x hx g`.

Take `⟨y, hy, rfl⟩` from `Subgroup.mem_map.mp hx`. Set `c : H →* H` to `(MulAut.conjNormal g).toMonoidHom`. Establish `hc : Continuous c`. Apply `Continuous.subtype_mk` to reduce the goal to its premises. Conclude with `(continuous_const.mul continuous_subtype_val).mul continuous_const`.

Use `res_map l H c hc hy` as an intermediate fact. Use `Subgroup.mem_map.mpr ⟨c y, this, ?_⟩` and prove the remaining obligations. Simplify using `[c, MulAut.conjNormal_apply]`. Unfold `proLResOf`. Rewrite using `[Subgroup.coe_map, Subgroup.coe_subtype]`.

Conclude with `hH.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_proLRes l H)`. Conclude with `Subgroup.map_subtype_le _`. Introduce `O hO h hh`. Establish `hle : proLRes l H ≤ (O.toOpenSubgroup : Subgroup G).comap H.subtype` using `Subgroup.map_le_iff_le_comap.mp hO`. Establish `hopen : IsOpen (((O.toOpenSubgroup : Subgroup G).comap H.subtype : Subgroup H) : Set H)` using `O.toOpenSubgroup.isOpen.preimage continuous_subtype_val`.

Take `⟨k, hk⟩` from `res_pow l H _ hopen hle ⟨h, hh⟩`. Conclude with `⟨k, hk⟩`.
-/
theorem UpperTheory.V.AlgebraTools.proLResOf_normal :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (H : Subgroup G) [H.Normal], IsClosed (H : Set G) →
      (proLResOf l H).Normal ∧ IsClosed (proLResOf l H : Set G) ∧ proLResOf l H ≤ H ∧
      ∀ (O : OpenNormalSubgroup G), proLResOf l H ≤ O.toSubgroup → ∀ h ∈ H, ∃ k : ℕ, h ^ l ^ k ∈ O.toSubgroup := by
  intro l _ G _ _ _ _ _ H _ hH
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    intro x hx g
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let c : H →* H := (MulAut.conjNormal g).toMonoidHom
    have hc : Continuous c := by
      apply Continuous.subtype_mk
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    have := res_map l H c hc hy
    refine Subgroup.mem_map.mpr ⟨c y, this, ?_⟩
    simp [c, MulAut.conjNormal_apply]
  · unfold proLResOf
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hH.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_proLRes l H)
  · exact Subgroup.map_subtype_le _
  · intro O hO h hh
    have hle : proLRes l H ≤ (O.toOpenSubgroup : Subgroup G).comap H.subtype :=
      Subgroup.map_le_iff_le_comap.mp hO
    have hopen : IsOpen (((O.toOpenSubgroup : Subgroup G).comap H.subtype : Subgroup H) : Set H) :=
      O.toOpenSubgroup.isOpen.preimage continuous_subtype_val
    obtain ⟨k, hk⟩ := res_pow l H _ hopen hle ⟨h, hh⟩
    exact ⟨k, hk⟩
