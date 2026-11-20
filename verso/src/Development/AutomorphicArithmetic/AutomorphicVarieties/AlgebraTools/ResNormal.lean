import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
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
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
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
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
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
