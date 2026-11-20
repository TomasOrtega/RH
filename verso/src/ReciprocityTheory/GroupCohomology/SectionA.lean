import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import Mathlib.Topology.Algebra.ClopenNhdofOne

open Pointwise Set

namespace ReciprocityTheory.Coh.ContinuousSections

variable {G : Type*} [Group G]

def rel (K N : Subgroup G) [hN : N.Normal] : Setoid G where
  r x y := ∃ k ∈ K, ∃ n ∈ N, y = k * n * x
  iseqv := {
    refl := fun x => ⟨1, K.one_mem, 1, N.one_mem, by simp⟩
    symm := by
      rintro x y ⟨k, hk, n, hn, rfl⟩
      refine ⟨k⁻¹, K.inv_mem hk, k * n⁻¹ * k⁻¹, hN.conj_mem _ (N.inv_mem hn) k, by group⟩
    trans := by
      rintro x y z ⟨k, hk, n, hn, rfl⟩ ⟨k', hk', n', hn', rfl⟩
      refine ⟨k' * k, K.mul_mem hk' hk, k⁻¹ * n' * k * n, N.mul_mem ?_ hn, by group⟩
      simpa using hN.conj_mem n' hn' k⁻¹ }

noncomputable def rep (K N : Subgroup G) [N.Normal] (x : G) : G :=
  (Quotient.mk (rel K N) x).out

/- English proof (translation)
Unfold `rep`. Rewrite using `[Quotient.sound (s := rel K N) h]`.
-/
lemma rep_eq (K N : Subgroup G) [N.Normal] {x y : G} (h : (rel K N) x y) : rep K N x = rep K N y := by
  unfold rep
  rw [Quotient.sound (s := rel K N) h]

/- English proof (translation)
Conclude with `Quotient.mk_out (s := rel K N) x`.
-/
lemma rep_spec (K N : Subgroup G) [N.Normal] (x : G) : ∃ k ∈ K, ∃ n ∈ N, x = k * n * rep K N x := by
  exact Quotient.mk_out (s := rel K N) x

def tr (K N : Subgroup G) [N.Normal] : Set G := {y | y * (rep K N y)⁻¹ ∈ N}

/- English proof (translation)
Establish `hr : rep K N z = rep K N y` using `(rep_eq K N ⟨1, K.one_mem, z * y⁻¹, h, by group⟩).symm`. Use `show z * (rep K N z)⁻¹ ∈ N ↔ y * (rep K N y)⁻¹ ∈ N`. Rewrite using `[hr, show z * (rep K N y)⁻¹ = z * y⁻¹ * (y * (rep K N y)⁻¹) by group]`. Conclude with `N.mul_mem_cancel_left h`.
-/
lemma tr_coset (K N : Subgroup G) [N.Normal] {y z : G} (h : z * y⁻¹ ∈ N) :
    z ∈ tr K N ↔ y ∈ tr K N := by
  have hr : rep K N z = rep K N y :=
    (rep_eq K N ⟨1, K.one_mem, z * y⁻¹, h, by group⟩).symm
  show z * (rep K N z)⁻¹ ∈ N ↔ y * (rep K N y)⁻¹ ∈ N
  rw [hr, show z * (rep K N y)⁻¹ = z * y⁻¹ * (y * (rep K N y)⁻¹) by group]
  exact N.mul_mem_cancel_left h

variable [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `y hy`. Use `⟨(fun z => z * y⁻¹) ⁻¹' (N : Set G), fun z hz hzt => hy ((tr_coset K N hz).1 hzt), hN.preimage (continuous_id.mul continuous_const), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
lemma tr_closed (K N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G)) : IsClosed (tr K N) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  refine ⟨(fun z => z * y⁻¹) ⁻¹' (N : Set G), fun z hz hzt => hy ((tr_coset K N hz).1 hzt),
    hN.preimage (continuous_id.mul continuous_const), ?_⟩
  simp

def admitted (U : Subgroup G) (p : Subgroup G × Set G) : Prop :=
  p.1 ≤ U ∧ IsClosed p.2 ∧ (∀ k ∈ p.1, ∀ s ∈ p.2, k * s ∈ p.2) ∧
  (∀ a ∈ p.2, ∀ b ∈ p.2, a * b⁻¹ ∈ U → a * b⁻¹ ∈ p.1) ∧ ∀ g, ∃ a ∈ p.2, a * g⁻¹ ∈ U

/- English proof (translation)
Take `⟨hKU, hSc, hKS, hSK, hSU⟩` from `h`. Use `⟨inf_le_left.trans hKU, hSc.inter (tr_closed K N hN), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `k ⟨hkK, hkN⟩ s ⟨hsS, hsT⟩`. Use `⟨hKS k hkK s hsS, (tr_coset K N ?_).2 hsT⟩` and prove the remaining obligations. Simplify using `using hkN`.

Introduce and unpack `a ⟨haS, haT⟩ b ⟨hbS, hbT⟩ hab`. Establish `habK` using `hSK a haS b hbS hab`. Use `⟨habK, ?_⟩` and prove the remaining obligations. Establish `hr : rep K N b = rep K N a` using `rep_eq K N ⟨a * b⁻¹, habK, 1, N.one_mem, by group⟩`. Establish `ha : a * (rep K N a)⁻¹ ∈ N` using `haT`.

Establish `hb : b * (rep K N b)⁻¹ ∈ N` using `hbT`. Rewrite `hb` using `[hr]`. Use `N.mul_mem ha (N.inv_mem hb)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Introduce `g`.

Take `⟨a, haS, hag⟩` from `hSU g`. Take `⟨k, hk, n, hn, ha⟩` from `rep_spec K N a`. Use `set r := rep K N a with hrdef`. Establish `hrel : rep K N (k⁻¹ * a) = r` using `(rep_eq K N ⟨k⁻¹, K.inv_mem hk, 1, N.one_mem, by group⟩).symm`. Use `⟨k⁻¹ * a, ⟨hKS _ (K.inv_mem hk) a haS, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `show k⁻¹ * a * (rep K N (k⁻¹ * a))⁻¹ ∈ N`. Rewrite using `[hrel, ha]`. Simplify `hn` using `[mul_assoc]`. Rewrite using `[mul_assoc]`. Conclude with `U.mul_mem (U.inv_mem (hKU hk)) hag`.
-/
lemma adm_of_section_mem (U K : Subgroup G) (S : Set G) (h : admitted U (K, S)) (N : Subgroup G) [N.Normal]
    (hN : IsOpen (N : Set G)) : admitted U (K ⊓ N, S ∩ tr K N) := by
  obtain ⟨hKU, hSc, hKS, hSK, hSU⟩ := h
  refine ⟨inf_le_left.trans hKU, hSc.inter (tr_closed K N hN), ?_, ?_, ?_⟩
  · rintro k ⟨hkK, hkN⟩ s ⟨hsS, hsT⟩
    refine ⟨hKS k hkK s hsS, (tr_coset K N ?_).2 hsT⟩
    simpa using hkN
  · rintro a ⟨haS, haT⟩ b ⟨hbS, hbT⟩ hab
    have habK := hSK a haS b hbS hab
    refine ⟨habK, ?_⟩
    have hr : rep K N b = rep K N a := rep_eq K N ⟨a * b⁻¹, habK, 1, N.one_mem, by group⟩
    have ha : a * (rep K N a)⁻¹ ∈ N := haT
    have hb : b * (rep K N b)⁻¹ ∈ N := hbT
    rw [hr] at hb
    have := N.mul_mem ha (N.inv_mem hb)
    simpa [mul_assoc] using this
  · intro g
    obtain ⟨a, haS, hag⟩ := hSU g
    obtain ⟨k, hk, n, hn, ha⟩ := rep_spec K N a
    set r := rep K N a with hrdef
    have hrel : rep K N (k⁻¹ * a) = r := (rep_eq K N ⟨k⁻¹, K.inv_mem hk, 1, N.one_mem, by group⟩).symm
    refine ⟨k⁻¹ * a, ⟨hKS _ (K.inv_mem hk) a haS, ?_⟩, ?_⟩
    · show k⁻¹ * a * (rep K N (k⁻¹ * a))⁻¹ ∈ N
      rw [hrel, ha]
      simpa [mul_assoc] using hn
    · rw [mul_assoc]
      exact U.mul_mem (U.inv_mem (hKU hk)) hag

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Use `⟨(iInf₂_le y hy).trans (hc y hy).1, isClosed_biInter fun p hp => (hc p hp).2.1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk s hs`. Simplify using `only [Subgroup.mem_iInf] at hk`. Simplify using `only [Set.mem_iInter] at hs ⊢`. Conclude with `fun p hp => (hc p hp).2.2.1 k (hk p hp) s (hs p hp)`.

Introduce `a ha b hb hab`. Simplify using `only [Set.mem_iInter] at ha hb`. Simplify using `only [Subgroup.mem_iInf]`. Conclude with `fun p hp => (hc p hp).2.2.2.1 a (ha p hp) b (hb p hp) hab`. Introduce `g`.

Establish `: Nonempty c` using `⟨⟨y, hy⟩⟩`. Establish `hne` using `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed (fun p : c => p.1.2 ∩ {a | a * g⁻¹ ∈ U}) ?_ ?_ (fun p => ((hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul continuous_const))).isCompact) (fun p => (hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul conti …`. Take `⟨a, ha⟩` from `hne`. Simplify using `only [Set.mem_iInter] at ha`. Use `⟨a, ?_, (ha ⟨y, hy⟩).2⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_iInter]`. Conclude with `fun p hp => (ha ⟨p, hp⟩).1`. Introduce `p q`. Break down `htot p.1 p.2 q.1 q.2 with hpq | hqp` into its components or cases. Conclude with `⟨p, le_rfl, Set.inter_subset_inter_left _ (Prod.le_def.1 hpq).2⟩`.

Conclude with `⟨q, Set.inter_subset_inter_left _ (Prod.le_def.1 hqp).2, le_rfl⟩`. Introduce `p`. Take `⟨a, haS, hag⟩` from `(hc p.1 p.2).2.2.2.2 g`. Conclude with `⟨a, haS, hag⟩`.
-/
lemma admissible_chain_inf [CompactSpace G] (U : Subgroup G) (hU : IsClosed (U : Set G))
    (c : Set (Subgroup G × Set G)) (hc : ∀ p ∈ c, admitted U p)
    (htot : ∀ p ∈ c, ∀ q ∈ c, p ≤ q ∨ q ≤ p) (y : Subgroup G × Set G) (hy : y ∈ c) :
    admitted U (⨅ p ∈ c, p.1, ⋂ p ∈ c, p.2) := by
  refine ⟨(iInf₂_le y hy).trans (hc y hy).1, isClosed_biInter fun p hp => (hc p hp).2.1, ?_, ?_, ?_⟩
  · intro k hk s hs
    simp only [Subgroup.mem_iInf] at hk
    simp only [Set.mem_iInter] at hs ⊢
    exact fun p hp => (hc p hp).2.2.1 k (hk p hp) s (hs p hp)
  · intro a ha b hb hab
    simp only [Set.mem_iInter] at ha hb
    simp only [Subgroup.mem_iInf]
    exact fun p hp => (hc p hp).2.2.2.1 a (ha p hp) b (hb p hp) hab
  · intro g
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    have hne := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun p : c => p.1.2 ∩ {a | a * g⁻¹ ∈ U}) ?_ ?_
      (fun p => ((hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul continuous_const))).isCompact)
      (fun p => (hc p.1 p.2).2.1.inter (hU.preimage (continuous_id.mul continuous_const)))
    · obtain ⟨a, ha⟩ := hne
      simp only [Set.mem_iInter] at ha
      refine ⟨a, ?_, (ha ⟨y, hy⟩).2⟩
      simp only [Set.mem_iInter]
      exact fun p hp => (ha ⟨p, hp⟩).1
    · intro p q
      rcases htot p.1 p.2 q.1 q.2 with hpq | hqp
      · exact ⟨p, le_rfl, Set.inter_subset_inter_left _ (Prod.le_def.1 hpq).2⟩
      · exact ⟨q, Set.inter_subset_inter_left _ (Prod.le_def.1 hqp).2, le_rfl⟩
    · intro p
      obtain ⟨a, haS, hag⟩ := (hc p.1 p.2).2.2.2.2 g
      exact ⟨a, haS, hag⟩

/- English proof (translation)
Establish `hchain : ∀ c ⊆ {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)}, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)}, ∀ z ∈ c, z ≤ ub`. Introduce `c hcs hc y hy`. Use `⟨OrderDual.toDual (⨅ p ∈ OrderDual.toDual ⁻¹' c, p.1, ⋂ p ∈ OrderDual.toDual ⁻¹' c, p.2), admissible_chain_inf U hU _ (fun p hp => hcs hp) ?_ (OrderDual.ofDual y) hy, ?_⟩` and prove the remaining obligations. Introduce `p hp q hq`. Distinguish the cases in `hpq : p = q`.

Conclude with `Or.inl (le_of_eq hpq)`. Break down `hc hp hq (fun h => hpq (OrderDual.toDual.injective h)) with h | h` into its components or cases. Conclude with `Or.inr h`. Conclude with `Or.inl h`. Introduce `z hz`.

Conclude with `Prod.le_def.2 ⟨iInf₂_le (OrderDual.ofDual z) hz, Set.iInter₂_subset (OrderDual.ofDual z) hz⟩`. Establish `hstart : OrderDual.toDual ((U, Set.univ) : Subgroup G × Set G) ∈ {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)}` using `⟨le_rfl, isClosed_univ, fun _ _ _ _ => Set.mem_univ _, fun _ _ _ _ h => h, fun g => ⟨g, Set.mem_univ _, by simp⟩⟩`. Take `⟨m, -, hm⟩` from `zorn_le_nonempty₀ _ hchain _ hstart`. Establish `hA : admitted U (OrderDual.ofDual m)` using `hm.1`. Use `set K := (OrderDual.ofDual m).1 with hKdef`.

Use `set S := (OrderDual.ofDual m).2 with hSdef`. Establish `hK1 : ∀ k ∈ K, k = 1`. Introduce `k hk`. Assume the negation of the conclusion as `hne`. Take `⟨N, hN⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_compl_singleton : IsOpen ({k}ᶜ : Set G)) (Set.mem_compl_singleton_iff.2 (Ne.symm hne))`.

Establish `hstep` using `adm_of_section_mem U K S hA N.toSubgroup N.isOpen'`. Establish `hle` using `hm.2 (y := OrderDual.toDual (K ⊓ N.toSubgroup, S ∩ tr K N.toSubgroup)) hstep (Prod.le_def.2 ⟨inf_le_left, Set.inter_subset_left⟩)`. Establish `hkN : k ∈ N.toSubgroup` using `((Prod.le_def.1 hle).1 hk).2`. Conclude with `hN hkN rfl`. Establish `hex : ∀ g, ∃ a ∈ S, a * g⁻¹ ∈ U` using `hA.2.2.2.2`.

Establish `huniq : ∀ g a a', a ∈ S → a' ∈ S → a * g⁻¹ ∈ U → a' * g⁻¹ ∈ U → a = a'`. Introduce `g a a' ha ha' hag ha'g`. Establish `hU' : a * a'⁻¹ ∈ U`. Use `U.mul_mem hag (U.inv_mem ha'g)` as an intermediate fact. Simplify `this` using `[mul_assoc]`.

Conclude with `mul_inv_eq_one.1 (hK1 _ (hA.2.2.2.1 a ha a' ha' hU'))`. Use `choose t htS htU using hex`. Use `⟨t, ?_, htU, fun g h hgh => ?_⟩` and prove the remaining obligations. Rewrite using `[continuous_iff_isClosed]`. Introduce `C hC`.

Establish `hset : t ⁻¹' C = (U : Set G) * (S ∩ C)`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Use `Set.mem_mul.2 ⟨g * (t g)⁻¹, ?_, t g, ⟨htS g, hg⟩, by group⟩` and prove the remaining obligations.

Simplify using `using U.inv_mem (htU g)`. Introduce and unpack `⟨u, hu, a, ⟨haS, haC⟩, rfl⟩ show t (u * a) ∈ C`. Rewrite using `[huniq (u * a) (t (u * a)) a (htS _) haS (htU _) (by simpa using U.inv_mem hu)]`. Conclude with `haC`. Rewrite using `[hset]`.

Conclude with `(hU.isCompact.mul (hA.2.1.inter hC).isCompact).isClosed`. Use `huniq g (t g) (t h) (htS g) (htS h) (htU g) ?_` and prove the remaining obligations. Establish `: t h * g⁻¹ = (t h * h⁻¹) * (g * h⁻¹)⁻¹` using `by group`. Rewrite using `[this]`. Conclude with `U.mul_mem (htU h) (U.inv_mem hgh)`.
-/
theorem core [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (U : Subgroup G)
    (hU : IsClosed (U : Set G)) : ∃ t : G → G, Continuous t ∧ (∀ g, t g * g⁻¹ ∈ U) ∧
      ∀ g h, g * h⁻¹ ∈ U → t g = t h := by
  classical
  have hchain : ∀ c ⊆ {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)},
      IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)},
        ∀ z ∈ c, z ≤ ub := by
    intro c hcs hc y hy
    refine ⟨OrderDual.toDual (⨅ p ∈ OrderDual.toDual ⁻¹' c, p.1, ⋂ p ∈ OrderDual.toDual ⁻¹' c, p.2),
      admissible_chain_inf U hU _ (fun p hp => hcs hp) ?_ (OrderDual.ofDual y) hy, ?_⟩
    · intro p hp q hq
      by_cases hpq : p = q
      · exact Or.inl (le_of_eq hpq)
      · rcases hc hp hq (fun h => hpq (OrderDual.toDual.injective h)) with h | h
        · exact Or.inr h
        · exact Or.inl h
    · intro z hz
      exact Prod.le_def.2 ⟨iInf₂_le (OrderDual.ofDual z) hz,
        Set.iInter₂_subset (OrderDual.ofDual z) hz⟩
  have hstart : OrderDual.toDual ((U, Set.univ) : Subgroup G × Set G) ∈
      {p : (Subgroup G × Set G)ᵒᵈ | admitted U (OrderDual.ofDual p)} :=
    ⟨le_rfl, isClosed_univ, fun _ _ _ _ => Set.mem_univ _, fun _ _ _ _ h => h,
      fun g => ⟨g, Set.mem_univ _, by simp⟩⟩
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ _ hchain _ hstart
  have hA : admitted U (OrderDual.ofDual m) := hm.1
  set K := (OrderDual.ofDual m).1 with hKdef
  set S := (OrderDual.ofDual m).2 with hSdef
  have hK1 : ∀ k ∈ K, k = 1 := by
    intro k hk
    by_contra hne
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (isOpen_compl_singleton : IsOpen ({k}ᶜ : Set G)) (Set.mem_compl_singleton_iff.2 (Ne.symm hne))
    have hstep := adm_of_section_mem U K S hA N.toSubgroup N.isOpen'
    have hle := hm.2 (y := OrderDual.toDual (K ⊓ N.toSubgroup, S ∩ tr K N.toSubgroup)) hstep
      (Prod.le_def.2 ⟨inf_le_left, Set.inter_subset_left⟩)
    have hkN : k ∈ N.toSubgroup := ((Prod.le_def.1 hle).1 hk).2
    exact hN hkN rfl
  have hex : ∀ g, ∃ a ∈ S, a * g⁻¹ ∈ U := hA.2.2.2.2
  have huniq : ∀ g a a', a ∈ S → a' ∈ S → a * g⁻¹ ∈ U → a' * g⁻¹ ∈ U → a = a' := by
    intro g a a' ha ha' hag ha'g
    have hU' : a * a'⁻¹ ∈ U := by
      have := U.mul_mem hag (U.inv_mem ha'g)
      simpa [mul_assoc] using this
    exact mul_inv_eq_one.1 (hK1 _ (hA.2.2.2.1 a ha a' ha' hU'))
  choose t htS htU using hex
  refine ⟨t, ?_, htU, fun g h hgh => ?_⟩
  · rw [continuous_iff_isClosed]
    intro C hC
    have hset : t ⁻¹' C = (U : Set G) * (S ∩ C) := by
      ext g
      constructor
      · intro hg
        refine Set.mem_mul.2 ⟨g * (t g)⁻¹, ?_, t g, ⟨htS g, hg⟩, by group⟩
        simpa using U.inv_mem (htU g)
      · rintro ⟨u, hu, a, ⟨haS, haC⟩, rfl⟩
        show t (u * a) ∈ C
        rw [huniq (u * a) (t (u * a)) a (htS _) haS (htU _) (by simpa using U.inv_mem hu)]
        exact haC
    rw [hset]
    exact (hU.isCompact.mul (hA.2.1.inter hC).isCompact).isClosed
  · refine huniq g (t g) (t h) (htS g) (htS h) (htU g) ?_
    have : t h * g⁻¹ = (t h * h⁻¹) * (g * h⁻¹)⁻¹ := by group
    rw [this]
    exact U.mul_mem (htU h) (U.inv_mem hgh)

end ReciprocityTheory.Coh.ContinuousSections
