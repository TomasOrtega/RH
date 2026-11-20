import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

/- English proof (translation)
Use `⟨fun h g => ?_, fun h x => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `h (g : G ⧸ N)`. Conclude with `⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`. Take `⟨k, hk⟩` from `h g`.

Conclude with `⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩`.
-/
private theorem pq_iff {l : ℕ} {G : Type} [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

/- English proof (translation)
Introduce `l _ G H _ _ _ _ _ _ _ _ _ _ f hf hs`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Subgroup.map_le_iff_le_comap]`. Introduce `g hg`. Rewrite using `[Subgroup.mem_comap, mem_proLRes]`.

Introduce `N hN`. Rewrite `hN` using `[pq_iff]`. Set `M : OpenNormalSubgroup G` to `{ toOpenSubgroup := OpenSubgroup.comap f hf N.toOpenSubgroup isNormal' := Subgroup.Normal.comap inferInstance f }`. Use `haveI : (M.toOpenSubgroup : Subgroup G).Normal := M.isNormal'`. Establish `hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G))`.

Rewrite using `[pq_iff]`. Introduce `x`. Take `⟨k, hk⟩` from `hN (f x)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `show x ^ l ^ k ∈ OpenSubgroup.comap f hf N.toOpenSubgroup`.

Rewrite using `[OpenSubgroup.mem_comap, map_pow]`. Conclude with `hk`. Use `(mem_proLRes.mp hg) M hM` as an intermediate fact. Conclude with `(OpenSubgroup.mem_comap (hf := hf)).mp this`. Introduce `h hh`.

Rewrite `hh` using `[mem_proLRes]`. Set `t : {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} → Set G` to `fun N => f ⁻¹' {h} ∩ (N.1.toOpenSubgroup : Set G)`. Set `T0 : OpenNormalSubgroup G` to `{ toOpenSubgroup := ⊤, isNormal' := by simpa using Subgroup.normal_top }`. Use `haveI : (T0.toOpenSubgroup : Subgroup G).Normal := T0.isNormal'`. Establish `htop : IsPGroup l (G ⧸ (T0.toOpenSubgroup : Subgroup G))`.

Rewrite using `[pq_iff]`. Introduce `g`. Use `⟨0, ?_⟩` and prove the remaining obligations. Use `show g ^ l ^ 0 ∈ (⊤ : OpenSubgroup G)`. Simplify using the standard rewrite rules.

Use `haveI : Nonempty {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} := ⟨⟨_, htop⟩⟩`. Establish `hcl : ∀ i, IsClosed (t i)` using `fun i => (isClosed_singleton.preimage hf).inter i.1.toOpenSubgroup.isClosed`. Establish `hdir : Directed (fun x1 x2 => x1 ⊇ x2) t`. Introduce `i j`. Establish `hK : IsPGroup l (G ⧸ ((i.1 ⊓ j.1).toOpenSubgroup : Subgroup G))`.

Rewrite using `[pq_iff]`. Introduce `g`. Take `⟨a, ha⟩` from `(pq_iff _).mp i.2 g`. Take `⟨b, hb⟩` from `(pq_iff _).mp j.2 g`. Use `⟨a + b, ?_⟩` and prove the remaining obligations.

Establish `e1 : g ^ l ^ (a + b) = (g ^ l ^ a) ^ l ^ b` using `by rw [pow_add, pow_mul]`. Establish `e2 : g ^ l ^ (a + b) = (g ^ l ^ b) ^ l ^ a` using `by rw [add_comm, pow_add, pow_mul]`. Establish `m1 : g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup : Subgroup G)` using `e1 ▸ pow_mem ha _`. Establish `m2 : g ^ l ^ (a + b) ∈ (j.1.toOpenSubgroup : Subgroup G)` using `e2 ▸ pow_mem hb _`. Use `show g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G)`.

Conclude with `OpenSubgroup.mem_inf.mpr ⟨m1, m2⟩`. Use `⟨⟨i.1 ⊓ j.1, hK⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G)` using `hx.2`. Conclude with `⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).1⟩`.

Introduce `x hx`. Establish `hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G)` using `hx.2`. Conclude with `⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).2⟩`. Establish `hnon : ∀ i, (t i).Nonempty`. Introduce `i`.

Establish `hNcl : IsClosed ((i.1.toOpenSubgroup : Subgroup G) : Set G)` using `i.1.toOpenSubgroup.isClosed`. Establish `hMcl : IsClosed (((i.1.toOpenSubgroup : Subgroup G).map f : Subgroup H) : Set H)`. Rewrite using `[Subgroup.coe_map]`. Conclude with `hf.isClosedMap _ hNcl`. Use `haveI : (i.1.toOpenSubgroup : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`.

Use `haveI : ((i.1.toOpenSubgroup : Subgroup G).map f).FiniteIndex := by`. Rewrite using `[Subgroup.finiteIndex_iff]`. Introduce `h0`. Establish `hd` using `Subgroup.index_map_dvd (i.1.toOpenSubgroup : Subgroup G) hs`. Rewrite `hd` using `[h0, zero_dvd_iff]`.

Conclude with `(Subgroup.finiteIndex_iff.mp inferInstance) hd`. Set `M : OpenNormalSubgroup H` to `{ toOpenSubgroup := ⟨(i.1.toOpenSubgroup : Subgroup G).map f, Subgroup.isOpen_of_isClosed_of_finiteIndex _ hMcl⟩ isNormal' := Subgroup.Normal.map inferInstance f hs }`. Use `haveI : (M.toOpenSubgroup : Subgroup H).Normal := M.isNormal'`. Establish `hM : IsPGroup l (H ⧸ (M.toOpenSubgroup : Subgroup H))`. Rewrite using `[pq_iff]`.

Introduce `y`. Take `⟨x, rfl⟩` from `hs y`. Take `⟨k, hk⟩` from `(pq_iff _).mp i.2 x`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `show f x ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G).map f`.

Conclude with `⟨x ^ l ^ k, hk, map_pow f x _⟩`. Take `⟨x, hx, hfx⟩` from `Subgroup.mem_map.mp (hh M hM)`. Conclude with `⟨x, hfx, hx⟩`. Take `⟨g, hg⟩` from `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hnon (fun i => (hcl i).isCompact) hcl`. Rewrite `hg` using `[Set.mem_iInter]`.

Use `⟨g, ?_, (hg (Classical.arbitrary _)).1⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, mem_proLRes]`. Introduce `N hN`. Conclude with `(hg ⟨N, hN⟩).2`.
-/
theorem UpperTheory.V.AlgebraTools.proLRes_map :
    ∀ (l : ℕ) [Fact l.Prime] (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H] (f : G →* H), Continuous f → Function.Surjective f →
      (proLRes l G).map f = proLRes l H := by
  intro l _ G H _ _ _ _ _ _ _ _ _ _ f hf hs
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro g hg
    rw [Subgroup.mem_comap, mem_proLRes]
    intro N hN
    rw [pq_iff] at hN
    let M : OpenNormalSubgroup G :=
      { toOpenSubgroup := OpenSubgroup.comap f hf N.toOpenSubgroup
        isNormal' := Subgroup.Normal.comap inferInstance f }
    haveI : (M.toOpenSubgroup : Subgroup G).Normal := M.isNormal'
    have hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G)) := by
      rw [pq_iff]
      intro x
      obtain ⟨k, hk⟩ := hN (f x)
      refine ⟨k, ?_⟩
      show x ^ l ^ k ∈ OpenSubgroup.comap f hf N.toOpenSubgroup
      rw [OpenSubgroup.mem_comap, map_pow]
      exact hk
    have := (mem_proLRes.mp hg) M hM
    exact (OpenSubgroup.mem_comap (hf := hf)).mp this
  · intro h hh
    rw [mem_proLRes] at hh
    let t : {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} → Set G :=
      fun N => f ⁻¹' {h} ∩ (N.1.toOpenSubgroup : Set G)
    let T0 : OpenNormalSubgroup G := { toOpenSubgroup := ⊤, isNormal' := by simpa using Subgroup.normal_top }
    haveI : (T0.toOpenSubgroup : Subgroup G).Normal := T0.isNormal'
    have htop : IsPGroup l (G ⧸ (T0.toOpenSubgroup : Subgroup G)) := by
      rw [pq_iff]
      intro g
      refine ⟨0, ?_⟩
      show g ^ l ^ 0 ∈ (⊤ : OpenSubgroup G)
      simp
    haveI : Nonempty {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))} := ⟨⟨_, htop⟩⟩
    have hcl : ∀ i, IsClosed (t i) := fun i =>
      (isClosed_singleton.preimage hf).inter i.1.toOpenSubgroup.isClosed
    have hdir : Directed (fun x1 x2 => x1 ⊇ x2) t := by
      intro i j
      have hK : IsPGroup l (G ⧸ ((i.1 ⊓ j.1).toOpenSubgroup : Subgroup G)) := by
        rw [pq_iff]
        intro g
        obtain ⟨a, ha⟩ := (pq_iff _).mp i.2 g
        obtain ⟨b, hb⟩ := (pq_iff _).mp j.2 g
        refine ⟨a + b, ?_⟩
        have e1 : g ^ l ^ (a + b) = (g ^ l ^ a) ^ l ^ b := by rw [pow_add, pow_mul]
        have e2 : g ^ l ^ (a + b) = (g ^ l ^ b) ^ l ^ a := by rw [add_comm, pow_add, pow_mul]
        have m1 : g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup : Subgroup G) := e1 ▸ pow_mem ha _
        have m2 : g ^ l ^ (a + b) ∈ (j.1.toOpenSubgroup : Subgroup G) := e2 ▸ pow_mem hb _
        show g ^ l ^ (a + b) ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G)
        exact OpenSubgroup.mem_inf.mpr ⟨m1, m2⟩
      refine ⟨⟨i.1 ⊓ j.1, hK⟩, ?_, ?_⟩
      · intro x hx
        have hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G) := hx.2
        exact ⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).1⟩
      · intro x hx
        have hx2 : x ∈ (i.1.toOpenSubgroup ⊓ j.1.toOpenSubgroup : OpenSubgroup G) := hx.2
        exact ⟨hx.1, (OpenSubgroup.mem_inf.mp hx2).2⟩
    have hnon : ∀ i, (t i).Nonempty := by
      intro i
      have hNcl : IsClosed ((i.1.toOpenSubgroup : Subgroup G) : Set G) := i.1.toOpenSubgroup.isClosed
      have hMcl : IsClosed (((i.1.toOpenSubgroup : Subgroup G).map f : Subgroup H) : Set H) := by
        rw [Subgroup.coe_map]
        exact hf.isClosedMap _ hNcl
      haveI : (i.1.toOpenSubgroup : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
      haveI : ((i.1.toOpenSubgroup : Subgroup G).map f).FiniteIndex := by
        rw [Subgroup.finiteIndex_iff]
        intro h0
        have hd := Subgroup.index_map_dvd (i.1.toOpenSubgroup : Subgroup G) hs
        rw [h0, zero_dvd_iff] at hd
        exact (Subgroup.finiteIndex_iff.mp inferInstance) hd
      let M : OpenNormalSubgroup H :=
        { toOpenSubgroup := ⟨(i.1.toOpenSubgroup : Subgroup G).map f,
            Subgroup.isOpen_of_isClosed_of_finiteIndex _ hMcl⟩
          isNormal' := Subgroup.Normal.map inferInstance f hs }
      haveI : (M.toOpenSubgroup : Subgroup H).Normal := M.isNormal'
      have hM : IsPGroup l (H ⧸ (M.toOpenSubgroup : Subgroup H)) := by
        rw [pq_iff]
        intro y
        obtain ⟨x, rfl⟩ := hs y
        obtain ⟨k, hk⟩ := (pq_iff _).mp i.2 x
        refine ⟨k, ?_⟩
        show f x ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G).map f
        exact ⟨x ^ l ^ k, hk, map_pow f x _⟩
      obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp (hh M hM)
      exact ⟨x, hfx, hx⟩
    obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t hdir hnon
      (fun i => (hcl i).isCompact) hcl
    rw [Set.mem_iInter] at hg
    refine ⟨g, ?_, (hg (Classical.arbitrary _)).1⟩
    rw [SetLike.mem_coe, mem_proLRes]
    intro N hN
    exact (hg ⟨N, hN⟩).2
