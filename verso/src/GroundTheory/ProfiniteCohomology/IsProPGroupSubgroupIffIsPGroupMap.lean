import Mathlib
import GroundTheory.ProfiniteCohomology.OpenNormal
import GroundTheory.ProfiniteCohomology.OfNatRelIndexSupAntitone
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

variable {G : Type*} [Group G] [TopologicalSpace G]

def IsProPGroup (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ (U : Subgroup G))

/- English proof (translation)
Use `forall_congr' fun U => ⟨fun h g => ?_, fun h x => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `h (g : G ⧸ (U : Subgroup G))`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`. Conclude with `hk`.

Proceed by induction on `x using QuotientGroup.induction_on with`. Consider the case `H g`. Take `⟨k, hk⟩` from `h g`. Conclude with `⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩`.
-/
theorem isProPGroup_iff {p : ℕ} :
    IsProPGroup p G ↔ ∀ U : OpenNormalSubgroup G, ∀ g : G, ∃ k : ℕ, g ^ p ^ k ∈ U := by
  refine forall_congr' fun U => ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ (U : Subgroup G))
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk
    exact hk
  · induction x using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨k, hk⟩ := h g
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

omit [TopologicalSpace G] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hp h hh`. Take `⟨k, hk⟩` from `hp ⟨QuotientGroup.mk' U h, Subgroup.mem_map_of_mem _ hh⟩`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hk'` using `congrArg Subtype.val hk`.

Simplify using `only [Subgroup.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply] at hk'`. Rewrite `hk'` using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`. Then use the resulting hypothesis. Introduce and unpack `h ⟨x, hx⟩`. Take `⟨g, hg, rfl⟩` from `Subgroup.mem_map.mp hx`. Take `⟨k, hk⟩` from `h g hg`.

Use `⟨k, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [Subgroup.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply]`. Rewrite using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`. Conclude with `hk`.
-/
theorem isPGroup_map_mk_iff {p : ℕ} (H U : Subgroup G) [U.Normal] :
    IsPGroup p (H.map (QuotientGroup.mk' U)) ↔ ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ U := by
  constructor
  · intro hp h hh
    obtain ⟨k, hk⟩ := hp ⟨QuotientGroup.mk' U h, Subgroup.mem_map_of_mem _ hh⟩
    refine ⟨k, ?_⟩
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply] at hk'
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk'
  · rintro h ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨k, hk⟩ := h g hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk

variable [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/- English proof (translation)
Take `⟨W, hWo, hWV⟩` from `isOpen_induced_iff.mp V.toOpenSubgroup.isOpen`. Establish `h1W : (1 : G) ∈ W`. Establish `: (1 : H) ∈ Subtype.val ⁻¹' W` using `hWV ▸ V.one_mem`. Simplify using `using this`. Take `⟨U, hUW⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W`.

Use `⟨U, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: (x : G) ∈ W` using `hUW hx`. Establish `: x ∈ Subtype.val ⁻¹' W` using `this`. Rewrite `this` using `[hWV]`. Conclude with `this`.
-/
theorem exists_subgroupOf_le {H : Subgroup G} (V : OpenNormalSubgroup H) :
    ∃ U : OpenNormalSubgroup G, (U : Subgroup G).subgroupOf H ≤ (V : Subgroup H) := by
  obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp V.toOpenSubgroup.isOpen
  have h1W : (1 : G) ∈ W := by
    have : (1 : H) ∈ Subtype.val ⁻¹' W := hWV ▸ V.one_mem
    simpa using this
  obtain ⟨U, hUW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo h1W
  refine ⟨U, fun x hx => ?_⟩
  have : (x : G) ∈ W := hUW hx
  have : x ∈ Subtype.val ⁻¹' W := this
  rw [hWV] at this
  exact this

/- English proof (translation)
Rewrite using `[isProPGroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hH U h hh`. Set `U' : OpenNormalSubgroup H` to `{ toSubgroup := (U : Subgroup G).subgroupOf H isOpen' := Subgroup.subgroupOf_isOpen H (U : Subgroup G) U.toOpenSubgroup.isOpen isNormal' := inferInstance }`. Take `⟨k, hk⟩` from `hH U' ⟨h, hh⟩`.

Conclude with `⟨k, hk⟩`. Introduce `hH V g`. Take `⟨U, hU⟩` from `exists_subgroupOf_le V`. Take `⟨k, hk⟩` from `hH U g g.2`. Conclude with `⟨k, hU (show (g ^ p ^ k : H) ∈ (U : Subgroup G).subgroupOf H from hk)⟩`.
-/
theorem isProPGroup_subgroup_iff {p : ℕ} {H : Subgroup G} :
    IsProPGroup p H ↔ ∀ U : OpenNormalSubgroup G, ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ U := by
  rw [isProPGroup_iff]
  constructor
  · intro hH U h hh
    let U' : OpenNormalSubgroup H :=
      { toSubgroup := (U : Subgroup G).subgroupOf H
        isOpen' := Subgroup.subgroupOf_isOpen H (U : Subgroup G) U.toOpenSubgroup.isOpen
        isNormal' := inferInstance }
    obtain ⟨k, hk⟩ := hH U' ⟨h, hh⟩
    exact ⟨k, hk⟩
  · intro hH V g
    obtain ⟨U, hU⟩ := exists_subgroupOf_le V
    obtain ⟨k, hk⟩ := hH U g g.2
    exact ⟨k, hU (show (g ^ p ^ k : H) ∈ (U : Subgroup G).subgroupOf H from hk)⟩

/- English proof (translation)
Rewrite using `[isProPGroup_subgroup_iff]`. Conclude with `forall_congr' fun U => (isPGroup_map_mk_iff H (U : Subgroup G)).symm`.
-/
theorem isProPGroup_subgroup_iff_isPGroup_map {p : ℕ} {H : Subgroup G} :
    IsProPGroup p H ↔
      ∀ U : OpenNormalSubgroup G, IsPGroup p (H.map (QuotientGroup.mk' (U : Subgroup G))) := by
  rw [isProPGroup_subgroup_iff]
  exact forall_congr' fun U => (isPGroup_map_mk_iff H (U : Subgroup G)).symm

/- English proof (translation)
Rewrite `hH`, the goal using `[isProPGroup_subgroup_iff]`. Conclude with `fun U k hk => hH U k (hKH hk)`.
-/
theorem IsProPGroup.of_le {p : ℕ} {H K : Subgroup G} (hH : IsProPGroup p H) (hKH : K ≤ H) :
    IsProPGroup p K := by
  rw [isProPGroup_subgroup_iff] at hH ⊢
  exact fun U k hk => hH U k (hKH hk)

/- English proof (translation)
Rewrite using `[isProPGroup_subgroup_iff]`. Introduce `U h hh`. Rewrite using `[Subgroup.mem_bot.mp hh]`. Conclude with `⟨0, by simp⟩`.
-/
theorem isProPGroup_bot (p : ℕ) : IsProPGroup p (⊥ : Subgroup G) := by
  rw [isProPGroup_subgroup_iff]
  intro U h hh
  rw [Subgroup.mem_bot.mp hh]
  exact ⟨0, by simp⟩

end GroundTheory.ProfCoh
