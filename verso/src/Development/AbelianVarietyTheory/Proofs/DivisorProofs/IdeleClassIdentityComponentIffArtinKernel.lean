import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.ArtinKernel

variable {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`. Set `N : Subgroup (Formalism.ConjugateSelfDual.G K Ω)` to `(commutator (Formalism.ConjugateSelfDual.G K Ω)).topologicalClosure`. Establish `hN : IsClosed (N : Set (Formalism.ConjugateSelfDual.G K Ω))` using `Subgroup.isClosed_topologicalClosure _`. Establish `hx : x ∉ N` using `fun h => hne ((QuotientGroup.eq_one_iff x).2 h)`.

Establish `e` using `ProfiniteGrp.closedSubgroup_eq_sInf_open (G := Formalism.ConjugateSelfDual.G K Ω) ⟨N, hN⟩`. Establish `hx' : x ∉ sInf {M : Subgroup (Formalism.ConjugateSelfDual.G K Ω) | IsOpen (M : Set (Formalism.ConjugateSelfDual.G K Ω)) ∧ N ≤ M}`. Introduce `h`. Rewrite `h` using `[← e]`. Conclude with `hx h`.

Rewrite `hx'` using `[Subgroup.mem_sInf]`. Use `push_neg at hx'`. Take `⟨M, ⟨hMo, hNM⟩, hxM⟩` from `hx'`. Set `V : Subgroup (GlobalTheory.HeckeGal.Gab K Ω)` to `M.map (QuotientGroup.mk' N)`. Establish `hVo : IsOpen (V : Set (GlobalTheory.HeckeGal.Gab K Ω))`.

Establish `: (V : Set (GlobalTheory.HeckeGal.Gab K Ω)) = (QuotientGroup.mk : Formalism.ConjugateSelfDual.G K Ω → _) '' (M : Set _)`. Rewrite using `[Subgroup.coe_map]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `QuotientGroup.isOpenMap_coe _ hMo`.

Establish `hVc : IsClopen (V : Set (GlobalTheory.HeckeGal.Gab K Ω))` using `⟨Subgroup.isClosed_of_isOpen V hVo, hVo⟩`. Establish `hsub` using `hVc.connectedComponent_subset V.one_mem`. Take `⟨m, hm, hmx⟩` from `hsub hy`. Apply `hxM` to reduce the goal to its premises. Establish `: m⁻¹ * x ∈ N` using `(QuotientGroup.eq).1 hmx`.

Use `M.mul_mem hm (hNM this)` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_one_of_mem_connectedComponent_one (y : GlobalTheory.HeckeGal.Gab K Ω)
    (hy : y ∈ connectedComponent (1 : GlobalTheory.HeckeGal.Gab K Ω)) : y = 1 := by
  by_contra hne
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  let N : Subgroup (Formalism.ConjugateSelfDual.G K Ω) := (commutator (Formalism.ConjugateSelfDual.G K Ω)).topologicalClosure
  have hN : IsClosed (N : Set (Formalism.ConjugateSelfDual.G K Ω)) := Subgroup.isClosed_topologicalClosure _
  have hx : x ∉ N := fun h => hne ((QuotientGroup.eq_one_iff x).2 h)
  have e := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := Formalism.ConjugateSelfDual.G K Ω) ⟨N, hN⟩
  have hx' : x ∉ sInf {M : Subgroup (Formalism.ConjugateSelfDual.G K Ω) | IsOpen (M : Set (Formalism.ConjugateSelfDual.G K Ω)) ∧ N ≤ M} := by
    intro h
    rw [← e] at h
    exact hx h
  rw [Subgroup.mem_sInf] at hx'
  push_neg at hx'
  obtain ⟨M, ⟨hMo, hNM⟩, hxM⟩ := hx'
  let V : Subgroup (GlobalTheory.HeckeGal.Gab K Ω) := M.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (GlobalTheory.HeckeGal.Gab K Ω)) := by
    have : (V : Set (GlobalTheory.HeckeGal.Gab K Ω)) = (QuotientGroup.mk : Formalism.ConjugateSelfDual.G K Ω → _) '' (M : Set _) := by
      rw [Subgroup.coe_map]; rfl
    rw [this]
    exact QuotientGroup.isOpenMap_coe _ hMo
  have hVc : IsClopen (V : Set (GlobalTheory.HeckeGal.Gab K Ω)) := ⟨Subgroup.isClosed_of_isOpen V hVo, hVo⟩
  have hsub := hVc.connectedComponent_subset V.one_mem
  obtain ⟨m, hm, hmx⟩ := hsub hy
  apply hxM
  have : m⁻¹ * x ∈ N := (QuotientGroup.eq).1 hmx
  have := M.mul_mem hm (hNM this)
  simpa using this

/- English proof (translation)
Establish `hker` using `h.ker`. Establish `hR : (diagUnits K).range ≤ art.ker`. Rewrite using `[hker]`. Conclude with `le_trans le_sup_left (Subgroup.le_topologicalClosure _)`. Set `f : IdeleClassGroup K →* GlobalTheory.HeckeGal.Gab K Ω` to `QuotientGroup.lift _ art hR`.

Establish `hf : Continuous f` using `(QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr h.quot.continuous`. Prove the components needed by the constructor for the conclusion. Introduce `hs`. Use `hf.image_connectedComponent_subset (1 : IdeleClassGroup K) ⟨_, hs, rfl⟩` as an intermediate fact. Rewrite `this` using `[map_one]`.

Conclude with `eq_one_of_mem_connectedComponent_one _ this`. Introduce `hs`. Establish `hs' : s ∈ ((diagUnits K).range ⊔ GlobalTheory.HeckeGal.infConn K).topologicalClosure`. Rewrite using `[← hker]`. Conclude with `hs`.

Establish `hC : IsClosed ((QuotientGroup.mk : Ideles K → IdeleClassGroup K) ⁻¹' connectedComponent 1)` using `isClosed_connectedComponent.preimage continuous_quot_mk`. Establish `hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)))` using `Continuous.units_map _ (continuous_id.prodMk continuous_const)`. Establish `hsub : (((diagUnits K).range ⊔ GlobalTheory.HeckeGal.infConn K : Subgroup (Ideles K)) : Set (Ideles K)) ⊆ (QuotientGroup.mk : Ideles K → IdeleClassGroup K) ⁻¹' connectedComponent 1`. Introduce `y hy`. Take `⟨a, ⟨k, rfl⟩, b, ⟨c, hc, rfl⟩, rfl⟩` from `Subgroup.mem_sup.1 hy`.

Establish `e : (QuotientGroup.mk (diagUnits K k * Units.map (MonoidHom.inl _ _) c) : IdeleClassGroup K) = QuotientGroup.mk (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) c)`. Use `QuotientGroup.eq.2 ⟨k⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv, mul_inv_rev]`. Use `first`. Consider the case `exact (inv_mul_cancel_comm _ _).symm`.

Consider the case `(rw [mul_comm, mul_inv_cancel_left])`. Consider the case `simp [mul_comm, mul_assoc]`. Use `show _ ∈ connectedComponent 1`. Rewrite using `[e]`. Establish `hg : Continuous (fun c : (InfiniteAdeleRing K)ˣ => (QuotientGroup.mk (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) c) : IdeleClassGroup K))` using `continuous_quot_mk.comp hinl`.

Use `hg.image_connectedComponent_subset 1 ⟨c, hc, rfl⟩` as an intermediate fact. Use `beta_reduce at this`. Establish `h1 : (QuotientGroup.mk (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) 1) : IdeleClassGroup K) = 1` using `by rw [map_one]; rfl`. Rewrite `this` using `[h1]`. Conclude with `this`.

Establish `hcl` using `closure_minimal hsub hC`. Rewrite `hcl` using `[← Subgroup.topologicalClosure_coe]`. Conclude with `hcl hs'`.
-/
theorem mk_mem_connectedComponent_iff {art : Ideles K →* GlobalTheory.HeckeGal.Gab K Ω}
    (h : GlobalTheory.HeckeGal.IsGlobalArtin art) (s : Ideles K) :
    (QuotientGroup.mk s : IdeleClassGroup K) ∈ connectedComponent (1 : IdeleClassGroup K) ↔ art s = 1 := by
  have hker := h.ker
  have hR : (diagUnits K).range ≤ art.ker := by
    rw [hker]; exact le_trans le_sup_left (Subgroup.le_topologicalClosure _)
  let f : IdeleClassGroup K →* GlobalTheory.HeckeGal.Gab K Ω := QuotientGroup.lift _ art hR
  have hf : Continuous f := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr h.quot.continuous
  constructor
  · intro hs
    have := hf.image_connectedComponent_subset (1 : IdeleClassGroup K) ⟨_, hs, rfl⟩
    rw [map_one] at this
    exact eq_one_of_mem_connectedComponent_one _ this
  · intro hs
    have hs' : s ∈ ((diagUnits K).range ⊔ GlobalTheory.HeckeGal.infConn K).topologicalClosure := by
      rw [← hker]; exact hs
    have hC : IsClosed ((QuotientGroup.mk : Ideles K → IdeleClassGroup K) ⁻¹' connectedComponent 1) :=
      isClosed_connectedComponent.preimage continuous_quot_mk
    have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) :=
      Continuous.units_map _ (continuous_id.prodMk continuous_const)
    have hsub : (((diagUnits K).range ⊔ GlobalTheory.HeckeGal.infConn K : Subgroup (Ideles K)) : Set (Ideles K)) ⊆
        (QuotientGroup.mk : Ideles K → IdeleClassGroup K) ⁻¹' connectedComponent 1 := by
      intro y hy
      obtain ⟨a, ⟨k, rfl⟩, b, ⟨c, hc, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hy
      have e : (QuotientGroup.mk (diagUnits K k * Units.map (MonoidHom.inl _ _) c) : IdeleClassGroup K) =
          QuotientGroup.mk (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) c) := by
        refine QuotientGroup.eq.2 ⟨k⁻¹, ?_⟩
        rw [map_inv, mul_inv_rev]
        first
          | exact (inv_mul_cancel_comm _ _).symm
          | (rw [mul_comm, mul_inv_cancel_left])
          | simp [mul_comm, mul_assoc]
      show _ ∈ connectedComponent 1
      rw [e]
      have hg : Continuous (fun c : (InfiniteAdeleRing K)ˣ =>
          (QuotientGroup.mk (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) c) :
            IdeleClassGroup K)) := continuous_quot_mk.comp hinl
      have := hg.image_connectedComponent_subset 1 ⟨c, hc, rfl⟩
      beta_reduce at this
      have h1 : (QuotientGroup.mk (Units.map (MonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) 1) :
          IdeleClassGroup K) = 1 := by rw [map_one]; rfl
      rw [h1] at this
      exact this
    have hcl := closure_minimal hsub hC
    rw [← Subgroup.topologicalClosure_coe] at hcl
    exact hcl hs'

/- English proof (translation)
Introduce `h s` and use `mk_mem_connectedComponent_iff h s`.
-/
theorem idele_class_mem_identity_component_iff :
    ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
      {art : Ideles K →* GlobalTheory.HeckeGal.Gab K Ω}, GlobalTheory.HeckeGal.IsGlobalArtin art → ∀ s : Ideles K,
      (QuotientGroup.mk s : IdeleClassGroup K) ∈ connectedComponent (1 : IdeleClassGroup K) ↔ art s = 1 :=
  fun h s => mk_mem_connectedComponent_iff h s

end GlobalTheory.ArtinKernel
