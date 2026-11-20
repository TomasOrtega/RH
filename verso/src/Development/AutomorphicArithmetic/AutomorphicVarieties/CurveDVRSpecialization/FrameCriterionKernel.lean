import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

open scoped Pointwise in
/- English proof (translation)
Take `⟨σ, hσ⟩` from `exists_smul_eq_of_isPlaceOver hA hB`. Establish `hlift : IsLift (RingEquiv.refl k) σ.toRingEquiv` using `fun x => σ.commutes x`. Establish `hmem : ∀ x : Ω, σ.toRingEquiv x ∈ B ↔ x ∈ A`. Introduce `x`. Rewrite using `[← hσ]`.

Conclude with `ValuationSubring.smul_mem_pointwise_smul_iff`. Use `⟨σ, fun τ hτ => ?_⟩` and prove the remaining obligations. Establish `h1` using `conjGal_mem_Ine hlift hmem hτ`. Establish `heq : conjGal hlift τ = σ⁻¹ * τ * σ` using `AlgEquiv.ext fun x => rfl`. Rewrite using `[← heq]`.

Conclude with `h1`.
-/
private theorem conj_ine {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : W.Plc k} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, ∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hB
  have hlift : IsLift (RingEquiv.refl k) σ.toRingEquiv := fun x => σ.commutes x
  have hmem : ∀ x : Ω, σ.toRingEquiv x ∈ B ↔ x ∈ A := by
    intro x
    rw [← hσ]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨σ, fun τ hτ => ?_⟩
  have h1 := conjGal_mem_Ine hlift hmem hτ
  have heq : conjGal hlift τ = σ⁻¹ * τ * σ := AlgEquiv.ext fun x => rfl
  rw [← heq]
  exact h1

/- English proof (translation)
Use `(QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨v, hv, A, hA, ht⟩`.
-/
private theorem ine_NS {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {S : Set (W.Plc k)} {A : ValuationSubring Ω} {v : W.Plc k} (hv : v ∉ S)
    (hA : IsPlaceOver A v) {t : G k Ω} (ht : t ∈ Ine (F := k) A) : toGS Ω S t = 1 := by
  refine (QuotientGroup.eq_one_iff t).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_))
  simp only [Set.mem_iUnion]
  exact ⟨v, hv, A, hA, ht⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `_ ⟨m, hm, rfl⟩ γ`. Distinguish the cases in `hγ : F.η γ = 1`. Conclude with `⟨⟨γ, hγ⟩ * m * (⟨γ, hγ⟩ : F.G₀)⁻¹, hN.conj_mem m hm _, rfl⟩`. Establish `hγ' : F.η γ = -1` using `(Int.units_eq_one_or _).resolve_left hγ`.

Establish `h0 : F.η (F.c⁻¹ * γ) = 1`. Rewrite using `[map_mul, map_inv, F.η_c, hγ']`. Simplify using the standard rewrite rules. Set `γ0 : F.G₀` to `⟨F.c⁻¹ * γ, h0⟩`. Use `⟨F.conj (γ0 * m * γ0⁻¹), hc _ (hN.conj_mem m hm γ0), ?_⟩` and prove the remaining obligations.

Use `show F.c * (F.c⁻¹ * γ * (m : F.Γ) * (F.c⁻¹ * γ)⁻¹) * F.c⁻¹ = γ * (m : F.Γ) * γ⁻¹`. Use `group`.
-/
private theorem normal_map {l : ℕ} [Fact l.Prime] (F : W.GFrame l) (N : Subgroup F.G₀) (hN : N.Normal)
    (hc : ∀ g ∈ N, F.conj g ∈ N) : (N.map F.η.ker.subtype).Normal := by
  constructor
  rintro _ ⟨m, hm, rfl⟩ γ
  by_cases hγ : F.η γ = 1
  · exact ⟨⟨γ, hγ⟩ * m * (⟨γ, hγ⟩ : F.G₀)⁻¹, hN.conj_mem m hm _, rfl⟩
  · have hγ' : F.η γ = -1 := (Int.units_eq_one_or _).resolve_left hγ
    have h0 : F.η (F.c⁻¹ * γ) = 1 := by
      rw [map_mul, map_inv, F.η_c, hγ']
      simp
    let γ0 : F.G₀ := ⟨F.c⁻¹ * γ, h0⟩
    refine ⟨F.conj (γ0 * m * γ0⁻¹), hc _ (hN.conj_mem m hm γ0), ?_⟩
    show F.c * (F.c⁻¹ * γ * (m : F.Γ) * (F.c⁻¹ * γ)⁻¹) * F.c⁻¹ = γ * (m : F.Γ) * γ⁻¹
    group

/- English proof (translation)
Unfold `UpperTheory.V.Pr.CrKer`. Introduce `Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS π hπ N hN hNc hNconj hIu hI0`. Set `N' : Subgroup V.frame.Γ` to `N.map V.frame.η.ker.subtype`. Use `haveI hN'n : N'.Normal := normal_map V.frame N hN hNconj`. Establish `hG0c : IsClosed (V.frame.η.ker : Set V.frame.Γ)` using `Subgroup.isClosed_of_isOpen _ V.frame.η_open`.

Establish `hN'c : IsClosed (N' : Set V.frame.Γ)`. Rewrite using `[Subgroup.coe_map]`. Conclude with `hG0c.isClosedEmbedding_subtypeVal.isClosedMap _ hNc`. Set `K : Subgroup (G (W.Lp L) Ω)` to `N'.comap (toGS Ω V.S')`. Establish `hKc : IsClosed (K : Set (G (W.Lp L) Ω))` using `hN'c.preimage (continuous_toGS Ω V.S')`.

Use `haveI hKn : K.Normal := hN'n.comap _`. Set `Kup : Subgroup (upl Ω L)` to `K.map (toUpl Ω L)`. Use `haveI hKupn : Kup.Normal := hKn.map _ toUpl_surj`. Establish `hind : Topology.IsInducing (toUpl Ω L)` using `(Topology.IsInducing.subtypeVal.of_comp_iff).1 (galEmbTop ℚ (W.Lp L) Ω).1.isInducing`. Establish `hKupc : IsClosed (Kup : Set (upl Ω L))`.

Take `⟨t, ht, hpre⟩` from `hind.isClosed_iff.1 hKc`. Rewrite using `[Subgroup.coe_map, ← hpre, Set.image_preimage_eq t toUpl_surj]`. Conclude with `ht`. Establish `hgen : ∀ u : upl Ω L, ∀ B' : ValuationSubring Ω, ¬B'.valuation (l : Ω) < 1 → (u : G ℚ Ω) ∈ Ine B' → barChar O Ψ (u : G ℚ Ω) = 1 → u ∈ Kup`. Introduce `u B' hl hIne hbar`.

Take `⟨τ, hτ⟩` from `toUpl_surj (Ω := Ω) (L := L) u`. Use `⟨τ, ?_, hτ⟩` and prove the remaining obligations. Establish `hτI : τ ∈ Ine (F` using `W.Lp L) B' := by`. Rewrite `hIne` using `[← hτ]`. Conclude with `hIne`.

Distinguish the cases in `htop : B' = ⊤`. Establish `hbot` using `((places (W.Lp L) Ω l B').2.1 htop).1`. Rewrite `hτI` using `[hbot]`. Rewrite using `[Subgroup.mem_bot.1 hτI]`. Conclude with `K.one_mem`.

Take `⟨v, hv⟩` from `(places (W.Lp L) Ω l B').1 htop`. Distinguish the cases in `hvS : v ∈ V.S'`. Establish `hvS' : v ∈ s.S` using `hS ▸ hvS`. Take `⟨h, hh⟩` from `conj_ine (s.hA v) hv`. Establish `hτ'` using `hh τ hτI`.

Take `⟨t, ht⟩` from `s.unr (s.A v) v (s.hA v) hτ'`. Establish `htI : t ∈ Ine (F` using `L) (s.A v) := by`. Establish `h1 : W.resP L Ω t ∈ Ine (F` using `W.Lp L) (s.A v) := by`. Rewrite using `[ht]`. Conclude with `hτ'`.

Conclude with `h1`. Establish `hprN : V.pr t ∈ N`. Break down `hvS' with hlv | hvSt | hv0` into its components or cases. It suffices to derive a contradiction. Conclude with `hl ((natCast_place hv l).2 hlv)`.

Apply `hIu ⟨v, hvSt⟩ (V.pr t) ⟨t, htI, rfl⟩` to reduce the goal to its premises. Rewrite using `[hπ t, k.galois_link_projection_coe, k.psi]`. Express the relevant statement in the definitionally equal form `barChar O Ψ (galEmb ℚ (W.Lp L) Ω (W.resP L Ω t)) = 1`. Rewrite using `[ht, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm ((barChar O Ψ) ((galEmb ℚ (W.Lp L) Ω) h))⁻¹ _, inv_mul_cancel_right]`. Establish `hu : (galEmb ℚ (W.Lp L) Ω) τ = (u : G ℚ Ω)`.

Rewrite using `[← hτ]`. Both sides reduce to the same expression. Rewrite using `[hu]`. Conclude with `hbar`. Apply `hI0` to reduce the goal to its premises.

Substitute `hv0` using the available equality. Conclude with `⟨t, htI, rfl⟩`. Establish `hτ'N : toGS Ω V.S' (h⁻¹ * τ * h) ∈ N'`. Use `⟨V.pr t, hprN, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `toGS Ω V.S' (W.resP L Ω t) = _`.

Rewrite using `[ht]`. Establish `hconj` using `hN'n.conj_mem _ hτ'N (toGS Ω V.S' h)`. Establish `heq : toGS Ω V.S' h * toGS Ω V.S' (h⁻¹ * τ * h) * (toGS Ω V.S' h)⁻¹ = toGS Ω V.S' τ`. Simplify using `only [map_mul, map_inv]`. Use `group`.

Express the relevant statement in the definitionally equal form `toGS Ω V.S' τ ∈ N'`. Rewrite using `[← heq]`. Conclude with `hconj`. Express the relevant statement in the definitionally equal form `toGS Ω V.S' τ ∈ N'`. Rewrite using `[ine_NS hvS hv hτI]`.

Conclude with `N'.one_mem`. Establish `hpker : k.p.ker ≤ Kup`. Rewrite using `[k.p_ker]`. Apply `Subgroup.topologicalClosure_minimal _ _ hKupc` to reduce the goal to its premises. Apply `Subgroup.normalClosure_le_normal` to reduce the goal to its premises.

Introduce and unpack `u ⟨B', hl, hIne, -, hbar⟩`. Conclude with `hgen u B' hl hIne hbar`. Introduce `g0 hg0`. Take `⟨g, rfl⟩` from `pr_surj V g0`. Establish `hp0 : k.p0 g = 1`.

Rewrite using `[← hπ g]`. Conclude with `hg0`. Establish `hpk : toUpl Ω L (W.resP L Ω g) ∈ k.p.ker`. Rewrite using `[MonoidHom.mem_ker, ← k.galois_link_projection_coe, hp0]`. Both sides reduce to the same expression.

Take `⟨τ, hτK, hτeq⟩` from `hpker hpk`. Establish `hτg : τ = W.resP L Ω g` using `toUpl_inj hτeq`. Take `⟨m, hm, hmeq⟩` from `hτK`. Establish `hpr : V.pr g = m`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `toGS Ω V.S' (W.resP L Ω g) = (m : V.frame.Γ)`. Rewrite using `[← hτg]`. Conclude with `hmeq.symm`. Rewrite using `[hpr]`. Conclude with `hm`.
-/
theorem UpperTheory.frame_criterion_kernel :
    UpperTheory.V.Pr.CrKer := by
  unfold UpperTheory.V.Pr.CrKer
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS π hπ N hN hNc hNconj hIu hI0
  let N' : Subgroup V.frame.Γ := N.map V.frame.η.ker.subtype
  haveI hN'n : N'.Normal := normal_map V.frame N hN hNconj
  have hG0c : IsClosed (V.frame.η.ker : Set V.frame.Γ) :=
    Subgroup.isClosed_of_isOpen _ V.frame.η_open
  have hN'c : IsClosed (N' : Set V.frame.Γ) := by
    rw [Subgroup.coe_map]
    exact hG0c.isClosedEmbedding_subtypeVal.isClosedMap _ hNc
  let K : Subgroup (G (W.Lp L) Ω) := N'.comap (toGS Ω V.S')
  have hKc : IsClosed (K : Set (G (W.Lp L) Ω)) := hN'c.preimage (continuous_toGS Ω V.S')
  haveI hKn : K.Normal := hN'n.comap _
  let Kup : Subgroup (upl Ω L) := K.map (toUpl Ω L)
  haveI hKupn : Kup.Normal := hKn.map _ toUpl_surj
  have hind : Topology.IsInducing (toUpl Ω L) :=
    (Topology.IsInducing.subtypeVal.of_comp_iff).1 (galEmbTop ℚ (W.Lp L) Ω).1.isInducing
  have hKupc : IsClosed (Kup : Set (upl Ω L)) := by
    obtain ⟨t, ht, hpre⟩ := hind.isClosed_iff.1 hKc
    rw [Subgroup.coe_map, ← hpre, Set.image_preimage_eq t toUpl_surj]
    exact ht
  have hgen : ∀ u : upl Ω L, ∀ B' : ValuationSubring Ω, ¬B'.valuation (l : Ω) < 1 →
      (u : G ℚ Ω) ∈ Ine B' → barChar O Ψ (u : G ℚ Ω) = 1 → u ∈ Kup := by
    intro u B' hl hIne hbar
    obtain ⟨τ, hτ⟩ := toUpl_surj (Ω := Ω) (L := L) u
    refine ⟨τ, ?_, hτ⟩
    have hτI : τ ∈ Ine (F := W.Lp L) B' := by
      rw [← hτ] at hIne
      exact hIne
    by_cases htop : B' = ⊤
    · have hbot := ((places (W.Lp L) Ω l B').2.1 htop).1
      rw [hbot] at hτI
      rw [Subgroup.mem_bot.1 hτI]
      exact K.one_mem
    obtain ⟨v, hv⟩ := (places (W.Lp L) Ω l B').1 htop
    by_cases hvS : v ∈ V.S'
    · have hvS' : v ∈ s.S := hS ▸ hvS
      obtain ⟨h, hh⟩ := conj_ine (s.hA v) hv
      have hτ' := hh τ hτI
      obtain ⟨t, ht⟩ := s.unr (s.A v) v (s.hA v) hτ'
      have htI : t ∈ Ine (F := L) (s.A v) := by
        have h1 : W.resP L Ω t ∈ Ine (F := W.Lp L) (s.A v) := by
          rw [ht]
          exact hτ'
        exact h1
      have hprN : V.pr t ∈ N := by
        rcases hvS' with hlv | hvSt | hv0
        · exfalso
          exact hl ((natCast_place hv l).2 hlv)
        · apply hIu ⟨v, hvSt⟩ (V.pr t) ⟨t, htI, rfl⟩
          rw [hπ t, k.galois_link_projection_coe, k.psi]
          change barChar O Ψ (galEmb ℚ (W.Lp L) Ω (W.resP L Ω t)) = 1
          rw [ht, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv,
            mul_comm ((barChar O Ψ) ((galEmb ℚ (W.Lp L) Ω) h))⁻¹ _, inv_mul_cancel_right]
          have hu : (galEmb ℚ (W.Lp L) Ω) τ = (u : G ℚ Ω) := by
            rw [← hτ]
            rfl
          rw [hu]
          exact hbar
        · apply hI0
          subst hv0
          exact ⟨t, htI, rfl⟩
      have hτ'N : toGS Ω V.S' (h⁻¹ * τ * h) ∈ N' := by
        refine ⟨V.pr t, hprN, ?_⟩
        change toGS Ω V.S' (W.resP L Ω t) = _
        rw [ht]
      have hconj := hN'n.conj_mem _ hτ'N (toGS Ω V.S' h)
      have heq : toGS Ω V.S' h * toGS Ω V.S' (h⁻¹ * τ * h) * (toGS Ω V.S' h)⁻¹ = toGS Ω V.S' τ := by
        simp only [map_mul, map_inv]
        group
      change toGS Ω V.S' τ ∈ N'
      rw [← heq]
      exact hconj
    · change toGS Ω V.S' τ ∈ N'
      rw [ine_NS hvS hv hτI]
      exact N'.one_mem
  have hpker : k.p.ker ≤ Kup := by
    rw [k.p_ker]
    apply Subgroup.topologicalClosure_minimal _ _ hKupc
    apply Subgroup.normalClosure_le_normal
    rintro u ⟨B', hl, hIne, -, hbar⟩
    exact hgen u B' hl hIne hbar
  intro g0 hg0
  obtain ⟨g, rfl⟩ := pr_surj V g0
  have hp0 : k.p0 g = 1 := by
    rw [← hπ g]
    exact hg0
  have hpk : toUpl Ω L (W.resP L Ω g) ∈ k.p.ker := by
    rw [MonoidHom.mem_ker, ← k.galois_link_projection_coe, hp0]
    rfl
  obtain ⟨τ, hτK, hτeq⟩ := hpker hpk
  have hτg : τ = W.resP L Ω g := toUpl_inj hτeq
  obtain ⟨m, hm, hmeq⟩ := hτK
  have hpr : V.pr g = m := by
    apply Subtype.ext
    change toGS Ω V.S' (W.resP L Ω g) = (m : V.frame.Γ)
    rw [← hτg]
    exact hmeq.symm
  rw [hpr]
  exact hm
