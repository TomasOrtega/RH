import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PhiGam
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Rewrite using `[totallyDisconnectedSpace_iff_connectedComponent_one]`. Use `Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`. Assume the negation of the conclusion as `hx`. Establish `hx' : x ∉ N` using `fun h => hx ((QuotientGroup.eq_one_iff x).2 h)`.

Establish `ho : IsOpen {g : G | g * x ∉ N}` using `hN.isOpen_compl.preimage (continuous_mul_const x)`. Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')`. Set `V : Subgroup (G ⧸ N)` to `U.toSubgroup.map (QuotientGroup.mk' N)`. Establish `hVo : IsOpen (V : Set (G ⧸ N))` using `QuotientGroup.isOpenMap_coe _ U.isOpen'`. Establish `hV : IsClopen (V : Set (G ⧸ N))` using `⟨V.isClosed_of_isOpen hVo, hVo⟩`.

Take `⟨u, hu, hux⟩` from `hV.connectedComponent_subset V.one_mem hy`. Conclude with `hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)`.
-/
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)

/- English proof (translation)
Introduce `hP Ω _ _ _ l hl c D hD P hc hu ⟨R₁, _, _, _, ρ₁, h₁⟩`. Take `⟨rb, r0, hb, -, -, -, H⟩` from `descend D hD`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, hk, -⟩` from `facts D hD`. Take `⟨_, _⟩` from `UpperTheory.V.Ws.Po.fin_res c`. Use `haveI : IsGalois ℚ Ω := {}`.

Use `haveI hcl := isClosed_NS Ω D.SP`. Use `haveI : CompactSpace D.Gam := inferInstance`. Use `haveI : T2Space D.Gam := inferInstance`. Use `haveI : TotallyDisconnectedSpace D.Gam := totDisc_quot _ hcl`. Establish `hq : Topology.IsQuotientMap (toGS Ω D.SP)` using `QuotientGroup.isQuotientMap_mk _`.

Establish `hlc : IsLocallyConstant D.rbar`. Use `(IsLocallyConstant.iff_exists_open _).2 fun g => ⟨(fun x => g⁻¹ * x) ⁻¹' (D.rbar.ker : Set _), hk.preimage (by fun_prop), by simp, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: D.rbar (g⁻¹ * x) = 1` using `hx`. Rewrite using `[← mul_inv_cancel_left g x, map_mul, this, mul_one]`. Establish `hlb : IsLocallyConstant rb` using `fun s => by`.

Rewrite using `[← hq.isOpen_preimage]`. Use `hlc s` as an intermediate fact. Rewrite `this` using `[← hb]`. Conclude with `this`. Take `⟨R, _, _, _, r, hr⟩` from `univ_lift l c.O D.Gam (Fin 4) rb (phiGam D hD hP) hlb`.

Take `⟨ρ, hρ, -⟩` from `(H R).1 r`. Set `P₀ : Cond c.O D.rbar` to `fun C _ _ _ s => ∃ t : Lift c.O rb C, s.hom = t.hom.comp (toGS Ω D.SP)`. Establish `hmap : ∀ (C : Type) [CommRing C] [Algebra c.O C] [IsCO c.O C] (f : R →ₐ[c.O] C), (ρ.map f).hom = (r.map f).hom.comp (toGS Ω D.SP)` using `fun C _ _ _ f => by`. Use extensionality with `g a b`. Use `show f (ρ.hom g a b) = f (r.hom _ a b)`.

Rewrite using `[hρ]`. Both sides reduce to the same expression. Establish `h0 : Represents P₀ ρ` using `fun C _ _ _ => by`. Use `⟨fun f => ⟨r.map f, hmap C f⟩, fun s ⟨t, ht⟩ => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, huq⟩` from `(hr C).2 t trivial`.

Use `⟨f, Lift.ext (by rw [hmap, hf, ht]), fun f' hf' => huq f' (Lift.ext ?_)⟩` and prove the remaining obligations. Use `(MonoidHom.cancel_right hq.surjective).1 ?_` and prove the remaining obligations. Rewrite using `[← hmap, ← ht]`. Conclude with `congrArg Lift.hom hf'`. Establish `hPP : ∀ (C : Type) [CommRing C] [Algebra c.O C] [IsCO c.O C] (s : Lift c.O D.rbar C), P C s → P₀ C s` using `fun C _ _ _ s h => (H C).2 s (hu C s h)`.

Take `⟨R', _, _, _, p, -, h⟩` from `univ_cond c.O (G ℚ Ω) (Fin 4) D.rbar R ρ P₀ P h0 hc ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁, hPP _ _ h₁, h₁⟩`. Conclude with `⟨R', inferInstance, inferInstance, inferInstance, ρ.map p, fun C _ _ _ => ⟨fun f => ((h C).1 f).2, fun r' h' => (h C).2 r' ⟨hPP _ _ h', h'⟩⟩⟩`.
-/
theorem UpperTheory.V.Ws.Po.univOf :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ P : Cond c.O D.rbar, P.IsClosed →
      (∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : Lift c.O D.rbar R), P R ρ → D.UnrT ρ.hom 1) →
      (∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O D.rbar R), P R ρ) →
      ∃ (U : Type) (_ : CommRing U) (_ : Algebra c.O U) (_ : IsCO c.O U) (ρ : Lift c.O D.rbar U), Represents P ρ := by
  intro hP Ω _ _ _ l hl c D hD P hc hu ⟨R₁, _, _, _, ρ₁, h₁⟩
  obtain ⟨rb, r0, hb, -, -, -, H⟩ := descend D hD
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := facts D hD
  obtain ⟨_, _⟩ := UpperTheory.V.Ws.Po.fin_res c
  haveI : IsGalois ℚ Ω := {}
  haveI hcl := isClosed_NS Ω D.SP
  haveI : CompactSpace D.Gam := inferInstance
  haveI : T2Space D.Gam := inferInstance
  haveI : TotallyDisconnectedSpace D.Gam := totDisc_quot _ hcl
  have hq : Topology.IsQuotientMap (toGS Ω D.SP) := QuotientGroup.isQuotientMap_mk _
  have hlc : IsLocallyConstant D.rbar := by
    refine (IsLocallyConstant.iff_exists_open _).2 fun g =>
      ⟨(fun x => g⁻¹ * x) ⁻¹' (D.rbar.ker : Set _), hk.preimage (by fun_prop), by simp, fun x hx => ?_⟩
    have : D.rbar (g⁻¹ * x) = 1 := hx
    rw [← mul_inv_cancel_left g x, map_mul, this, mul_one]
  have hlb : IsLocallyConstant rb := fun s => by
    rw [← hq.isOpen_preimage]
    have := hlc s
    rw [← hb] at this
    exact this
  obtain ⟨R, _, _, _, r, hr⟩ := univ_lift l c.O D.Gam (Fin 4) rb (phiGam D hD hP) hlb
  obtain ⟨ρ, hρ, -⟩ := (H R).1 r
  let P₀ : Cond c.O D.rbar := fun C _ _ _ s => ∃ t : Lift c.O rb C, s.hom = t.hom.comp (toGS Ω D.SP)
  have hmap : ∀ (C : Type) [CommRing C] [Algebra c.O C] [IsCO c.O C] (f : R →ₐ[c.O] C),
      (ρ.map f).hom = (r.map f).hom.comp (toGS Ω D.SP) := fun C _ _ _ f => by
    ext g a b
    show f (ρ.hom g a b) = f (r.hom _ a b)
    rw [hρ]
    rfl
  have h0 : Represents P₀ ρ := fun C _ _ _ => by
    refine ⟨fun f => ⟨r.map f, hmap C f⟩, fun s ⟨t, ht⟩ => ?_⟩
    obtain ⟨f, hf, huq⟩ := (hr C).2 t trivial
    refine ⟨f, Lift.ext (by rw [hmap, hf, ht]), fun f' hf' => huq f' (Lift.ext ?_)⟩
    refine (MonoidHom.cancel_right hq.surjective).1 ?_
    rw [← hmap, ← ht]
    exact congrArg Lift.hom hf'
  have hPP : ∀ (C : Type) [CommRing C] [Algebra c.O C] [IsCO c.O C] (s : Lift c.O D.rbar C), P C s → P₀ C s :=
    fun C _ _ _ s h => (H C).2 s (hu C s h)
  obtain ⟨R', _, _, _, p, -, h⟩ := univ_cond c.O (G ℚ Ω) (Fin 4) D.rbar R ρ P₀ P h0 hc
    ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁, hPP _ _ h₁, h₁⟩
  exact ⟨R', inferInstance, inferInstance, inferInstance, ρ.map p, fun C _ _ _ =>
    ⟨fun f => ((h C).1 f).2, fun r' h' => (h C).2 r' ⟨hPP _ _ h', h'⟩⟩⟩
