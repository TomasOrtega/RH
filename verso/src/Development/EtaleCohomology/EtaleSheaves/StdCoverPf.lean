import Development.EtaleCohomology.EtaleSheaves.PullInjOfIso

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StdCoverPf

/- English proof (translation)
Establish `h : Mono (yoneda.map (Spec.map (CommRingCat.ofHom φ)))` using `inferInstance`. Use `haveI : ∀ X, Mono ((spMap φ).app X) := fun _ => h`. Conclude with `NatTrans.mono_of_mono_app _`.
-/
theorem mono_spMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    [Mono (Spec.map (CommRingCat.ofHom φ))] : Mono (spMap φ) := by
  have h : Mono (yoneda.map (Spec.map (CommRingCat.ofHom φ))) := inferInstance
  haveI : ∀ X, Mono ((spMap φ).app X) := fun _ => h
  exact NatTrans.mono_of_mono_app _

abbrev Xs {S : Type} [CommRing S] (f g : S) (b : Bool) : Scheme.{0} :=
  Spec (CommRingCat.of (Localization.Away (bif b then f else g)))

abbrev ι {S : Type} [CommRing S] (f g : S) (b : Bool) : Xs f g b ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (bif b then f else g))))

/- English proof (translation)
Apply `Precoverage.generate_mem_toGrothendieck` to reduce the goal to its premises. Use `(Scheme.ofArrows_mem_precoverage_iff (P := @Etale) (f := ι f g)).2 ⟨fun pt => ?_, fun b => inferInstance⟩` and prove the remaining obligations. Set `p : PrimeSpectrum S` to `pt`. Establish `hp : f ∉ p.asIdeal ∨ g ∉ p.asIdeal`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Establish `: Ideal.span {f, g} ≤ p.asIdeal`. Rewrite using `[Ideal.span_le]`. Introduce `z hz`. Break down `hz with rfl | hz` into its components or cases.

Conclude with `hc.1`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Conclude with `hz ▸ hc.2`. Rewrite `this` using `[hfg]`. Conclude with `p.isPrime.ne_top (top_le_iff.mp this)`.

Break down `hp with h | h` into its components or cases. Establish `hm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f)))`. Rewrite using `[PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]`. Conclude with `h`. Take `⟨q, hq⟩` from `hm`.

Conclude with `⟨true, q, hq⟩`. Establish `hm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g)))`. Rewrite using `[PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]`. Conclude with `h`. Take `⟨q, hq⟩` from `hm`.

Conclude with `⟨false, q, hq⟩`.
-/
theorem cover_mem {S : Type} [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤) :
    Sieve.ofArrows (Xs f g) (ι f g) ∈ Scheme.etaleTopology.{0} (Spec (CommRingCat.of S)) := by
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale) (f := ι f g)).2 ⟨fun pt => ?_, fun b => inferInstance⟩
  let p : PrimeSpectrum S := pt
  have hp : f ∉ p.asIdeal ∨ g ∉ p.asIdeal := by
    by_contra hc
    push_neg at hc
    have : Ideal.span {f, g} ≤ p.asIdeal := by
      rw [Ideal.span_le]; intro z hz
      rcases hz with rfl | hz
      · exact hc.1
      · rw [Set.mem_singleton_iff] at hz; exact hz ▸ hc.2
    rw [hfg] at this
    exact p.isPrime.ne_top (top_le_iff.mp this)
  rcases hp with h | h
  · have hm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]; exact h
    obtain ⟨q, hq⟩ := hm
    exact ⟨true, q, hq⟩
  · have hm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]; exact h
    obtain ⟨q, hq⟩ := hm
    exact ⟨false, q, hq⟩

/- English proof (translation)
Set `adj` to `sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))`. Apply `(adj.homEquiv ((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))) G).injective` to reduce the goal to its premises. Establish `hb' : ∀ b, (freeP R).map (yoneda.map (ι f g b)) ≫ adj.homEquiv _ G u = (freeP R).map (yoneda.map (ι f g b)) ≫ adj.homEquiv _ G v`. Introduce `b`. Establish `h0 : (presheafToSheaf _ _).map ((freeP R).map (yoneda.map (ι f g b))) ≫ u = (presheafToSheaf _ _).map ((freeP R).map (yoneda.map (ι f g b))) ≫ v` using `hb b`.

Establish `h1` using `congrArg (adj.homEquiv _ G) h0`. Use `erw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at h1`. Conclude with `h1`. Generalize the expression as in `adj.homEquiv _ G u = u' at hb' ⊢`. Generalize the expression as in `adj.homEquiv _ G v = v' at hb' ⊢`.

Use extensionality with `X : 2`. Apply `ModuleCat.free_hom_ext` to reduce the goal to its premises. Introduce `x0`. Establish `hT` using `Scheme.etaleTopology.pullback_stable x0.down (cover_mem f g hfg)`. Establish `e` using `G.cond.hom_ext ⟨_, hT⟩ (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (u'.app X (ModuleCat.freeMk x0)))) (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (v'.app X (ModuleCat.freeMk x0)))) ?_`.

Use `congrArg (fun e => e.hom 1) e` as an intermediate fact. Simplify using `only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul] at this`. Conclude with `this`. Introduce and unpack `⟨W, k, hk⟩`. Take `⟨Z, h, _, ⟨b⟩, hh⟩` from `hk`.

Use `ext1`. Apply `LinearMap.ext_ring` to reduce the goal to its premises. Simplify using `only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply, LinearMap.toSpanSingleton_apply, one_smul]`. Establish `hm : (((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0) = (((freeP R).map (yoneda.map (ι f g b))).app (op W)).hom (ModuleCat.freeMk (ULift.up h))`. Simplify using `only [freeP, ModuleCat.freeMk]`.

Use `erw [Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.mapDomain_single]`. Express the relevant statement in the definitionally equal form `Finsupp.single (ULift.up (k ≫ x0.down)) _ = Finsupp.single (ULift.up (h ≫ ι f g b)) _`. Rewrite using `[hh]`. Express the relevant statement in the definitionally equal form `((u'.app X ≫ (G.obj.map k.op)).hom (ModuleCat.freeMk x0)) = ((v'.app X ≫ (G.obj.map k.op)).hom (ModuleCat.freeMk x0))`. Use `erw [← u'.naturality, ← v'.naturality]`.

Express the relevant statement in the definitionally equal form `(u'.app (op W)).hom ((((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0)) = (v'.app (op W)).hom ((((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0))`. Rewrite using `[hm]`. Express the relevant statement in the definitionally equal form `((((freeP R).map (yoneda.map (ι f g b))) ≫ u').app (op W)).hom (ModuleCat.freeMk (ULift.up h)) = ((((freeP R).map (yoneda.map (ι f g b))) ≫ v').app (op W)).hom (ModuleCat.freeMk (ULift.up h))`. Rewrite using `[hb' b]`.
-/
theorem key (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤) {G : Shv R}
    (u v : (free R).obj (yoneda.obj (Spec (CommRingCat.of S))) ⟶ G)
    (hb : ∀ b, (free R).map (yoneda.map (ι f g b)) ≫ u = (free R).map (yoneda.map (ι f g b)) ≫ v) : u = v := by
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  apply (adj.homEquiv ((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))) G).injective
  have hb' : ∀ b, (freeP R).map (yoneda.map (ι f g b)) ≫ adj.homEquiv _ G u =
      (freeP R).map (yoneda.map (ι f g b)) ≫ adj.homEquiv _ G v := by
    intro b
    have h0 : (presheafToSheaf _ _).map ((freeP R).map (yoneda.map (ι f g b))) ≫ u =
        (presheafToSheaf _ _).map ((freeP R).map (yoneda.map (ι f g b))) ≫ v := hb b
    have h1 := congrArg (adj.homEquiv _ G) h0
    erw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at h1
    exact h1
  generalize adj.homEquiv _ G u = u' at hb' ⊢
  generalize adj.homEquiv _ G v = v' at hb' ⊢
  ext X : 2
  apply ModuleCat.free_hom_ext
  intro x0
  have hT := Scheme.etaleTopology.pullback_stable x0.down (cover_mem f g hfg)
  have e := G.cond.hom_ext ⟨_, hT⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (u'.app X (ModuleCat.freeMk x0))))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (v'.app X (ModuleCat.freeMk x0)))) ?_
  · have := congrArg (fun e => e.hom 1) e
    simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul] at this
    exact this
  rintro ⟨W, k, hk⟩
  obtain ⟨Z, h, _, ⟨b⟩, hh⟩ := hk
  ext1
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.toSpanSingleton_apply, one_smul]
  have hm : (((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0) =
      (((freeP R).map (yoneda.map (ι f g b))).app (op W)).hom (ModuleCat.freeMk (ULift.up h)) := by
    simp only [freeP, ModuleCat.freeMk]
    erw [Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    change Finsupp.single (ULift.up (k ≫ x0.down)) _ = Finsupp.single (ULift.up (h ≫ ι f g b)) _
    rw [hh]
  change ((u'.app X ≫ (G.obj.map k.op)).hom (ModuleCat.freeMk x0)) =
    ((v'.app X ≫ (G.obj.map k.op)).hom (ModuleCat.freeMk x0))
  erw [← u'.naturality, ← v'.naturality]
  change (u'.app (op W)).hom ((((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0)) =
    (v'.app (op W)).hom ((((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0))
  rw [hm]
  change ((((freeP R).map (yoneda.map (ι f g b))) ≫ u').app (op W)).hom (ModuleCat.freeMk (ULift.up h)) =
    ((((freeP R).map (yoneda.map (ι f g b))) ≫ v').app (op W)).hom (ModuleCat.freeMk (ULift.up h))
  rw [hb' b]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `G u v h`. Establish `hf` using `congrArg (biprod.inl ≫ ·) h`. Establish `hg` using `congrArg (biprod.inr ≫ ·) h`. Simplify using `only [biprod.inl_desc_assoc, biprod.inr_desc_assoc] at hf hg`.

Conclude with `key R S f g hfg u v (fun b => by cases b; exacts [hg, hf])`.
-/
theorem epi_cover (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤)
    (n : SimplexCategoryᵒᵖ) :
    Epi (biprod.desc ((free R).map ((spMap (algebraMap S (Localization.Away f))).app n))
      ((free R).map ((spMap (algebraMap S (Localization.Away g))).app n))) := by
  constructor
  intro G u v h
  have hf := congrArg (biprod.inl ≫ ·) h
  have hg := congrArg (biprod.inr ≫ ·) h
  simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc] at hf hg
  exact key R S f g hfg u v (fun b => by cases b; exacts [hg, hf])

end LateralTheory.E.StdCoverPf

open LateralTheory.E.StdCoverPf in
/- English proof (translation)
Introduce `R _ S _ f g hfg`. Conclude with `⟨mono_spMap _, mono_spMap _, epi_cover R S f g hfg⟩`.
-/
theorem LateralTheory.E.MVPf.StdCover_of : LateralTheory.E.MVPf.StdCover := by
  intro R _ S _ f g hfg
  exact ⟨mono_spMap _, mono_spMap _, epi_cover R S f g hfg⟩
