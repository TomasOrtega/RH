import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

/- English proof (translation)
Establish `h1 : (l : Ω) ≠ 0`. Introduce `h`. Apply `hl` to reduce the goal to its premises. Apply `(algebraMap k Ω).injective` to reduce the goal to its premises. Rewrite using `[map_natCast, h, map_zero]`.

Establish `h2 : IsUnit (l : Ω)` using `isUnit_iff_ne_zero.mpr h1`. Establish `h3` using `h2.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm`. Simplify using `using h3`.
-/
private theorem l_unit (l : ℕ) {k : Type} [Field k] (hl : (l : k) ≠ 0) (Ω : Type) [Field Ω] [Algebra k Ω] :
    IsUnit (l : Γ(sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    intro h
    apply hl
    apply (algebraMap k Ω).injective
    rw [map_natCast, h, map_zero]
  have h2 : IsUnit (l : Ω) := isUnit_iff_ne_zero.mpr h1
  have h3 := h2.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm
  simpa using h3

/- English proof (translation)
Introduce `hEt hBc hClos hEx hTr hOpEt hOpBc hSpl l _ k _ hl H Ω _ _ g d hd`. Take `⟨_, _, hcard⟩` from `hd`. Establish `gs : GalSplit (H.s g)` using `hClos (H.s g) d hcard`. Set `g₀ : sp Ω ⟶ sp k` to `Spec.map (CommRingCat.ofHom (algebraMap k Ω))`. Establish `hT : (et l (sp Ω)).Good` using `hEt l (sp Ω) (l_unit l hl Ω)`.

Establish `hT' : ((et l (sp Ω)).bc g₀).Good` using `hBc _ g₀ hT`. Establish `hs : H.sΩ Ω g = bcMap g₀ (H.s g) rfl` using `rfl`. Establish `ht : H.tΩ Ω g = bcMap g₀ (H.t g) (H.comm g)` using `rfl`. Establish `hfe` using `hSpl g₀ H.q (H.s g ≫ H.q) H.q (H.s g) rfl (𝟙 _) (Category.id_comp _) PEmpty (fun j => j.elim) (fun j => j.elim)`. Take `⟨_, _, -⟩` from `hfe`.

Establish `hEq` using `hOpEt l (pullback.snd H.q g₀) (pullback.snd H.q g₀) (bcMap g₀ (H.s g) rfl) (bcMap g₀ (H.t g) (H.comm g)) ((bcMap_snd g₀ (H.t g) (H.comm g)).trans (bcMap_snd g₀ (H.s g) rfl).symm)`. Establish `toCorr : ∀ A, ((et l (sp Ω)).bc g₀).IsOp H.q H.q (H.s g) (H.t g) A → IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) A`. Introduce `A hA`. Establish `h1` using `hOpBc (et l (sp Ω)) g₀ H.q (H.s g ≫ H.q) H.q (H.s g) (H.t g) rfl (H.comm g) A hA`. Conclude with `(hEq A).1 h1`.

Establish `hex : ∃ A, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) A`. Take `⟨A, hA, -⟩` from `(hEx _ hT' H.q H.q (H.s g) (H.t g) (H.comm g)).1 gs`. Conclude with `⟨A, toCorr A hA⟩`. Establish `hspec : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (hop l H Ω g)`. Unfold `hop`.

Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`. Use `⟨hspec, fun tr htr => ?_⟩` and prove the remaining obligations. Establish `hA` using `((hTr _ hT' H.q (H.s g ≫ H.q) H.q (H.s g) (H.t g) rfl (H.comm g) tr htr) _).2 gs rfl`. Establish `hcorr` using `toCorr _ hA`.

Take `⟨tr', htr'⟩` from `hT.tr (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀) (bcMap g₀ (H.s g) rfl) (bcMap_snd _ _ _)`. Establish `key` using `fun A => hTr _ hT (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀) (pullback.snd H.q g₀) (bcMap g₀ (H.s g) rfl) (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _) (bcMap_snd _ _ _) tr' htr' A`. Establish `e1` using `(key _).1 ((hEq _).2 hspec)`. Establish `e2` using `(key _).1 ((hEq _).2 hcorr)`. Conclude with `e1.trans e2.symm`.
-/
theorem UpperTheory.Gal.G3.pHopSpec :
    EtGood → BcGood.{1} → GalClos → OpEx.{1} → OpTr.{1} → OpEt → OpBc.{1} → BcSplits → HopSpec := by
  intro hEt hBc hClos hEx hTr hOpEt hOpBc hSpl l _ k _ hl H Ω _ _ g d hd
  obtain ⟨_, _, hcard⟩ := hd
  have gs : GalSplit (H.s g) := hClos (H.s g) d hcard
  let g₀ : sp Ω ⟶ sp k := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  have hT : (et l (sp Ω)).Good := hEt l (sp Ω) (l_unit l hl Ω)
  have hT' : ((et l (sp Ω)).bc g₀).Good := hBc _ g₀ hT
  have hs : H.sΩ Ω g = bcMap g₀ (H.s g) rfl := rfl
  have ht : H.tΩ Ω g = bcMap g₀ (H.t g) (H.comm g) := rfl
  have hfe := hSpl g₀ H.q (H.s g ≫ H.q) H.q (H.s g) rfl (𝟙 _) (Category.id_comp _) PEmpty (fun j => j.elim) (fun j => j.elim)
  obtain ⟨_, _, -⟩ := hfe
  have hEq := hOpEt l (pullback.snd H.q g₀) (pullback.snd H.q g₀) (bcMap g₀ (H.s g) rfl) (bcMap g₀ (H.t g) (H.comm g))
    ((bcMap_snd g₀ (H.t g) (H.comm g)).trans (bcMap_snd g₀ (H.s g) rfl).symm)
  have toCorr : ∀ A, ((et l (sp Ω)).bc g₀).IsOp H.q H.q (H.s g) (H.t g) A → IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) A := by
    intro A hA
    have h1 := hOpBc (et l (sp Ω)) g₀ H.q (H.s g ≫ H.q) H.q (H.s g) (H.t g) rfl (H.comm g) A hA
    exact (hEq A).1 h1
  have hex : ∃ A, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) A := by
    obtain ⟨A, hA, -⟩ := (hEx _ hT' H.q H.q (H.s g) (H.t g) (H.comm g)).1 gs
    exact ⟨A, toCorr A hA⟩
  have hspec : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (hop l H Ω g) := by
    unfold hop
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hspec, fun tr htr => ?_⟩
  have hA := ((hTr _ hT' H.q (H.s g ≫ H.q) H.q (H.s g) (H.t g) rfl (H.comm g) tr htr) _).2 gs rfl
  have hcorr := toCorr _ hA
  obtain ⟨tr', htr'⟩ := hT.tr (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀) (bcMap g₀ (H.s g) rfl) (bcMap_snd _ _ _)
  have key := fun A => hTr _ hT (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀) (pullback.snd H.q g₀)
    (bcMap g₀ (H.s g) rfl) (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _) (bcMap_snd _ _ _) tr' htr' A
  have e1 := (key _).1 ((hEq _).2 hspec)
  have e2 := (key _).1 ((hEq _).2 hcorr)
  exact e1.trans e2.symm
