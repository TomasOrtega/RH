import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Izumi

/- English proof (translation)
Set `χ' : M.Z.presheaf.stalk x ⟶ CommRingCat.of (OO p)` to `CommRingCat.ofHom (χ.comp (M.stalkEquiv x).toRingHom)`. Use `haveI : IsLocalHom χ'.hom := by`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1 : IsUnit (M.stalkEquiv x a)` using `isUnit_of_map_unit χ _ ha`. Conclude with `(MulEquiv.isUnit_map (M.stalkEquiv x).toMulEquiv).1 h1`.

Use `set y : Sp (OO p) ⟶ M.Z := Spec.map χ' ≫ M.Z.fromSpecStalk x with hy`. Establish `hc : y (cPt p) = x`. Rewrite using `[hy, Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]`. Establish `key : ∀ h : y (cPt p) ⤳ x, M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y = χ'`. Introduce `h`.

Use `TopCat.Presheaf.stalk_hom_ext _ fun W hxW => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]`. Conclude with `Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk χ' W _`. Use `⟨y, hc, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[RatModel.val_gPt hc a]`.

Express the relevant statement in the definitionally equal form `(((M.Z.presheaf.stalkSpecializes _ ≫ Scheme.stalkClosedPointTo y).hom ((M.stalkEquiv x).symm a) : OO p) : PadicAlgCl p) = _`. Rewrite using `[key]`. Conclude with `congrArg (fun b => ((χ b : OO p) : PadicAlgCl p)) ((M.stalkEquiv x).apply_symm_apply a)`.
-/
theorem exists_point_of_isLocalHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (x : M.Z)
    {p : ℕ} [Fact p.Prime] (χ : M.O x →+* OO p) [IsLocalHom χ] :
    ∃ y : Sp (OO p) ⟶ M.Z, y (cPt p) = x ∧ ∀ a : M.O x,
      M.val (gPt p ≫ y) a = ((χ a : OO p) : PadicAlgCl p) := by
  let χ' : M.Z.presheaf.stalk x ⟶ CommRingCat.of (OO p) :=
    CommRingCat.ofHom (χ.comp (M.stalkEquiv x).toRingHom)
  haveI : IsLocalHom χ'.hom := by
    refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit (M.stalkEquiv x a) := isUnit_of_map_unit χ _ ha
    exact (MulEquiv.isUnit_map (M.stalkEquiv x).toMulEquiv).1 h1
  set y : Sp (OO p) ⟶ M.Z := Spec.map χ' ≫ M.Z.fromSpecStalk x with hy
  have hc : y (cPt p) = x := by
    rw [hy, Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have key : ∀ h : y (cPt p) ⤳ x, M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y = χ' := by
    intro h
    refine TopCat.Presheaf.stalk_hom_ext _ fun W hxW => ?_
    rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk χ' W _
  refine ⟨y, hc, fun a => ?_⟩
  rw [RatModel.val_gPt hc a]
  change (((M.Z.presheaf.stalkSpecializes _ ≫ Scheme.stalkClosedPointTo y).hom
    ((M.stalkEquiv x).symm a) : OO p) : PadicAlgCl p) = _
  rw [key]
  exact congrArg (fun b => ((χ b : OO p) : PadicAlgCl p)) ((M.stalkEquiv x).apply_symm_apply a)

/- English proof (translation)
Take `⟨V, hV, hxV, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial`. Take `⟨w, hwU, hwV⟩` from `M.nonempty_inf hU ⟨x, hxV⟩`. Take `⟨t, htU, hwt⟩` from `hV.exists_basicOpen_le (V := U) ⟨w, hwU⟩ hwV`. Establish `ht0 : valF M.pt V t ≠ 0` using `((RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hwV t).2 hwt)).1`. Use `⟨⟨valF M.pt V t, RatModel.valF_mem_O hxV t⟩, fun h => ht0 (congrArg Subtype.val h), ?_⟩` and prove the remaining obligations.

Introduce `p _ χ hχ hs`. Take `⟨y, hc, hval⟩` from `exists_point_of_isLocalHom M x χ`. Use `⟨y, ⟨hc, ?_⟩, hval⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w', rfl⟩`. Establish `hz : (gPt p ≫ y) w' ∈ V` using `(RatModel.gPt_specializes hc w').mem_open V.isOpen hxV`.

Establish `hne : M.val (gPt p ≫ y) (valF M.pt V t) ≠ 0`. Establish `e` using `hval ⟨valF M.pt V t, RatModel.valF_mem_O hxV t⟩`. Rewrite using `[e]`. Introduce `h0`. Conclude with `hs (Subtype.ext h0)`.

Establish `hu` using `(RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ w') ⟨valF M.pt V t, RatModel.valF_mem_O hz t⟩).1 hne`. Conclude with `htU ((RatModel.isUnit_valF_iff hz t).1 hu)`.
-/
theorem exists_ne_zero_forall_exists_cen (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) (x : M.Z) :
    ∃ s : M.O x, s ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime] (χ : M.O x →+* OO p), IsLocalHom χ → χ s ≠ 0 →
      ∃ y : Sp (OO p) ⟶ M.Z, M.Cen U x y ∧ ∀ a : M.O x, M.val (gPt p ≫ y) a = ((χ a : OO p) : PadicAlgCl p) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  obtain ⟨w, hwU, hwV⟩ := M.nonempty_inf hU ⟨x, hxV⟩
  obtain ⟨t, htU, hwt⟩ := hV.exists_basicOpen_le (V := U) ⟨w, hwU⟩ hwV
  have ht0 : valF M.pt V t ≠ 0 :=
    ((RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hwV t).2 hwt)).1
  refine ⟨⟨valF M.pt V t, RatModel.valF_mem_O hxV t⟩, fun h => ht0 (congrArg Subtype.val h), ?_⟩
  intro p _ χ hχ hs
  obtain ⟨y, hc, hval⟩ := exists_point_of_isLocalHom M x χ
  refine ⟨y, ⟨hc, ?_⟩, hval⟩
  rintro _ ⟨w', rfl⟩
  have hz : (gPt p ≫ y) w' ∈ V := (RatModel.gPt_specializes hc w').mem_open V.isOpen hxV
  have hne : M.val (gPt p ≫ y) (valF M.pt V t) ≠ 0 := by
    have e := hval ⟨valF M.pt V t, RatModel.valF_mem_O hxV t⟩
    rw [e]
    intro h0
    exact hs (Subtype.ext h0)
  have hu := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ w')
    ⟨valF M.pt V t, RatModel.valF_mem_O hz t⟩).1 hne
  exact htU ((RatModel.isUnit_valF_iff hz t).1 hu)

end GlobalTheory.Izumi
