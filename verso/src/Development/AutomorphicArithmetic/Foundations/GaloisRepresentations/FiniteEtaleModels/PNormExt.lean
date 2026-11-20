import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOverNormalQuasiProjectiveBase

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

/- English proof (translation)
Establish `hG : IsIrreducible {y : S | y ⤳ x}`. Rewrite using `[← Scheme.range_fromSpecStalk]`. Use `haveI := hd x`. Simplify `(IrreducibleSpace.isIrreducible_univ _).image _ (S.fromSpecStalk x).continuous.continuousOn` using `[Set.image_univ]`. Take `⟨N, hN, hxN, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens) (show x ∈ (⊤ : S.Opens) from trivial)`.

Use `haveI : IsNoetherianRing Γ(S, N) := IsLocallyNoetherian.component_noetherian ⟨N, hN⟩`. Use `haveI : TopologicalSpace.NoetherianSpace N := noetherianSpace_of_isAffineOpen N hN`. Set `x' : N` to `⟨x, hxN⟩`. Set `C : Set (Set N)` to `{Z | Z ∈ irreducibleComponents N ∧ x' ∉ Z}`. Establish `hCfin : C.Finite` using `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)`.

Set `O : Set N` to `(⋃₀ C)ᶜ`. Establish `hO : IsOpen O`. Use `isOpen_compl_iff.mpr ?_` and prove the remaining obligations. Rewrite using `[Set.sUnion_eq_biUnion]`. Conclude with `hCfin.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)`.

Establish `hxO : x' ∈ O` using `fun ⟨Z, hZ, hxZ⟩ => hZ.2 hxZ`. Set `O' : Set S` to `Subtype.val '' O`. Establish `hO' : IsOpen O'` using `N.isOpen.isOpenMap_subtype_val O hO`. Establish `hsub : O' ⊆ closure {y : S | y ⤳ x}`. Introduce and unpack `_ ⟨y, hyO, rfl⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨Z, hZ, hyZ⟩ : ∃ Z ∈ irreducibleComponents N, y ∈ Z := by`. Establish `h` using `Set.mem_univ y`. Rewrite `h` using `[← sUnion_irreducibleComponents]`. Take `⟨Z, hZ, hyZ⟩` from `h`. Conclude with `⟨Z, hZ, hyZ⟩`.

Establish `hxZ : x' ∈ Z`. Assume the negation of the conclusion as `h`. Conclude with `hyO ⟨Z, ⟨hZ, h⟩, hyZ⟩`. Establish `hT : IsIrreducible (Subtype.val '' Z)` using `hZ.1.image _ continuous_subtype_val.continuousOn`. Establish `hgen` using `hT.isGenericPoint_genericPoint_closure`.

Establish `h1 : hT.genericPoint ⤳ x` using `hgen.specializes (subset_closure ⟨x', hxZ, rfl⟩)`. Establish `h2 : (y : S) ∈ closure {hT.genericPoint}` using `specializes_iff_mem_closure.mp (hgen.specializes (subset_closure ⟨y, hyZ, rfl⟩))`. Conclude with `closure_mono (Set.singleton_subset_iff.mpr h1) h2`. Take `⟨V, hV, hxV, hVO⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens) (show x ∈ (⟨O', hO'⟩ : S.Opens) from ⟨x', hxO, rfl⟩)`. Conclude with `⟨V, hV, hxV, ⟨x, hxV⟩, hG.closure.2.open_subset V.isOpen (fun z hz => hsub (hVO hz))⟩`.
-/
private theorem exists_affine_irreducible_open_nhd (S : Scheme) [IsLocallyNoetherian S]
    (hd : ∀ x : S, IsDomain (S.presheaf.stalk x)) (x : S) :
    ∃ V : S.Opens, IsAffineOpen V ∧ x ∈ V ∧ IsIrreducible (V : Set S) := by
  have hG : IsIrreducible {y : S | y ⤳ x} := by
    rw [← Scheme.range_fromSpecStalk]
    haveI := hd x
    simpa [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ _).image _ (S.fromSpecStalk x).continuous.continuousOn
  obtain ⟨N, hN, hxN, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show x ∈ (⊤ : S.Opens) from trivial)
  haveI : IsNoetherianRing Γ(S, N) := IsLocallyNoetherian.component_noetherian ⟨N, hN⟩
  haveI : TopologicalSpace.NoetherianSpace N := noetherianSpace_of_isAffineOpen N hN
  let x' : N := ⟨x, hxN⟩
  let C : Set (Set N) := {Z | Z ∈ irreducibleComponents N ∧ x' ∉ Z}
  have hCfin : C.Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (fun Z hZ => hZ.1)
  let O : Set N := (⋃₀ C)ᶜ
  have hO : IsOpen O := by
    refine isOpen_compl_iff.mpr ?_
    rw [Set.sUnion_eq_biUnion]
    exact hCfin.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)
  have hxO : x' ∈ O := fun ⟨Z, hZ, hxZ⟩ => hZ.2 hxZ
  let O' : Set S := Subtype.val '' O
  have hO' : IsOpen O' := N.isOpen.isOpenMap_subtype_val O hO
  have hsub : O' ⊆ closure {y : S | y ⤳ x} := by
    rintro _ ⟨y, hyO, rfl⟩
    obtain ⟨Z, hZ, hyZ⟩ : ∃ Z ∈ irreducibleComponents N, y ∈ Z := by
      have h := Set.mem_univ y
      rw [← sUnion_irreducibleComponents] at h
      obtain ⟨Z, hZ, hyZ⟩ := h
      exact ⟨Z, hZ, hyZ⟩
    have hxZ : x' ∈ Z := by
      by_contra h
      exact hyO ⟨Z, ⟨hZ, h⟩, hyZ⟩
    have hT : IsIrreducible (Subtype.val '' Z) := hZ.1.image _ continuous_subtype_val.continuousOn
    have hgen := hT.isGenericPoint_genericPoint_closure
    have h1 : hT.genericPoint ⤳ x := hgen.specializes (subset_closure ⟨x', hxZ, rfl⟩)
    have h2 : (y : S) ∈ closure {hT.genericPoint} :=
      specializes_iff_mem_closure.mp (hgen.specializes (subset_closure ⟨y, hyZ, rfl⟩))
    exact closure_mono (Set.singleton_subset_iff.mpr h1) h2
  obtain ⟨V, hV, hxV, hVO⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show x ∈ (⟨O', hO'⟩ : S.Opens) from ⟨x', hxO, rfl⟩)
  exact ⟨V, hV, hxV, ⟨x, hxV⟩, hG.closure.2.open_subset V.isOpen (fun z hz => hsub (hVO hz))⟩

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `s hs`. Rewrite using `[← basicOpen_eq_bot_iff]`. Use `eq_bot_iff.mpr (fun y hy => ?_)` and prove the remaining obligations. Establish `hyW : y ∈ W` using `X.basicOpen_le s hy`.

Establish `hxb : x ∈ X.basicOpen s` using `(hgen y hyW).mem_open (X.basicOpen s).isOpen hy`. Rewrite `hxb` using `[Scheme.mem_basicOpen X s x hx]`. Rewrite `hxb` using `[hs]`. Conclude with `absurd hxb not_isUnit_zero`.
-/
private theorem injective_germ_of_generic_in_open (X : Scheme) [IsReduced X] (W : X.Opens) (x : X) (hx : x ∈ W)
    (hgen : ∀ y ∈ W, x ⤳ y) : Function.Injective (X.presheaf.germ W x hx).hom := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  rw [← basicOpen_eq_bot_iff]
  refine eq_bot_iff.mpr (fun y hy => ?_)
  have hyW : y ∈ W := X.basicOpen_le s hy
  have hxb : x ∈ X.basicOpen s := (hgen y hyW).mem_open (X.basicOpen s).isOpen hy
  rw [Scheme.mem_basicOpen X s x hx] at hxb
  rw [hs] at hxb
  exact absurd hxb not_isUnit_zero

/- English proof (translation)
Use `letI := (i.app V).hom.toAlgebra`. Use `haveI : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by haveI := hd x infer_instance`. Use `haveI : IsReduced S := isReduced_of_isReduced_stalk S`. Use `haveI : IsReduced U := isReduced_of_isOpenImmersion i`. Establish `hgen` using `hirr.isGenericPoint_genericPoint_closure`.

Establish `hηV : hirr.genericPoint ∈ V` using `(hgen.mem_open_set_iff V.isOpen).mpr ⟨hirr.1.some, subset_closure hirr.1.some_mem, hirr.1.some_mem⟩`. Establish `hsp : ∀ y ∈ V, hirr.genericPoint ⤳ y` using `fun y hy => hgen.specializes (subset_closure hy)`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : hirr.genericPoint ∈ Set.range i := by`. Take `⟨z, hzV, hzr⟩` from `i.denseRange.inter_open_nonempty V V.isOpen hirr.1`. Conclude with `(hsp z hzV).mem_open i.isOpenEmbedding.isOpen_range hzr`.

Establish `hiuV : i u ∈ V` using `hu ▸ hηV`. Establish `hspS : ∀ y ∈ V, i u ⤳ y` using `fun y hy => hu ▸ hsp y hy`. Establish `huV : u ∈ i ⁻¹ᵁ V` using `hiuV`. Establish `hspU : ∀ y ∈ i ⁻¹ᵁ V, u ⤳ y` using `fun y hy => by`. Rewrite using `[← i.isOpenEmbedding.isInducing.specializes_iff]`.

Conclude with `hspS _ hy`. Establish `hφ : i.app V ≫ (U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)) = S.presheaf.germ V (i u) hiuV`. Rewrite using `[← cancel_mono (i.stalkMap u), Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]`. Conclude with `(i.germ_stalkMap V u hiuV).symm`. Establish `hg0inj : Function.Injective (S.presheaf.germ V (i u) hiuV).hom` using `injective_germ_of_generic_in_open S V (i u) hiuV hspS`.

Establish `hφinj : Function.Injective (U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)).hom`. Establish `h1` using `injective_germ_of_generic_in_open U (i ⁻¹ᵁ V) u huV hspU`. Establish `h2 : Function.Injective (inv (i.stalkMap u)).hom` using `((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1`. Rewrite using `[CommRingCat.hom_comp, RingHom.coe_comp]`. Conclude with `h2.comp h1`.

Use `haveI : IsDomain (S.presheaf.stalk (i u)) := hd _`. Use `haveI : IsDomain Γ(S, V) := Function.Injective.isDomain _ hg0inj`. Use `letI : Algebra Γ(S, V) (S.presheaf.stalk (i u)) := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨i u, hiuV⟩ : V)`. Establish `hloc` using `hV.isLocalization_stalk ⟨i u, hiuV⟩`. Establish `hP : (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal = ⊥`.

Use `eq_bot_iff.mpr (fun a ha => ?_)` and prove the remaining obligations. Establish `hnu : ¬ IsUnit (algebraMap Γ(S, V) (S.presheaf.stalk (i u)) a)`. Rewrite using `[IsLocalization.AtPrime.isUnit_to_map_iff _ (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal]`. Conclude with `fun h => h ha`. Establish `hnot : i u ∉ S.basicOpen a`.

Rewrite using `[Scheme.mem_basicOpen S a (i u) hiuV]`. Conclude with `hnu`. Rewrite using `[Submodule.mem_bot, ← basicOpen_eq_bot_iff]`. Conclude with `eq_bot_iff.mpr (fun y hy => hnot ((hspS y (S.basicOpen_le a hy)).mem_open (S.basicOpen a).isOpen hy))`. Use `haveI hfr : IsFractionRing Γ(S, V) (S.presheaf.stalk (i u)) := by`.

Establish `e : (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal.primeCompl = nonZeroDivisors Γ(S, V)`. Use extensionality with `a`. Simplify using `[Ideal.primeCompl, hP, mem_nonZeroDivisors_iff_ne_zero]`. Unfold `IsLocalization.AtPrime at hloc`. Rewrite `hloc` using `[e]`.

Conclude with `hloc`. Use `haveI : IsIntegrallyClosed Γ(S, V) := by`. Use `IsIntegrallyClosed.of_localization_maximal ?_` and prove the remaining obligations. Introduce `p _ hpm`. Set `q : PrimeSpectrum Γ(S, V)` to `⟨p, hpm.isPrime⟩`.

Establish `hq : hV.fromSpec q ∈ V` using `by show hV.fromSpec q ∈ (V : Set S)`. Rewrite using `[← hV.range_fromSpec]`. Conclude with `⟨q, rfl⟩`. Use `letI : Algebra Γ(S, V) (S.presheaf.stalk (hV.fromSpec q)) := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨hV.fromSpec q, hq⟩ : V)`. Use `haveI : IsLocalization p.primeCompl (S.presheaf.stalk (hV.fromSpec q)) := hV.isLocalization_stalk' q hq`.

Use `haveI := hc (hV.fromSpec q)`. Conclude with `IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv p.primeCompl (S.presheaf.stalk (hV.fromSpec q)) (Localization.AtPrime p)).toRingEquiv`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Apply `hg0inj` to reduce the goal to its premises.

Establish `hab' : (i.app V).hom a = (i.app V).hom b` using `congrArg Subtype.val hab`. Rewrite using `[← hφ, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply, hab']`. Introduce and unpack `⟨t, ht⟩`. Establish `hint : IsIntegral Γ(S, V) ((U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)).hom t)`. Use `IsIntegral.map_of_comp_eq (RingHom.id _) _ ?_ ht` and prove the remaining obligations.

Use extensionality with `a`. Conclude with `(congrArg (fun f => CommRingCat.Hom.hom f a) hφ).symm`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Use `⟨r, Subtype.ext (hφinj ?_)⟩` and prove the remaining obligations. Rewrite using `[← hr]`.

Conclude with `congrArg (fun f => CommRingCat.Hom.hom f r) hφ`.
-/
private theorem normalization_affine_open_irreducible_of_normal {U S : Scheme} (i : U ⟶ S) [IsOpenImmersion i] [IsDominant i]
    (hd : ∀ x : S, IsDomain (S.presheaf.stalk x))
    (hc : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (V : S.Opens) (hV : IsAffineOpen V) (hirr : IsIrreducible (V : Set S)) :
    letI := (i.app V).hom.toAlgebra
    Function.Bijective (algebraMap Γ(S, V) (integralClosure Γ(S, V) Γ(U, i ⁻¹ᵁ V))) := by
  letI := (i.app V).hom.toAlgebra
  haveI : ∀ x : S, _root_.IsReduced (S.presheaf.stalk x) := fun x => by
    haveI := hd x
    infer_instance
  haveI : IsReduced S := isReduced_of_isReduced_stalk S
  haveI : IsReduced U := isReduced_of_isOpenImmersion i
  have hgen := hirr.isGenericPoint_genericPoint_closure
  have hηV : hirr.genericPoint ∈ V := (hgen.mem_open_set_iff V.isOpen).mpr
    ⟨hirr.1.some, subset_closure hirr.1.some_mem, hirr.1.some_mem⟩
  have hsp : ∀ y ∈ V, hirr.genericPoint ⤳ y := fun y hy => hgen.specializes (subset_closure hy)
  obtain ⟨u, hu⟩ : hirr.genericPoint ∈ Set.range i := by
    obtain ⟨z, hzV, hzr⟩ := i.denseRange.inter_open_nonempty V V.isOpen hirr.1
    exact (hsp z hzV).mem_open i.isOpenEmbedding.isOpen_range hzr
  have hiuV : i u ∈ V := hu ▸ hηV
  have hspS : ∀ y ∈ V, i u ⤳ y := fun y hy => hu ▸ hsp y hy
  have huV : u ∈ i ⁻¹ᵁ V := hiuV
  have hspU : ∀ y ∈ i ⁻¹ᵁ V, u ⤳ y := fun y hy => by
    rw [← i.isOpenEmbedding.isInducing.specializes_iff]
    exact hspS _ hy
  have hφ : i.app V ≫ (U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)) =
      S.presheaf.germ V (i u) hiuV := by
    rw [← cancel_mono (i.stalkMap u), Category.assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
    exact (i.germ_stalkMap V u hiuV).symm
  have hg0inj : Function.Injective (S.presheaf.germ V (i u) hiuV).hom :=
    injective_germ_of_generic_in_open S V (i u) hiuV hspS
  have hφinj : Function.Injective
      (U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)).hom := by
    have h1 := injective_germ_of_generic_in_open U (i ⁻¹ᵁ V) u huV hspU
    have h2 : Function.Injective (inv (i.stalkMap u)).hom :=
      ((ConcreteCategory.isIso_iff_bijective _).mp inferInstance).1
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact h2.comp h1
  haveI : IsDomain (S.presheaf.stalk (i u)) := hd _
  haveI : IsDomain Γ(S, V) := Function.Injective.isDomain _ hg0inj
  letI : Algebra Γ(S, V) (S.presheaf.stalk (i u)) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨i u, hiuV⟩ : V)
  have hloc := hV.isLocalization_stalk ⟨i u, hiuV⟩
  have hP : (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal = ⊥ := by
    refine eq_bot_iff.mpr (fun a ha => ?_)
    have hnu : ¬ IsUnit (algebraMap Γ(S, V) (S.presheaf.stalk (i u)) a) := by
      rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal]
      exact fun h => h ha
    have hnot : i u ∉ S.basicOpen a := by
      rw [Scheme.mem_basicOpen S a (i u) hiuV]
      exact hnu
    rw [Submodule.mem_bot, ← basicOpen_eq_bot_iff]
    exact eq_bot_iff.mpr (fun y hy =>
      hnot ((hspS y (S.basicOpen_le a hy)).mem_open (S.basicOpen a).isOpen hy))
  haveI hfr : IsFractionRing Γ(S, V) (S.presheaf.stalk (i u)) := by
    have e : (hV.primeIdealOf ⟨i u, hiuV⟩).asIdeal.primeCompl = nonZeroDivisors Γ(S, V) := by
      ext a
      simp [Ideal.primeCompl, hP, mem_nonZeroDivisors_iff_ne_zero]
    unfold IsLocalization.AtPrime at hloc
    rw [e] at hloc
    exact hloc
  haveI : IsIntegrallyClosed Γ(S, V) := by
    refine IsIntegrallyClosed.of_localization_maximal ?_
    intro p _ hpm
    let q : PrimeSpectrum Γ(S, V) := ⟨p, hpm.isPrime⟩
    have hq : hV.fromSpec q ∈ V := by
      show hV.fromSpec q ∈ (V : Set S)
      rw [← hV.range_fromSpec]
      exact ⟨q, rfl⟩
    letI : Algebra Γ(S, V) (S.presheaf.stalk (hV.fromSpec q)) :=
      TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨hV.fromSpec q, hq⟩ : V)
    haveI : IsLocalization p.primeCompl (S.presheaf.stalk (hV.fromSpec q)) :=
      hV.isLocalization_stalk' q hq
    haveI := hc (hV.fromSpec q)
    exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv p.primeCompl
      (S.presheaf.stalk (hV.fromSpec q)) (Localization.AtPrime p)).toRingEquiv
  constructor
  · intro a b hab
    apply hg0inj
    have hab' : (i.app V).hom a = (i.app V).hom b := congrArg Subtype.val hab
    rw [← hφ, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply, hab']
  · rintro ⟨t, ht⟩
    have hint : IsIntegral Γ(S, V)
        ((U.presheaf.germ (i ⁻¹ᵁ V) u huV ≫ inv (i.stalkMap u)).hom t) := by
      refine IsIntegral.map_of_comp_eq (RingHom.id _) _ ?_ ht
      ext a
      exact (congrArg (fun f => CommRingCat.Hom.hom f a) hφ).symm
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨r, Subtype.ext (hφinj ?_)⟩
    rw [← hr]
    exact congrArg (fun f => CommRingCat.Hom.hom f r) hφ

/- English proof (translation)
Establish `hcov : iSup (fun V : {V : S.Opens // IsAffineOpen V ∧ IsIrreducible (V : Set S)} => V.1) = ⊤`. Use `eq_top_iff.mpr (fun x _ => ?_)` and prove the remaining obligations. Take `⟨V, hV, hxV, hirr⟩` from `exists_affine_irreducible_open_nhd S hd x`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hirr⟩, hxV⟩`. Rewrite using `[← MorphismProperty.isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _ hcov]`.

Introduce and unpack `⟨V, hV, hirr⟩`. Set `W : S.AffineZariskiSite` to `⟨V, hV⟩`. Use `haveI : IsOpenImmersion (i.normalizationOpenCover.f W) := i.normalizationOpenCover.map_prop W`. Set `e` to `IsOpenImmersion.isoOfRangeEq (i.fromNormalization ⁻¹ᵁ V).ι (i.normalizationOpenCover.f W) (by`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `congr($(i.fromNormalization_preimage ⟨V, hV⟩).1))`. Rewrite using `[← MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme) e.inv, ← MorphismProperty.cancel_right_of_respectsIso (MorphismProperty.isomorphisms Scheme) _ hV.isoSpec.hom]`. Establish `hb` using `normalization_affine_open_irreducible_of_normal i hd hc V hV hirr`. Use `haveI : IsIso (i.normalizationDiagramMap.app (.op V)) := by`. Rewrite using `[ConcreteCategory.isIso_iff_bijective]`.

Conclude with `hb`. Rewrite using `[MorphismProperty.isomorphisms.iff]`. Establish `key : e.inv ≫ (i.fromNormalization ∣_ V) ≫ hV.isoSpec.hom = (Spec.map (i.normalizationDiagramMap.app (.op V)) : i.normalizationOpenCover.X W ⟶ Spec Γ(S, V))`. Use `(cancel_mono hV.fromSpec).mp ?_` and prove the remaining obligations. Simplify using `[IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]`.

Conclude with `i.ι_fromNormalization ⟨V, hV⟩`. Use `show IsIso (e.inv ≫ (i.fromNormalization ∣_ V) ≫ hV.isoSpec.hom)`. Rewrite using `[key]`. Conclude with `(inferInstance : IsIso (Spec.map (i.normalizationDiagramMap.app (.op V))))`.
-/
private theorem isIso_fromNormalization_of_normal_noetherian {U S : Scheme} (i : U ⟶ S) [IsOpenImmersion i] [IsDominant i]
    [IsLocallyNoetherian S]
    (hd : ∀ x : S, IsDomain (S.presheaf.stalk x))
    (hc : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x)) :
    IsIso i.fromNormalization := by
  have hcov : iSup (fun V : {V : S.Opens // IsAffineOpen V ∧ IsIrreducible (V : Set S)} => V.1) = ⊤ := by
    refine eq_top_iff.mpr (fun x _ => ?_)
    obtain ⟨V, hV, hxV, hirr⟩ := exists_affine_irreducible_open_nhd S hd x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hirr⟩, hxV⟩
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _ hcov]
  rintro ⟨V, hV, hirr⟩
  let W : S.AffineZariskiSite := ⟨V, hV⟩
  haveI : IsOpenImmersion (i.normalizationOpenCover.f W) := i.normalizationOpenCover.map_prop W
  let e := IsOpenImmersion.isoOfRangeEq (i.fromNormalization ⁻¹ᵁ V).ι
    (i.normalizationOpenCover.f W)
    (by
      rw [Scheme.Opens.range_ι]
      exact congr($(i.fromNormalization_preimage ⟨V, hV⟩).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme) e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso (MorphismProperty.isomorphisms Scheme) _
      hV.isoSpec.hom]
  have hb := normalization_affine_open_irreducible_of_normal i hd hc V hV hirr
  haveI : IsIso (i.normalizationDiagramMap.app (.op V)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hb
  rw [MorphismProperty.isomorphisms.iff]
  have key : e.inv ≫ (i.fromNormalization ∣_ V) ≫ hV.isoSpec.hom =
      (Spec.map (i.normalizationDiagramMap.app (.op V)) :
        i.normalizationOpenCover.X W ⟶ Spec Γ(S, V)) := by
    refine (cancel_mono hV.fromSpec).mp ?_
    simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]
    exact i.ι_fromNormalization ⟨V, hV⟩
  show IsIso (e.inv ≫ (i.fromNormalization ∣_ V) ≫ hV.isoSpec.hom)
  rw [key]
  exact (inferInstance : IsIso (Spec.map (i.normalizationDiagramMap.app (.op V))))

/- English proof (translation)
Unfold `UpperTheory.Gal.FiniteEtaleModels.NormExt`. Introduce `U S Y B i f g y hi hdom hnoeth hdst hic hfin hcomm`. Use `haveI := hi`. Use `haveI := hdom`. Use `haveI := hnoeth`.

Use `haveI := hfin`. Use `haveI : IsIso i.fromNormalization := isIso_fromNormalization_of_normal_noetherian i hdst hic`. Establish `H : i = pullback.lift y i hcomm ≫ pullback.snd g f` using `(pullback.lift_snd _ _ _).symm`. Use `⟨inv i.fromNormalization ≫ i.normalizationDesc (pullback.lift y i hcomm) (pullback.snd g f) H ≫ pullback.fst g f, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : i ≫ inv i.fromNormalization = i.toNormalization`.

Rewrite using `[IsIso.comp_inv_eq, Scheme.Hom.toNormalization_fromNormalization]`. Rewrite using `[reassoc_of% h1, Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_fst]`. Rewrite using `[Category.assoc, Category.assoc, pullback.condition, Scheme.Hom.normalizationDesc_comp_assoc, IsIso.inv_hom_id_assoc]`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.normExt_holds :
    NormExt := by
  unfold UpperTheory.Gal.FiniteEtaleModels.NormExt
  intro U S Y B i f g y hi hdom hnoeth hdst hic hfin hcomm
  haveI := hi
  haveI := hdom
  haveI := hnoeth
  haveI := hfin
  haveI : IsIso i.fromNormalization := isIso_fromNormalization_of_normal_noetherian i hdst hic
  have H : i = pullback.lift y i hcomm ≫ pullback.snd g f := (pullback.lift_snd _ _ _).symm
  refine ⟨inv i.fromNormalization ≫
    i.normalizationDesc (pullback.lift y i hcomm) (pullback.snd g f) H ≫ pullback.fst g f, ?_, ?_⟩
  · have h1 : i ≫ inv i.fromNormalization = i.toNormalization := by
      rw [IsIso.comp_inv_eq, Scheme.Hom.toNormalization_fromNormalization]
    rw [reassoc_of% h1, Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, pullback.condition,
      Scheme.Hom.normalizationDesc_comp_assoc, IsIso.inv_hom_id_assoc]
