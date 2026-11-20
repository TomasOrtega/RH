import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNowhereZeroSectionNearOfFlatTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocusStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocalTriv

/- English proof (translation)
Introduce `Y V hV hLN hY U hU`. Establish `hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp Γ(Y, V))` using `fun p => by`. Set `e` to `(asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv`. Take `⟨h1, h2⟩` from `hY (hV.fromSpec p)`. Use `haveI := h1`.

Use `haveI := h2`. Use `haveI : IsDomain ((Sp Γ(Y, V)).presheaf.stalk p) := MulEquiv.isDomain _ e.symm.toMulEquiv`. Conclude with `⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩`. Establish `hb` using `((GlobalTheory.extension_over_codim_two (Sp Γ(Y, V)) hN).1 U fun p hp => hU p (by`. Set `e` to `(asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv`.

Conclude with `(ringKrullDim_eq_of_ringEquiv e).trans_le hp)).1 ⊤`. Establish `key : ∀ (V' : (Sp Γ(Y, V)).Opens) (_ : V' = U) (h' : V' ≤ ⊤), Function.Bijective (resG (Sp Γ(Y, V)) h') → Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom`. Introduce and unpack `_ rfl _ h`. Conclude with `h`. Conclude with `key _ (top_inf_eq U) _ hb`.
-/
theorem hartogs_chart : ∀ (Y : Scheme.{0}) (V : Y.Opens) (hV : IsAffineOpen V), IsLocallyNoetherian (Sp Γ(Y, V)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ U : (Sp Γ(Y, V)).Opens, (∀ p : Sp Γ(Y, V), ringKrullDim (Y.presheaf.stalk (hV.fromSpec p)) ≤ 1 → p ∈ U) → Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
  intro Y V hV hLN hY U hU
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp Γ(Y, V)) := fun p => by
    let e := (asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    obtain ⟨h1, h2⟩ := hY (hV.fromSpec p)
    haveI := h1
    haveI := h2
    haveI : IsDomain ((Sp Γ(Y, V)).presheaf.stalk p) := MulEquiv.isDomain _ e.symm.toMulEquiv
    exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩
  have hb := ((GlobalTheory.extension_over_codim_two (Sp Γ(Y, V)) hN).1 U fun p hp => hU p (by
    let e := (asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    exact (ringKrullDim_eq_of_ringEquiv e).trans_le hp)).1 ⊤
  have key : ∀ (V' : (Sp Γ(Y, V)).Opens) (_ : V' = U) (h' : V' ≤ ⊤),
      Function.Bijective (resG (Sp Γ(Y, V)) h') →
        Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
    rintro _ rfl _ h
    exact h
  exact key _ (top_inf_eq U) _ hb

/- English proof (translation)
Introduce `X T W c j _ V hV N hN`. Establish `hz : ∀ z : (N ⊓ W).toScheme, ∃ z' ∈ V, (j ∣_ W) z' = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z`. Introduce `z`. Take `⟨z', hz'V, hz'⟩` from `hN ((N ⊓ W).ι z) z.2`. Use `⟨z', hz'V, W.ι.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations.

Establish `e1 : W.ι ((j ∣_ W) z') = j ((j ⁻¹ᵁ W).ι z')` using `congrArg (fun f => f.base z') (morphismRestrict_ι j W)`. Establish `e2 : W.ι (X.homOfLE (inf_le_right : N ⊓ W ≤ W) z) = (N ⊓ W).ι z` using `congrArg (fun f => f.base z) (X.homOfLE_ι (inf_le_right : N ⊓ W ≤ W))`. Conclude with `e1.trans (hz'.trans e2.symm)`. Set `k` to `IsOpenImmersion.lift (j ∣_ W) (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) (by`. Introduce and unpack `_ ⟨z, rfl⟩`.

Take `⟨z', -, h⟩` from `hz z`. Conclude with `⟨z', h⟩)`. Establish `hk : k ≫ (j ∣_ W) = X.homOfLE (inf_le_right : N ⊓ W ≤ W)` using `IsOpenImmersion.lift_fac _ _ _`. Rewrite using `[← hk, pull_comp]`. Use `GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.2 _ _ k _ V hV fun z => ?_` and prove the remaining obligations.

Take `⟨z', hz'V, h⟩` from `hz z`. Establish `hkz : k z = z'` using `(j ∣_ W).isOpenEmbedding.injective (by`. Establish `e : (j ∣_ W) (k z) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z` using `congrArg (fun f => f.base z) hk`. Conclude with `e.trans h.symm)`. Rewrite using `[hkz]`.

Conclude with `hz'V`.
-/
theorem factor_locus : ∀ (X T : Scheme.{0}) (W : X.Opens) (c : Pic W.toScheme) (j : T ⟶ X) [IsOpenImmersion j] (V : (j ⁻¹ᵁ W).toScheme.Opens), IsLocus (GlobalTheory.CechPic.pull (j ∣_ W) c) V → ∀ N : X.Opens, (∀ w ∈ N ⊓ W, ∃ z ∈ V, j ((j ⁻¹ᵁ W).ι z) = w) → GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  intro X T W c j _ V hV N hN
  have hz : ∀ z : (N ⊓ W).toScheme, ∃ z' ∈ V, (j ∣_ W) z' = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z := by
    intro z
    obtain ⟨z', hz'V, hz'⟩ := hN ((N ⊓ W).ι z) z.2
    refine ⟨z', hz'V, W.ι.isOpenEmbedding.injective ?_⟩
    have e1 : W.ι ((j ∣_ W) z') = j ((j ⁻¹ᵁ W).ι z') :=
      congrArg (fun f => f.base z') (morphismRestrict_ι j W)
    have e2 : W.ι (X.homOfLE (inf_le_right : N ⊓ W ≤ W) z) = (N ⊓ W).ι z :=
      congrArg (fun f => f.base z) (X.homOfLE_ι (inf_le_right : N ⊓ W ≤ W))
    exact e1.trans (hz'.trans e2.symm)
  let k := IsOpenImmersion.lift (j ∣_ W) (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) (by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z', -, h⟩ := hz z
    exact ⟨z', h⟩)
  have hk : k ≫ (j ∣_ W) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) := IsOpenImmersion.lift_fac _ _ _
  rw [← hk, pull_comp]
  refine GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.2 _ _ k _ V hV fun z => ?_
  obtain ⟨z', hz'V, h⟩ := hz z
  have hkz : k z = z' := (j ∣_ W).isOpenEmbedding.injective (by
    have e : (j ∣_ W) (k z) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z := congrArg (fun f => f.base z) hk
    exact e.trans h.symm)
  rw [hkz]
  exact hz'V

/- English proof (translation)
Introduce `X Y _ q _ _ hY W hW c hc x`. Take `⟨y, rfl⟩` from `q.surjective x`. Take `⟨N0, hN0, hx0, -⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show q y ∈ (⊤ : X.Opens) from trivial)`. Take `⟨N1, hN1, hy1, hle⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show y ∈ q ⁻¹ᵁ N0 from hx0)`. Establish `hA0 : IsAffineOpen N0` using `hN0`.

Establish `hA1 : IsAffineOpen N1` using `hN1`. Establish `hB : IsNoetherianRing Γ(X, N0)` using `IsLocallyNoetherian.component_noetherian ⟨N0, hN0⟩`. Set `g : Γ(X, N0) →+* Γ(Y, N1)` to `(q.appLE N0 N1 hle).hom`. Establish `hg : g.Flat` using `HasRingHomProperty.appLE @Flat q inferInstance ⟨N0, hN0⟩ ⟨N1, hN1⟩ hle`. Establish `hsq : spMap g ≫ hA0.fromSpec = hA1.fromSpec ≫ q` using `IsAffineOpen.SpecMap_appLE_fromSpec q hA0 hA1 hle`.

Establish `hpt : ∀ p, hA0.fromSpec (spMap g p) = q (hA1.fromSpec p)` using `fun p => by`. Use `congrArg (fun f => f.base p) hsq` as an intermediate fact. Simplify using `using this`. Establish `hLN : IsLocallyNoetherian (Sp Γ(Y, N1))` using `LocallyOfFiniteType.isLocallyNoetherian (hA1.fromSpec ≫ q)`. Set `W0 : (Sp Γ(X, N0)).Opens` to `hA0.fromSpec ⁻¹ᵁ W`.

Establish `hbij` using `hartogs_chart Y N1 hA1 hLN hY (spMap g ⁻¹ᵁ W0) fun p hp => by show hA0.fromSpec (spMap g p) ∈ W`. Rewrite using `[hpt]`. Conclude with `hW _ hp`. Take `⟨L, hL, rfl⟩` from `cls_surj c`. Set `M` to `L.pull (hA0.fromSpec ∣_ W)`.

Establish `hM : M.IsLB` using `pull_isLB hL _`. Establish `hk : spMap g ⁻¹ᵁ W0 ≤ hA1.fromSpec ⁻¹ᵁ (q ⁻¹ᵁ W)` using `fun p hp => by show q (hA1.fromSpec p) ∈ W`. Rewrite using `[← hpt]`. Conclude with `hp`. Establish `hcomp : (spMap g ∣_ W0) ≫ (hA0.fromSpec ∣_ W) = hA1.fromSpec.resLE (q ⁻¹ᵁ W) _ hk ≫ (q ∣_ W)`.

Rewrite using `[← cancel_mono W.ι]`. Simplify using `only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]`. Conclude with `(morphismRestrict_ι_assoc (spMap g) W0 hA0.fromSpec).trans (congrArg _ hsq)`. Establish `htriv : Triv (M.pull (spMap g ∣_ W0))`. Establish `h0 : cls _ (pull_isLB hM (spMap g ∣_ W0)) = 0`.

Rewrite using `[cls_pull hM, cls_pull hL, ← pull_comp, hcomp, pull_comp, hc, map_zero]`. Conclude with `(cls_eq_zero_iff _).1 h0`. Take `⟨y1, rfl⟩ : y ∈ Set.range hA1.fromSpec` from `hA1.range_fromSpec ▸ hy1`. Take `⟨s, D, hyD, hD⟩` from `GlobalTheory.T.exists_nowhereZero_section_near_of_flat_trivial Γ(X, N0) Γ(Y, N1) g hg W0 hbij M hM htriv y1`. Set `N : X.Opens` to `⟨q '' (hA1.fromSpec '' D), q.isOpenMap _ (hA1.fromSpec.isOpenEmbedding.isOpenMap _ D.isOpen)⟩`.

Use `⟨N, ⟨_, ⟨y1, hyD, rfl⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Use `factor_locus X _ W _ hA0.fromSpec (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) ⟨M, hM, s, cls_pull hL _ hM, rfl⟩ N ?_` and prove the remaining obligations. Introduce and unpack `w ⟨⟨_, ⟨d, hd, rfl⟩, rfl⟩, hwW⟩`. Establish `hdW : d ∈ spMap g ⁻¹ᵁ W0` using `by show hA0.fromSpec (spMap g d) ∈ W`. Rewrite using `[hpt]`.

Conclude with `hwW`. Use `⟨(spMap g ∣_ W0) ⟨d, hdW⟩, hD ⟨d, hdW⟩ hd, ?_⟩` and prove the remaining obligations. Establish `e : W0.ι ((spMap g ∣_ W0) ⟨d, hdW⟩) = spMap g d` using `congrArg (fun f => f.base ⟨d, hdW⟩) (morphismRestrict_ι (spMap g) W0)`. Conclude with `(congrArg hA0.fromSpec.base e).trans (hpt d)`.
-/
theorem locally_trivial : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) [Smooth q] [Surjective q], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ W : X.Opens, (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (q ∣_ W) c = 0 → ∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  intro X Y _ q _ _ hY W hW c hc x
  obtain ⟨y, rfl⟩ := q.surjective x
  obtain ⟨N0, hN0, hx0, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show q y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨N1, hN1, hy1, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ q ⁻¹ᵁ N0 from hx0)
  have hA0 : IsAffineOpen N0 := hN0
  have hA1 : IsAffineOpen N1 := hN1
  have hB : IsNoetherianRing Γ(X, N0) := IsLocallyNoetherian.component_noetherian ⟨N0, hN0⟩
  let g : Γ(X, N0) →+* Γ(Y, N1) := (q.appLE N0 N1 hle).hom
  have hg : g.Flat := HasRingHomProperty.appLE @Flat q inferInstance ⟨N0, hN0⟩ ⟨N1, hN1⟩ hle
  have hsq : spMap g ≫ hA0.fromSpec = hA1.fromSpec ≫ q := IsAffineOpen.SpecMap_appLE_fromSpec q hA0 hA1 hle
  have hpt : ∀ p, hA0.fromSpec (spMap g p) = q (hA1.fromSpec p) := fun p => by
    have := congrArg (fun f => f.base p) hsq
    simpa using this
  have hLN : IsLocallyNoetherian (Sp Γ(Y, N1)) := LocallyOfFiniteType.isLocallyNoetherian (hA1.fromSpec ≫ q)
  let W0 : (Sp Γ(X, N0)).Opens := hA0.fromSpec ⁻¹ᵁ W
  have hbij := hartogs_chart Y N1 hA1 hLN hY (spMap g ⁻¹ᵁ W0) fun p hp => by
    show hA0.fromSpec (spMap g p) ∈ W
    rw [hpt]
    exact hW _ hp
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  let M := L.pull (hA0.fromSpec ∣_ W)
  have hM : M.IsLB := pull_isLB hL _
  have hk : spMap g ⁻¹ᵁ W0 ≤ hA1.fromSpec ⁻¹ᵁ (q ⁻¹ᵁ W) := fun p hp => by
    show q (hA1.fromSpec p) ∈ W
    rw [← hpt]
    exact hp
  have hcomp : (spMap g ∣_ W0) ≫ (hA0.fromSpec ∣_ W) = hA1.fromSpec.resLE (q ⁻¹ᵁ W) _ hk ≫ (q ∣_ W) := by
    rw [← cancel_mono W.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]
    exact (morphismRestrict_ι_assoc (spMap g) W0 hA0.fromSpec).trans (congrArg _ hsq)
  have htriv : Triv (M.pull (spMap g ∣_ W0)) := by
    have h0 : cls _ (pull_isLB hM (spMap g ∣_ W0)) = 0 := by
      rw [cls_pull hM, cls_pull hL, ← pull_comp, hcomp, pull_comp, hc, map_zero]
    exact (cls_eq_zero_iff _).1 h0
  obtain ⟨y1, rfl⟩ : y ∈ Set.range hA1.fromSpec := hA1.range_fromSpec ▸ hy1
  obtain ⟨s, D, hyD, hD⟩ := GlobalTheory.T.exists_nowhereZero_section_near_of_flat_trivial Γ(X, N0) Γ(Y, N1) g hg W0 hbij M hM htriv y1
  let N : X.Opens := ⟨q '' (hA1.fromSpec '' D), q.isOpenMap _ (hA1.fromSpec.isOpenEmbedding.isOpenMap _ D.isOpen)⟩
  refine ⟨N, ⟨_, ⟨y1, hyD, rfl⟩, rfl⟩, ?_⟩
  refine factor_locus X _ W _ hA0.fromSpec (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) ⟨M, hM, s, cls_pull hL _ hM, rfl⟩ N ?_
  rintro w ⟨⟨_, ⟨d, hd, rfl⟩, rfl⟩, hwW⟩
  have hdW : d ∈ spMap g ⁻¹ᵁ W0 := by
    show hA0.fromSpec (spMap g d) ∈ W
    rw [hpt]
    exact hwW
  refine ⟨(spMap g ∣_ W0) ⟨d, hdW⟩, hD ⟨d, hdW⟩ hd, ?_⟩
  have e : W0.ι ((spMap g ∣_ W0) ⟨d, hdW⟩) = spMap g d :=
    congrArg (fun f => f.base ⟨d, hdW⟩) (morphismRestrict_ι (spMap g) W0)
  exact (congrArg hA0.fromSpec.base e).trans (hpt d)

end GlobalTheory.LocalTriv
