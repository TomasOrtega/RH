import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical
open CategoryTheory.Limits

namespace GlobalTheory.LatChain.ProjDom

/- English proof (translation)
Establish `H₀` using `V.pb`. Use `V.ar.isLocallyNoetherian` as an intermediate fact. Establish `: IsProper V.p` using `CommonModel.isProper_of_isProjOver V.ar.isProjOver`. Establish `: IsProper s` using `CommonModel.isProper_of_isProjOver hs`. Set `r` to `pullback.fst V.p s`.

Establish `hc : V.j ≫ V.p = h ≫ s` using `hhs.symm`. Set `l : V.G ⟶ pullback V.p s` to `pullback.lift V.j h hc`. Establish `hr : l ≫ r = V.j` using `pullback.lift_fst _ _ _`. Establish `hr' : l ≫ pullback.snd V.p s = h` using `pullback.lift_snd _ _ _`. Establish `hW : IsProjOver (r ≫ V.p)` using `GlobalTheory.ProjSpace.isProjOver_pullback V.ar.isProjOver hs`.

Establish `w : l ≫ r ≫ V.p = (V.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F)`. Rewrite using `[← Category.assoc, hr, H₀.w]`. Establish `hb` using `IsPullback.of_hasPullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F))`. Set `f' : V.G ⟶ pullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F))` to `pullback.lift l (V.π ≫ Y.str) w`. Set `ρ : pullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F)) ⟶ V.G` to `H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)`.

Establish `hρ : ρ ≫ V.π ≫ Y.str = pullback.snd _ _` using `H₀.lift_snd _ _ _`. Establish `hfρ : f' ≫ ρ = 𝟙 V.G`. Apply `H₀.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]`. Rewrite using `[Category.assoc, hρ, pullback.lift_snd, Category.id_comp]`.

Establish `: IsSeparated (ρ ≫ V.π ≫ Y.str)` using `by rw [hρ]; infer_instance`. Establish `: IsSeparated ρ` using `IsSeparated.of_comp ρ (V.π ≫ Y.str)`. Establish `: IsClosedImmersion (f' ≫ ρ)` using `by rw [hfρ]; infer_instance`. Establish `: IsClosedImmersion f'` using `IsClosedImmersion.of_comp f' ρ`. Establish `hh : l = f' ≫ 𝟙 _ ≫ pullback.fst _ _` using `by rw [Category.id_comp, pullback.lift_fst]`.

Establish `: IsAffineHom (pullback.fst (r ≫ V.p) (spMap (algebraMap (𝓞 F) F)))` using `MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)`. Establish `: IsAffineHom l` using `by rw [hh]; infer_instance`. Establish `hpb` using `GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) l hh`. Rewrite `hpb` using `[Category.id_comp]`. Establish `hfin : IsFinite l.fromNormalization` using `GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) l (r ≫ V.p) F (V.π ≫ Y.str) w`.

Establish `: GlobalTheory.IsNormalScheme V.G` using `GlobalTheory.Mean4O.CoverDom.isNormalScheme_G V`. Establish `: GlobalTheory.IsNormalScheme l.normalization` using `GlobalTheory.IsNormalScheme.normalization_of_isIntegral l`. Establish `hint : IsIntegral l.normalization` using `inferInstance`. Establish `: Flat (spMap (algebraMap (𝓞 F) F))` using `flat_specMap_localization (nonZeroDivisors (𝓞 F)) F`. Establish `: IsPreimmersion (spMap (algebraMap (𝓞 F) F))` using `IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))`.

Establish `: Flat V.j` using `MorphismProperty.of_isPullback V.pb.flip ‹_›`. Establish `: IsPreimmersion V.j` using `MorphismProperty.of_isPullback V.pb.flip ‹_›`. Establish `e₁ : l.toNormalization ≫ l.fromNormalization ≫ r = V.j`. Rewrite using `[← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]`. Establish `e₂ : l.toNormalization ≫ l.fromNormalization ≫ pullback.snd V.p s = h`.

Rewrite using `[← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']`. Establish `hU` using `ModelDom.exists_isIso_restrict l.toNormalization (l.fromNormalization ≫ r) V.j e₁`. Establish `hdim : topologicalKrullDim l.normalization = (Y.dim + 1 : ℕ)`. Take `⟨U, hne, _⟩` from `hU`. Take `⟨_, _⟩` from `birational_of_isIso_morphismRestrict (l.fromNormalization ≫ r) U hne.to_subtype`.

Use `surjective_of_isDominant_of_isClosed_range (l.fromNormalization ≫ r) (l.fromNormalization ≫ r).isClosedMap.isClosed_range` as an intermediate fact. Rewrite using `[← V.ar.dim_eq]`. Conclude with `(ModelDom.dim_le_of_birational (l.fromNormalization ≫ r)).antisymm (PosBaseChange.dim_le_of_isClosedMap (l.fromNormalization ≫ r).isClosedMap (l.fromNormalization ≫ r).surjective)`. Establish `hfl : Flat (l.fromNormalization ≫ r ≫ V.p)` using `GlobalTheory.flat_fromNormalization_comp l F (r ≫ V.p) (V.π ≫ Y.str) w`. Establish `hfZ : Flat (spMap (Int.castRingHom (𝓞 F)))`.

Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))`. Establish `hpb'` using `hpb.paste_vert hb`. Rewrite `hpb'` using `[pullback.lift_snd]`. Set `V' : Cover Y` to `{ X := l.normalization p := l.fromNormalization ≫ r ≫ V.p ar := ⟨V.ar.isDomain, V.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩ normal := GlobalTheory.IsNormalScheme.pred _ G := V.G j := l.toNormalization π := V.π pb := hpb' φ := …`.

Use `⟨V', l.fromNormalization ≫ pullback.snd V.p s, 𝟙 V.G, ?_, ?_, Category.id_comp _⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(l.fromNormalization ≫ pullback.snd V.p s) ≫ s = l.fromNormalization ≫ r ≫ V.p`. Rewrite using `[Category.assoc, ← pullback.condition]`. Express the relevant statement in the definitionally equal form `l.toNormalization ≫ l.fromNormalization ≫ pullback.snd V.p s = 𝟙 V.G ≫ h`. Rewrite using `[e₂, Category.id_comp]`.
-/
theorem exists_cover_dominating_proj (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (Z : Scheme.{0})
    (s : Z ⟶ Sp (𝓞 F)) (h : V.G ⟶ Z) (hs : IsProjOver s) (hhs : h ≫ s = V.j ≫ V.p) :
    ∃ (V' : Cover Y) (ν : V'.X ⟶ Z) (g : V'.G ⟶ V.G), ν ≫ s = V'.p ∧ V'.j ≫ ν = g ≫ h ∧ g ≫ V.π = V'.π := by
  have H₀ := V.pb
  have := V.ar.isLocallyNoetherian
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  have : IsProper s := CommonModel.isProper_of_isProjOver hs
  let r := pullback.fst V.p s
  have hc : V.j ≫ V.p = h ≫ s := hhs.symm
  let l : V.G ⟶ pullback V.p s := pullback.lift V.j h hc
  have hr : l ≫ r = V.j := pullback.lift_fst _ _ _
  have hr' : l ≫ pullback.snd V.p s = h := pullback.lift_snd _ _ _
  have hW : IsProjOver (r ≫ V.p) := GlobalTheory.ProjSpace.isProjOver_pullback V.ar.isProjOver hs
  have w : l ≫ r ≫ V.p = (V.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← Category.assoc, hr, H₀.w]
  have hb := IsPullback.of_hasPullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F))
  let f' : V.G ⟶ pullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F)) := pullback.lift l (V.π ≫ Y.str) w
  let ρ : pullback (r ≫ V.p) (spMap (algebraMap (𝓞 F) F)) ⟶ V.G :=
    H₀.lift (pullback.fst _ _ ≫ r) (pullback.snd _ _) (by rw [Category.assoc]; exact hb.w)
  have hρ : ρ ≫ V.π ≫ Y.str = pullback.snd _ _ := H₀.lift_snd _ _ _
  have hfρ : f' ≫ ρ = 𝟙 V.G := by
    apply H₀.hom_ext
    · rw [Category.assoc, H₀.lift_fst, pullback.lift_fst_assoc, hr, Category.id_comp]
    · rw [Category.assoc, hρ, pullback.lift_snd, Category.id_comp]
  have : IsSeparated (ρ ≫ V.π ≫ Y.str) := by rw [hρ]; infer_instance
  have : IsSeparated ρ := IsSeparated.of_comp ρ (V.π ≫ Y.str)
  have : IsClosedImmersion (f' ≫ ρ) := by rw [hfρ]; infer_instance
  have : IsClosedImmersion f' := IsClosedImmersion.of_comp f' ρ
  have hh : l = f' ≫ 𝟙 _ ≫ pullback.fst _ _ := by rw [Category.id_comp, pullback.lift_fst]
  have : IsAffineHom (pullback.fst (r ≫ V.p) (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback hb.flip (isAffineHom_of_isAffine _)
  have : IsAffineHom l := by rw [hh]; infer_instance
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) hb f' (𝟙 _) l hh
  rw [Category.id_comp] at hpb
  have hfin : IsFinite l.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) l (r ≫ V.p) F (V.π ≫ Y.str) w
  have : GlobalTheory.IsNormalScheme V.G := GlobalTheory.Mean4O.CoverDom.isNormalScheme_G V
  have : GlobalTheory.IsNormalScheme l.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral l
  have hint : IsIntegral l.normalization := inferInstance
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have : IsPreimmersion V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  have e₁ : l.toNormalization ≫ l.fromNormalization ≫ r = V.j := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr]
  have e₂ : l.toNormalization ≫ l.fromNormalization ≫ pullback.snd V.p s = h := by
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hr']
  have hU := ModelDom.exists_isIso_restrict l.toNormalization (l.fromNormalization ≫ r) V.j e₁
  have hdim : topologicalKrullDim l.normalization = (Y.dim + 1 : ℕ) := by
    obtain ⟨U, hne, _⟩ := hU
    obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict (l.fromNormalization ≫ r) U hne.to_subtype
    have := surjective_of_isDominant_of_isClosed_range (l.fromNormalization ≫ r)
      (l.fromNormalization ≫ r).isClosedMap.isClosed_range
    rw [← V.ar.dim_eq]
    exact (ModelDom.dim_le_of_birational (l.fromNormalization ≫ r)).antisymm
      (PosBaseChange.dim_le_of_isClosedMap (l.fromNormalization ≫ r).isClosedMap
        (l.fromNormalization ≫ r).surjective)
  have hfl : Flat (l.fromNormalization ≫ r ≫ V.p) := GlobalTheory.flat_fromNormalization_comp l F (r ≫ V.p) (V.π ≫ Y.str) w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have hpb' := hpb.paste_vert hb
  rw [pullback.lift_snd] at hpb'
  let V' : Cover Y :=
    { X := l.normalization
      p := l.fromNormalization ≫ r ≫ V.p
      ar := ⟨V.ar.isDomain, V.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin hW, inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := V.G
      j := l.toNormalization
      π := V.π
      pb := hpb'
      φ := V.φ
      φ_spec := V.φ_spec }
  refine ⟨V', l.fromNormalization ≫ pullback.snd V.p s, 𝟙 V.G, ?_, ?_, Category.id_comp _⟩
  · change (l.fromNormalization ≫ pullback.snd V.p s) ≫ s = l.fromNormalization ≫ r ≫ V.p
    rw [Category.assoc, ← pullback.condition]
  · change l.toNormalization ≫ l.fromNormalization ≫ pullback.snd V.p s = 𝟙 V.G ≫ h
    rw [e₂, Category.id_comp]

end GlobalTheory.LatChain.ProjDom

end
