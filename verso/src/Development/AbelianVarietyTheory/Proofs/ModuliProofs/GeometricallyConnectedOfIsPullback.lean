import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.SemiAbelianDescent

/- English proof (translation)
Establish `: IsAffine Z` using `isAffine_of_isAffineHom f`. Establish `: Nonempty Z` using `⟨(f.surjective (Nonempty.some inferInstance)).choose⟩`. Take `⟨z, -, hz⟩` from `(isClosed_univ (X := Z)).exists_closed_singleton Set.univ_nonempty`. Rewrite `hz` using `[isClosed_singleton_iff_isClosedImmersion]`. Use `set g : Spec (Z.residueField z) ⟶ Spec (CommRingCat.of Ω) := Z.fromSpecResidueField z ≫ f with hg`.

Establish `: IsIntegralHom g` using `inferInstance`. Establish `: IsIso (Spec.preimage g)`. Rewrite using `[ConcreteCategory.isIso_iff_bijective]`. Use `IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_` and prove the remaining obligations. Rewrite using `[← IsIntegralHom.SpecMap_iff, Spec.map_preimage]`.

Use `infer_instance`. Use `⟨Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Category.assoc, Spec.map_preimage]`. Use `_ = 𝟙 _ := by rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]`.
-/
theorem exists_section {Z : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (f : Z ⟶ Spec (CommRingCat.of Ω)) [IsIntegralHom f] [Surjective f] :
    ∃ s : Spec (CommRingCat.of Ω) ⟶ Z, s ≫ f = 𝟙 _ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  have : Nonempty Z := ⟨(f.surjective (Nonempty.some inferInstance)).choose⟩
  obtain ⟨z, -, hz⟩ := (isClosed_univ (X := Z)).exists_closed_singleton Set.univ_nonempty
  rw [isClosed_singleton_iff_isClosedImmersion] at hz
  set g : Spec (Z.residueField z) ⟶ Spec (CommRingCat.of Ω) := Z.fromSpecResidueField z ≫ f with hg
  have : IsIntegralHom g := inferInstance
  have : IsIso (Spec.preimage g) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  refine ⟨Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z, ?_⟩
  calc (Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z) ≫ f
      = Spec.map (inv (Spec.preimage g)) ≫ Spec.map (Spec.preimage g) := by
        rw [Category.assoc, Spec.map_preimage]
    _ = 𝟙 _ := by rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

/- English proof (translation)
Take `⟨s, hs⟩` from `exists_section (pullback.snd π p)`. Use `⟨s ≫ pullback.fst π p, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]`.
-/
theorem exists_lift {X X' : Scheme.{0}} (π : X ⟶ X') [IsIntegralHom π] [Surjective π]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ X') :
    ∃ q : Spec (CommRingCat.of Ω) ⟶ X, q ≫ π = p := by
  obtain ⟨s, hs⟩ := exists_section (pullback.snd π p)
  refine ⟨s ≫ pullback.fst π p, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

/- English proof (translation)
Establish `key : Set.range (pullback.diagonal f) = m '' Set.range d`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Take `⟨x, rfl⟩` from `j.surjective y`.

Conclude with `⟨d x, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]⟩`. Introduce and unpack `⟨_, ⟨x, rfl⟩, rfl⟩`. Conclude with `⟨j x, by rw [← Scheme.Hom.comp_apply, ← hc, Scheme.Hom.comp_apply]⟩`. Rewrite using `[key]`. Conclude with `m.isClosedMap _ hd`.
-/
private theorem isClosed_range_diagonal_of_surjective_universallyClosed {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S) [Surjective j]
    {P : Scheme.{0}} (m : P ⟶ Limits.pullback f f) [UniversallyClosed m] (d : X ⟶ P)
    (hd : IsClosed (Set.range d)) (hc : d ≫ m = j ≫ pullback.diagonal f) :
    IsClosed (Set.range (pullback.diagonal f)) := by
  have key : Set.range (pullback.diagonal f) = m '' Set.range d := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := j.surjective y
      exact ⟨d x, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨j x, by rw [← Scheme.Hom.comp_apply, ← hc, Scheme.Hom.comp_apply]⟩
  rw [key]
  exact m.isClosedMap _ hd

/- English proof (translation)
Establish `hm` using `MorphismProperty.pullbackMap (P := @UniversallyClosed) (f := j ≫ f) (g := j ≫ f) (f' := f) (g' := f) (i₁ := j) (i₂ := j) ‹UniversallyClosed j› ‹UniversallyClosed j› rfl rfl`. Establish `hcl` using `isClosed_range_diagonal_of_surjective_universallyClosed j f (pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 _) (Category.comp_id _) (Category.comp_id _)) (pullback.diagonal (j ≫ f)) (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range (pullback.comp_diagonal j f).symm`. Conclude with `⟨IsClosedImmersion.of_isPreimmersion _ hcl⟩`.
-/
theorem isSeparated_of_comp {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  have hm := MorphismProperty.pullbackMap (P := @UniversallyClosed) (f := j ≫ f) (g := j ≫ f)
    (f' := f) (g' := f) (i₁ := j) (i₂ := j) ‹UniversallyClosed j› ‹UniversallyClosed j› rfl rfl
  have hcl := isClosed_range_diagonal_of_surjective_universallyClosed j f
    (pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 _) (Category.comp_id _) (Category.comp_id _)) (pullback.diagonal (j ≫ f))
    (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range (pullback.comp_diagonal j f).symm
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hcl⟩

/- English proof (translation)
Use `⟨fun U hU hU' => ?_⟩` and prove the remaining obligations. Establish `h` using `(QuasiCompact.isCompact_preimage (f := j ≫ f) U hU hU').image j.continuous`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Take `⟨y, rfl⟩` from `j.surjective x`. Conclude with `⟨y, by simpa using hx, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify using `using hy`.
-/
theorem quasiCompact_of_comp {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [QuasiCompact (j ≫ f)] : QuasiCompact f := by
  refine ⟨fun U hU hU' => ?_⟩
  have h := (QuasiCompact.isCompact_preimage (f := j ≫ f) U hU hU').image j.continuous
  convert h using 1
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := j.surjective x
    exact ⟨y, by simpa using hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

/- English proof (translation)
Use `⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩` and prove the remaining obligations. Set `ιK : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K)` to `Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))`. Take `⟨q, hq⟩` from `exists_lift π (ιK ≫ y)`. Establish `hA : ConnectedSpace ↥(pullback f q)` using `GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)`. Establish `hιK : Surjective ιK` using `⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩`.

Set `M` to `(IsPullback.paste_horiz (IsPullback.of_hasPullback f q) h).isoPullback.hom ≫ (pullback.congrHom rfl hq).hom ≫ (pullbackLeftPullbackSndIso f' y ιK).inv ≫ pullback.fst (pullback.snd f' y) ιK`. Establish `hM : Surjective M` using `by dsimp only [M]; infer_instance`. Conclude with `M.surjective.connectedSpace M.continuous`.
-/
theorem geometricallyConnected_of_isPullback {X X' Y Y' : Scheme.{0}} {π : X ⟶ X'} [IsIntegralHom π]
    [Surjective π] {f : Y ⟶ X} {f' : Y' ⟶ X'} {φ : Y ⟶ Y'} (h : IsPullback φ f f' π)
    [GeometricallyConnected f] : GeometricallyConnected f' := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let ιK : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨q, hq⟩ := exists_lift π (ιK ≫ y)
  have hA : ConnectedSpace ↥(pullback f q) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  have hιK : Surjective ιK := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  let M := (IsPullback.paste_horiz (IsPullback.of_hasPullback f q) h).isoPullback.hom ≫
    (pullback.congrHom rfl hq).hom ≫ (pullbackLeftPullbackSndIso f' y ιK).inv ≫
      pullback.fst (pullback.snd f' y) ιK
  have hM : Surjective M := by dsimp only [M]; infer_instance
  exact M.surjective.connectedSpace M.continuous

/- English proof (translation)
Take `⟨hc, hsm, hsep, hqc, hgc, hfib⟩` from `hG`. Establish `hpb : IsPullback φ G.hom G'.hom π` using `h.1`. Establish `hφi : IsIntegralHom φ` using `MorphismProperty.of_isPullback hpb.flip ‹IsIntegralHom π›`. Establish `hφs : Surjective φ` using `MorphismProperty.of_isPullback hpb.flip ‹Surjective π›`. Establish `hw : φ ≫ G'.hom = G.hom ≫ π` using `hpb.w`.

Establish `hsep' : IsSeparated G'.hom`. Establish `: IsSeparated (φ ≫ G'.hom)` using `by rw [hw]; infer_instance`. Conclude with `isSeparated_of_comp φ G'.hom`. Establish `hqc' : QuasiCompact G'.hom`. Establish `: QuasiCompact (φ ≫ G'.hom)` using `by rw [hw]; infer_instance`.

Conclude with `quasiCompact_of_comp φ G'.hom`. Establish `hgc' : GeometricallyConnected G'.hom` using `geometricallyConnected_of_isPullback hpb`. Use `⟨‹_›, ‹_›, hsep', hqc', hgc', ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ p`. Take `⟨q, hq⟩` from `exists_lift π p`.

Take `⟨T⟩` from `hfib Ω q`. Establish `h1` using `isGrpPullback_pullback G q`. Establish `h2` using `IsGrpPullback.comp h1 h`. Establish `h3` using `isGrpPullback_pullback G' p`. Take `⟨e, he, -⟩` from `grpPullback_iso (h2.congr hq rfl) h3`.

Conclude with `⟨torusExtOfIso e T⟩`.
-/
theorem isSemiAbelian_descends {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} [GrpObj G] {G' : Over X'}
    [GrpObj G'] [IsCommMonObj G'] {φ : G.left ⟶ G'.left} [IsIntegralHom π] [Surjective π]
    (h : IsGrpPullback G G' π φ) [Smooth G'.hom] (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨hc, hsm, hsep, hqc, hgc, hfib⟩ := hG
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hφi : IsIntegralHom φ := MorphismProperty.of_isPullback hpb.flip ‹IsIntegralHom π›
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hsep' : IsSeparated G'.hom := by
    have : IsSeparated (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact isSeparated_of_comp φ G'.hom
  have hqc' : QuasiCompact G'.hom := by
    have : QuasiCompact (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact quasiCompact_of_comp φ G'.hom
  have hgc' : GeometricallyConnected G'.hom := geometricallyConnected_of_isPullback hpb
  refine ⟨‹_›, ‹_›, hsep', hqc', hgc', ?_⟩
  intro Ω _ _ p
  obtain ⟨q, hq⟩ := exists_lift π p
  obtain ⟨T⟩ := hfib Ω q
  have h1 := isGrpPullback_pullback G q
  have h2 := IsGrpPullback.comp h1 h
  have h3 := isGrpPullback_pullback G' p
  obtain ⟨e, he, -⟩ := grpPullback_iso (h2.congr hq rfl) h3
  exact ⟨torusExtOfIso e T⟩

/- English proof (translation)
Introduce `X X' π G _ G' _ _ φ hi hs h hsm hG`. Establish `hG' : IsSemiAbelian G'` using `isSemiAbelian_descends h hG`. Use `⟨hG', ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨U, hU, hP⟩`. Establish `hloc : ∀ x, π x ∈ abLocus G' ↔ x ∈ abLocus G` using `abLocus_pullback abLocusOne hG' h.1`.

Establish `hV : IsOpen (abLocus G')`. Establish `hc : (abLocus G')ᶜ = π '' (U : Set X)ᶜ`. Use extensionality with `y`. Take `⟨x, rfl⟩` from `π.surjective y`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Use `⟨x, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[Set.mem_compl_iff, hU, ← hloc]`. Conclude with `hy`. Introduce and unpack `⟨x', hx', hxx⟩`.

Rewrite using `[Set.mem_compl_iff, ← hxx, hloc, ← hU]`. Conclude with `hx'`. Rewrite using `[← isClosed_compl_iff, hc]`. Conclude with `π.isClosedMap _ U.isOpen.isClosed_compl`. Set `V' : X'.Opens` to `⟨abLocus G', hV⟩`.

Establish `hpre : π ⁻¹ᵁ V' = U`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `π x ∈ abLocus G' ↔ x ∈ (U : Set X)`. Rewrite using `[hU, hloc]`. Rewrite `hP` using `[← hpre]`.

Establish `hpb : IsPullback φ G.hom G'.hom π` using `h.1`. Establish `hw : φ ≫ G'.hom = G.hom ≫ π` using `hpb.w`. Establish `hφs : Surjective φ` using `MorphismProperty.of_isPullback hpb.flip ‹Surjective π›`. Establish `hle : G.hom ⁻¹ᵁ (π ⁻¹ᵁ V') ≤ φ ⁻¹ᵁ (G'.hom ⁻¹ᵁ V')`. Introduce `x hx`.

Express the relevant statement in the definitionally equal form `G'.hom (φ x) ∈ V'`. Rewrite using `[← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]`. Conclude with `hx`. Set `a` to `φ.resLE (G'.hom ⁻¹ᵁ V') (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')) hle`. Establish `heq : a ≫ (G'.hom ∣_ V') = (G.hom ∣_ (π ⁻¹ᵁ V')) ≫ (π ∣_ V')`.

Rewrite using `[← cancel_mono V'.ι]`. Simplify using `only [a, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc, hw]`. Establish `ha : Surjective a`. Prove the components needed by the constructor for the conclusion. Introduce `z`.

Take `⟨w, hw'⟩` from `φ.surjective ((G'.hom ⁻¹ᵁ V').ι z)`. Establish `hz : (G'.hom ⁻¹ᵁ V').ι z ∈ ((G'.hom ⁻¹ᵁ V' : G'.left.Opens) : Set G'.left)`. Rewrite using `[← Scheme.Opens.range_ι (G'.hom ⁻¹ᵁ V')]`. Conclude with `⟨z, rfl⟩`. Establish `hm : w ∈ Set.range (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')).ι`.

Rewrite using `[Scheme.Opens.range_ι]`. Express the relevant statement in the definitionally equal form `π (G.hom w) ∈ V'`. Rewrite using `[← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply, hw']`. Conclude with `hz`. Take `⟨w', rfl⟩` from `hm`.

Use `⟨w', (G'.hom ⁻¹ᵁ V').ι.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, hw']`. Establish `hsep : IsSeparated G'.hom` using `hG'.separated`. Establish `hcomp : UniversallyClosed (a ≫ (G'.hom ∣_ V'))`. Rewrite using `[heq]`.

Use `infer_instance`. Establish `huc : UniversallyClosed (G'.hom ∣_ V')` using `UniversallyClosed.of_comp_surjective a _`. Conclude with `⟨V', rfl, by constructor⟩`.
-/
theorem main : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G.left ⟶ G'.left), IsIntegralHom π → Surjective π → IsGrpPullback G G' π φ → Smooth G'.hom → IsSemiAbelian G → IsSemiAbelian G' ∧ ((∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)) → (∃ U : X'.Opens, (U : Set X') = abLocus G' ∧ IsProper (G'.hom ∣_ U))) := by
  intro X X' π G _ G' _ _ φ hi hs h hsm hG
  have hG' : IsSemiAbelian G' := isSemiAbelian_descends h hG
  refine ⟨hG', ?_⟩
  rintro ⟨U, hU, hP⟩
  have hloc : ∀ x, π x ∈ abLocus G' ↔ x ∈ abLocus G := abLocus_pullback abLocusOne hG' h.1
  have hV : IsOpen (abLocus G') := by
    have hc : (abLocus G')ᶜ = π '' (U : Set X)ᶜ := by
      ext y
      obtain ⟨x, rfl⟩ := π.surjective y
      constructor
      · intro hy
        refine ⟨x, ?_, rfl⟩
        rw [Set.mem_compl_iff, hU, ← hloc]
        exact hy
      · rintro ⟨x', hx', hxx⟩
        rw [Set.mem_compl_iff, ← hxx, hloc, ← hU]
        exact hx'
    rw [← isClosed_compl_iff, hc]
    exact π.isClosedMap _ U.isOpen.isClosed_compl
  let V' : X'.Opens := ⟨abLocus G', hV⟩
  have hpre : π ⁻¹ᵁ V' = U := by
    ext x
    change π x ∈ abLocus G' ↔ x ∈ (U : Set X)
    rw [hU, hloc]
  rw [← hpre] at hP
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hle : G.hom ⁻¹ᵁ (π ⁻¹ᵁ V') ≤ φ ⁻¹ᵁ (G'.hom ⁻¹ᵁ V') := by
    intro x hx
    change G'.hom (φ x) ∈ V'
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    exact hx
  let a := φ.resLE (G'.hom ⁻¹ᵁ V') (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')) hle
  have heq : a ≫ (G'.hom ∣_ V') = (G.hom ∣_ (π ⁻¹ᵁ V')) ≫ (π ∣_ V') := by
    rw [← cancel_mono V'.ι]
    simp only [a, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      Scheme.Hom.resLE_comp_ι_assoc, hw]
  have ha : Surjective a := by
    constructor
    intro z
    obtain ⟨w, hw'⟩ := φ.surjective ((G'.hom ⁻¹ᵁ V').ι z)
    have hz : (G'.hom ⁻¹ᵁ V').ι z ∈ ((G'.hom ⁻¹ᵁ V' : G'.left.Opens) : Set G'.left) := by
      rw [← Scheme.Opens.range_ι (G'.hom ⁻¹ᵁ V')]
      exact ⟨z, rfl⟩
    have hm : w ∈ Set.range (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')).ι := by
      rw [Scheme.Opens.range_ι]
      change π (G.hom w) ∈ V'
      rw [← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply, hw']
      exact hz
    obtain ⟨w', rfl⟩ := hm
    refine ⟨w', (G'.hom ⁻¹ᵁ V').ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, hw']
  have hsep : IsSeparated G'.hom := hG'.separated
  have hcomp : UniversallyClosed (a ≫ (G'.hom ∣_ V')) := by
    rw [heq]
    infer_instance
  have huc : UniversallyClosed (G'.hom ∣_ V') := UniversallyClosed.of_comp_surjective a _
  exact ⟨V', rfl, by constructor⟩

end GlobalTheory.SemiAbelianDescent
