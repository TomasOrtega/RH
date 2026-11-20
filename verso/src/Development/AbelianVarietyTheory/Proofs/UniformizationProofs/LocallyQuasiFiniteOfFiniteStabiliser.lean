import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteStabiliser

/- English proof (translation)
Establish `hr : Set.range h ⊆ Set.range W.ι`. Rewrite using `[Scheme.Opens.range_ι]`. Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `hh c`. Establish `: IsAffine W` using `hW`.

Set `l` to `IsOpenImmersion.lift W.ι h hr`. Establish `e : l ≫ W.ι = h` using `IsOpenImmersion.lift_fac _ _ _`. Establish `e' : l = F.toSpecΓ ≫ Spec.map l.appTop ≫ W.toScheme.isoSpec.inv`. Rewrite using `[← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]`. Use `letI := (isField_of_universallyClosed K q).toField`.

Establish `hab : F.toSpecΓ a = F.toSpecΓ b` using `Subsingleton.elim (α := PrimeSpectrum Γ(F, ⊤)) _ _`. Rewrite using `[← e, e']`. Simplify using `only [Scheme.Hom.comp_apply, hab]`.
-/
theorem apply_eq_of_range_subset_affine {K : Type} [Field K] {F Z : Scheme.{0}} [IsIntegral F]
    (q : F ⟶ Spec (.of K)) [UniversallyClosed q] (h : F ⟶ Z) {W : Z.Opens} (hW : IsAffineOpen W)
    (hh : ∀ a, h a ∈ W) (a b : F) : h a = h b := by
  have hr : Set.range h ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨c, rfl⟩
    exact hh c
  have : IsAffine W := hW
  let l := IsOpenImmersion.lift W.ι h hr
  have e : l ≫ W.ι = h := IsOpenImmersion.lift_fac _ _ _
  have e' : l = F.toSpecΓ ≫ Spec.map l.appTop ≫ W.toScheme.isoSpec.inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  letI := (isField_of_universallyClosed K q).toField
  have hab : F.toSpecΓ a = F.toSpecΓ b :=
    Subsingleton.elim (α := PrimeSpectrum Γ(F, ⊤)) _ _
  rw [← e, e']
  simp only [Scheme.Hom.comp_apply, hab]

/- English proof (translation)
Establish `huc : UniversallyClosed (snd F B).left`. Express the relevant statement in the definitionally equal form `UniversallyClosed (pullback.snd F.hom B.hom)`. Use `infer_instance`. Set `j : (𝟙_ _ ⟶ B) → (F ⟶ F ⊗ B)` to `fun x ↦ lift (𝟙 F) (toUnit F ≫ x)`. Establish `hpb (x : 𝟙_ _ ⟶ B) : IsPullback (j x).left F.hom (snd F B).left x.left`.

Establish `hw : x.left ≫ B.hom = 𝟙 _` using `Over.w x`. Establish `hr : IsPullback (fst F B).left (snd F B).left F.hom B.hom` using `.of_hasPullback F.hom B.hom`. Use `IsPullback.of_right ?_ ?_ hr` and prove the remaining obligations. Establish `: (j x).left ≫ (fst F B).left = 𝟙 F.left`. Rewrite using `[← Over.comp_left, lift_fst, Over.id_left]`.

Rewrite using `[this, hw]`. Conclude with `IsPullback.of_id_fst`. Rewrite using `[← Over.comp_left, lift_snd, Over.comp_left]`. Both sides reduce to the same expression. Take `⟨_, ⟨W, hW, rfl⟩, hzW, -⟩` from `Z.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ`.

Establish `hcl : IsClosed ((snd F B).left '' ((g.left ⁻¹ᵁ W : (F ⊗ B).left.Opens) : Set _)ᶜ)` using `(snd F B).left.isClosedMap _ (g.left ⁻¹ᵁ W).isOpen.isClosed_compl`. Set `pt : Spec (CommRingCat.of K)` to `IsLocalRing.closedPoint K`. Establish `hlft : LocallyOfFiniteType ((lift (toUnit B ≫ f) (𝟙 B) ≫ g).left ≫ Z.hom)`. Rewrite using `[Over.w]`. Use `infer_instance`.

Use `Over.OverMorphism.ext (ext_of_apply_eq (K := K) Z.hom _ hcl.isOpen_compl.isLocallyClosed (hcl.isOpen_compl.dense ⟨b.left pt, ?_⟩) (fun x hxV hx ↦ ?_) (by rw [Over.w, Over.w]))` and prove the remaining obligations. Introduce and unpack `⟨w, hw, hwb⟩`. Take `⟨a, rfl, -⟩` from `Scheme.exists_preimage_of_isPullback (hpb b) w pt hwb`. Apply `hw` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `g.left ((j b).left a) ∈ W`.

Rewrite using `[← Scheme.Hom.comp_apply, ← Over.comp_left, hz]`. Conclude with `hzW`. Set `p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B` to `Over.homMk (pointOfClosedPoint (K := K) B.hom x hx) (pointOfClosedPoint_comp (K := K) B.hom x hx)`. Establish `hp (s) : p.left s = x` using `pointOfClosedPoint_apply (K := K) B.hom x hx s`. Establish `hin (a : F.left) : (j p ≫ g).left a ∈ W`.

Assume the negation of the conclusion as `hn`. Use `hxV ⟨(j p).left a, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hn` using `[Over.comp_left, Scheme.Hom.comp_apply]`. Conclude with `hn`. Rewrite using `[← Scheme.Hom.comp_apply, (hpb p).w, Scheme.Hom.comp_apply, hp]`.

Establish `key (u : 𝟙_ _ ⟶ F) : (lift (toUnit B ≫ u) (𝟙 B) ≫ g).left x = (j p ≫ g).left (u.left pt)`. Establish `e : p ≫ lift (toUnit B ≫ u) (𝟙 B) ≫ g = u ≫ j p ≫ g`. Rewrite using `[← Category.assoc, ← Category.assoc]`. Use `congr 1`. Use `ext1`.

Simplify using `[j, toUnit_unique (toUnit _) (𝟙 _)]`. Simplify using `[j, toUnit_unique (toUnit _) (𝟙 _)]`. Rewrite using `[← hp pt, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, e]`. Rewrite using `[key, key]`. Conclude with `apply_eq_of_range_subset_affine (K := K) F.hom _ hW hin _ _`.
-/
theorem slice_eq {K : Type} [Field K] [IsAlgClosed K] {F B Z : Over (Spec (CommRingCat.of K))}
    [IsIntegral F.left] [UniversallyClosed F.hom] [IsIntegral B.left] [LocallyOfFiniteType B.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (g : F ⊗ B ⟶ Z) (b : 𝟙_ _ ⟶ B) (z : Z.left)
    (hz : ∀ a, (lift (𝟙 F) (toUnit F ≫ b) ≫ g).left a = z) (f f' : 𝟙_ _ ⟶ F) :
    lift (toUnit B ≫ f) (𝟙 B) ≫ g = lift (toUnit B ≫ f') (𝟙 B) ≫ g := by
  have huc : UniversallyClosed (snd F B).left := by
    change UniversallyClosed (pullback.snd F.hom B.hom); infer_instance
  let j : (𝟙_ _ ⟶ B) → (F ⟶ F ⊗ B) := fun x ↦ lift (𝟙 F) (toUnit F ≫ x)
  have hpb (x : 𝟙_ _ ⟶ B) : IsPullback (j x).left F.hom (snd F B).left x.left := by
    have hw : x.left ≫ B.hom = 𝟙 _ := Over.w x
    have hr : IsPullback (fst F B).left (snd F B).left F.hom B.hom := .of_hasPullback F.hom B.hom
    refine IsPullback.of_right ?_ ?_ hr
    · have : (j x).left ≫ (fst F B).left = 𝟙 F.left := by
        rw [← Over.comp_left, lift_fst, Over.id_left]
      rw [this, hw]
      exact IsPullback.of_id_fst
    · rw [← Over.comp_left, lift_snd, Over.comp_left]
      rfl
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
    Z.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hcl : IsClosed ((snd F B).left '' ((g.left ⁻¹ᵁ W : (F ⊗ B).left.Opens) : Set _)ᶜ) :=
    (snd F B).left.isClosedMap _ (g.left ⁻¹ᵁ W).isOpen.isClosed_compl
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hlft : LocallyOfFiniteType ((lift (toUnit B ≫ f) (𝟙 B) ≫ g).left ≫ Z.hom) := by
    rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Z.hom _ hcl.isOpen_compl.isLocallyClosed
    (hcl.isOpen_compl.dense ⟨b.left pt, ?_⟩) (fun x hxV hx ↦ ?_) (by rw [Over.w, Over.w]))
  · rintro ⟨w, hw, hwb⟩
    obtain ⟨a, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (hpb b) w pt hwb
    apply hw
    change g.left ((j b).left a) ∈ W
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hz]
    exact hzW
  · let p : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B :=
      Over.homMk (pointOfClosedPoint (K := K) B.hom x hx)
        (pointOfClosedPoint_comp (K := K) B.hom x hx)
    have hp (s) : p.left s = x := pointOfClosedPoint_apply (K := K) B.hom x hx s
    have hin (a : F.left) : (j p ≫ g).left a ∈ W := by
      by_contra hn
      refine hxV ⟨(j p).left a, ?_, ?_⟩
      · rw [Over.comp_left, Scheme.Hom.comp_apply] at hn
        exact hn
      · rw [← Scheme.Hom.comp_apply, (hpb p).w, Scheme.Hom.comp_apply, hp]
    have key (u : 𝟙_ _ ⟶ F) :
        (lift (toUnit B ≫ u) (𝟙 B) ≫ g).left x = (j p ≫ g).left (u.left pt) := by
      have e : p ≫ lift (toUnit B ≫ u) (𝟙 B) ≫ g = u ≫ j p ≫ g := by
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext1
        · simp [j, toUnit_unique (toUnit _) (𝟙 _)]
        · simp [j, toUnit_unique (toUnit _) (𝟙 _)]
      rw [← hp pt, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left,
        ← Over.comp_left, e]
    rw [key, key]
    exact apply_eq_of_range_subset_affine (K := K) F.hom _ hW hin _ _

/- English proof (translation)
Set `I` to `Scheme.IdealSheafData.vanishingIdeal S`. Establish `hrange : Set.range I.subschemeι = S`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι]`. Simplify using `[I]`. Set `F : Over (Spec (CommRingCat.of K))` to `Over.mk (I.subschemeι ≫ B.hom)`.

Set `i : F ⟶ B` to `Over.homMk I.subschemeι rfl`. Establish `hemb` using `I.subschemeι.isClosedEmbedding`. Establish `: IsReduced F.left` using `ReducedSubgroup.isReduced_subscheme_vanishingIdeal S`. Establish `: IrreducibleSpace F.left`. Establish `: IrreducibleSpace (Set.range I.subschemeι)`.

Rewrite using `[hrange]`. Conclude with `Subtype.irreducibleSpace hS`. Conclude with `hemb.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this`. Establish `: IsIntegral F.left` using `isIntegral_of_irreducibleSpace_of_isReduced _`. Establish `: IsProper F.hom` using `by change IsProper (I.subschemeι ≫ B.hom); infer_instance`.

Set `pt : Spec (CommRingCat.of K)` to `IsLocalRing.closedPoint K`. Establish `hpt (y : B.left) (hy : y ∈ (S : Set B.left) ∩ closedPoints B.left) : ∃ u : 𝟙_ _ ⟶ F, (u ≫ i).left pt = y`. Take `⟨a, rfl⟩ : y ∈ Set.range I.subschemeι` from `hrange ▸ hy.1`. Establish `ha : IsClosed ({a} : Set F.left)`. Use `hemb.isClosed_iff_image_isClosed.mpr ?_` and prove the remaining obligations.

Rewrite using `[Set.image_singleton]`. Conclude with `hy.2`. Use `⟨Over.homMk (pointOfClosedPoint (K := K) F.hom a ha) (pointOfClosedPoint_comp (K := K) F.hom a ha), ?_⟩` and prove the remaining obligations. Rewrite using `[Over.comp_left, Scheme.Hom.comp_apply]`. Conclude with `congrArg I.subschemeι (pointOfClosedPoint_apply (K := K) F.hom a ha pt)`.

Break down `((S : Set B.left) ∩ closedPoints B.left).eq_empty_or_nonempty with h | ⟨y₀, hy₀⟩` into its components or cases. Rewrite using `[h]`. Conclude with `Set.finite_empty`. Take `⟨u₀, -⟩` from `hpt y₀ hy₀`. Use `(hφ.image fun s ↦ (s * (u₀ ≫ i)).left pt).subset fun y hy ↦ ?_` and prove the remaining obligations.

Take `⟨u, rfl⟩` from `hpt y hy`. Use `⟨(u ≫ i) * (u₀ ≫ i)⁻¹, ?_, by simp only [inv_mul_cancel_right]⟩` and prove the remaining obligations. Establish `key` using `slice_eq (((fst F B ≫ i) * snd F B) ≫ φ) (1 : 𝟙_ _ ⟶ B) z (fun a ↦ by`. Rewrite using `[← Category.assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.comp_one, _root_.mul_one, Category.id_comp, Over.comp_left, Scheme.Hom.comp_apply]`. Conclude with `hz _ (hrange.le ⟨a, rfl⟩)) u u₀`.

Establish `key'` using `congrArg (fun t ↦ ((toUnit B ≫ u₀ ≫ i)⁻¹ * 𝟙 B) ≫ t) key`. Establish `hu (t : B ⟶ B) : t ≫ toUnit B = toUnit B` using `toUnit_unique _ _`. Simplify using `only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, hu, Category.comp_id, mul_inv_cancel_left, Category.id_comp] at key'`. Express the relevant statement in the definitionally equal form `(toUnit B ≫ ((u ≫ i) * (u₀ ≫ i)⁻¹) * 𝟙 B) ≫ φ = φ`. Simplify using `only [MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc, ← Category.assoc]`.

Conclude with `key'`.
-/
theorem finite_closedPoints_of_contracted {K : Type} [Field K] [IsAlgClosed K]
    {B Z : Over (Spec (CommRingCat.of K))} [GrpObj B] [IsIntegral B.left] [IsProper B.hom]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z)
    (hφ : {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}.Finite)
    (S : TopologicalSpace.Closeds B.left) (hS : IsIrreducible (S : Set B.left)) (z : Z.left)
    (hz : ∀ y ∈ S, φ.left y = z) : ((S : Set B.left) ∩ closedPoints B.left).Finite := by
  let I := Scheme.IdealSheafData.vanishingIdeal S
  have hrange : Set.range I.subschemeι = S := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  let F : Over (Spec (CommRingCat.of K)) := Over.mk (I.subschemeι ≫ B.hom)
  let i : F ⟶ B := Over.homMk I.subschemeι rfl
  have hemb := I.subschemeι.isClosedEmbedding
  have : IsReduced F.left := ReducedSubgroup.isReduced_subscheme_vanishingIdeal S
  have : IrreducibleSpace F.left := by
    have : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [hrange]; exact Subtype.irreducibleSpace hS
    exact hemb.isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr this
  have : IsIntegral F.left := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsProper F.hom := by change IsProper (I.subschemeι ≫ B.hom); infer_instance
  let pt : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hpt (y : B.left) (hy : y ∈ (S : Set B.left) ∩ closedPoints B.left) :
      ∃ u : 𝟙_ _ ⟶ F, (u ≫ i).left pt = y := by
    obtain ⟨a, rfl⟩ : y ∈ Set.range I.subschemeι := hrange ▸ hy.1
    have ha : IsClosed ({a} : Set F.left) := by
      refine hemb.isClosed_iff_image_isClosed.mpr ?_
      rw [Set.image_singleton]
      exact hy.2
    refine ⟨Over.homMk (pointOfClosedPoint (K := K) F.hom a ha)
      (pointOfClosedPoint_comp (K := K) F.hom a ha), ?_⟩
    rw [Over.comp_left, Scheme.Hom.comp_apply]
    exact congrArg I.subschemeι (pointOfClosedPoint_apply (K := K) F.hom a ha pt)
  rcases ((S : Set B.left) ∩ closedPoints B.left).eq_empty_or_nonempty with h | ⟨y₀, hy₀⟩
  · rw [h]; exact Set.finite_empty
  obtain ⟨u₀, -⟩ := hpt y₀ hy₀
  refine (hφ.image fun s ↦ (s * (u₀ ≫ i)).left pt).subset fun y hy ↦ ?_
  obtain ⟨u, rfl⟩ := hpt y hy
  refine ⟨(u ≫ i) * (u₀ ≫ i)⁻¹, ?_, by simp only [inv_mul_cancel_right]⟩
  have key := slice_eq (((fst F B ≫ i) * snd F B) ≫ φ) (1 : 𝟙_ _ ⟶ B) z (fun a ↦ by
    rw [← Category.assoc, MonObj.comp_mul, lift_fst_assoc, lift_snd, MonObj.comp_one,
      _root_.mul_one, Category.id_comp, Over.comp_left, Scheme.Hom.comp_apply]
    exact hz _ (hrange.le ⟨a, rfl⟩)) u u₀
  have key' := congrArg (fun t ↦ ((toUnit B ≫ u₀ ≫ i)⁻¹ * 𝟙 B) ≫ t) key
  have hu (t : B ⟶ B) : t ≫ toUnit B = toUnit B := toUnit_unique _ _
  simp only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, hu, Category.comp_id,
    mul_inv_cancel_left, Category.id_comp] at key'
  change (toUnit B ≫ ((u ≫ i) * (u₀ ≫ i)⁻¹) * 𝟙 B) ≫ φ = φ
  simp only [MonObj.comp_mul, GrpObj.comp_inv, _root_.mul_assoc, ← Category.assoc]
  exact key'

/- English proof (translation)
Introduce `K _ _ B _ _ hB Z _ _ φ hφ`. Use `hB.proper` as an intermediate fact. Use `hB.smooth` as an intermediate fact. Use `hB.geomConnected` as an intermediate fact. Establish `: GeometricallyIntegral B.hom` using `geometricallyIntegral_of_smooth B.hom`.

Establish `: IsIntegral B.left` using `GeometricallyIntegral.isIntegral_of_subsingleton B.hom`. Establish `: IsProper (φ.left ≫ Z.hom)` using `by rw [Over.w]; infer_instance`. Establish `: IsProper φ.left` using `.of_comp _ Z.hom`. Establish `: JacobsonSpace B.left` using `LocallyOfFiniteType.jacobsonSpace B.hom`. Establish `: IsLocallyNoetherian B.left` using `LocallyOfFiniteType.isLocallyNoetherian B.hom`.

Establish `: CompactSpace B.left` using `QuasiCompact.compactSpace_of_compactSpace B.hom`. Establish `: IsNoetherian B.left` using `{}`. Use `locallyQuasiFinite_of_finite_fibres_closedPoints φ.left fun y hy ↦ ?_` and prove the remaining obligations. Establish `hc : IsClosed (φ.left ⁻¹' {φ.left y})`. Use `IsClosed.preimage φ.left.continuous ?_` and prove the remaining obligations.

Simplify using `using φ.left.isClosedMap _ hy`. Use `finite_of_isClosed_of_finite_inter_closedPoints hc ?_` and prove the remaining obligations. Take `⟨T, hT, hTc, hTi, hTU⟩` from `TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hc`. Rewrite using `[hTU, Set.sUnion_eq_biUnion, Set.iUnion₂_inter]`. Use `hT.biUnion fun S hS ↦ ?_` and prove the remaining obligations.

Use `finite_closedPoints_of_contracted φ hφ ⟨S, hTc S hS⟩ (hTi S hS) (φ.left y) fun w hw ↦ ?_` and prove the remaining obligations. Conclude with `hTU.ge ⟨S, hS, hw⟩`.
-/
theorem locallyQuasiFinite_of_finite_stabiliser :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (Z : Over (Spec (CommRingCat.of K))) [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] (φ : B ⟶ Z), {x : 𝟙_ _ ⟶ B | ((toUnit B ≫ x) * 𝟙 B) ≫ φ = φ}.Finite → LocallyQuasiFinite φ.left := by
  intro K _ _ B _ _ hB Z _ _ φ hφ
  have := hB.proper
  have := hB.smooth
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom := geometricallyIntegral_of_smooth B.hom
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have : IsProper (φ.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  have : IsProper φ.left := .of_comp _ Z.hom
  have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : IsNoetherian B.left := {}
  refine locallyQuasiFinite_of_finite_fibres_closedPoints φ.left fun y hy ↦ ?_
  have hc : IsClosed (φ.left ⁻¹' {φ.left y}) := by
    refine IsClosed.preimage φ.left.continuous ?_
    simpa using φ.left.isClosedMap _ hy
  refine finite_of_isClosed_of_finite_inter_closedPoints hc ?_
  obtain ⟨T, hT, hTc, hTi, hTU⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hc
  rw [hTU, Set.sUnion_eq_biUnion, Set.iUnion₂_inter]
  refine hT.biUnion fun S hS ↦ ?_
  refine finite_closedPoints_of_contracted φ hφ ⟨S, hTc S hS⟩ (hTi S hS) (φ.left y) fun w hw ↦ ?_
  exact hTU.ge ⟨S, hS, hw⟩

end GlobalTheory.FiniteStabiliser
