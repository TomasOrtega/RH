import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusExtendsSemiabelian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocallyTrivialTorusQuotientFlatSurjectiveCosetsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothTorusQuotientOfGoodOpenCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyTorusExtensionOfSurjectivePointsStatement
import Development.AutomorphicArithmetic.DivisorFrames.FiniteExtensionCurveCover
import Development.AutomorphicArithmetic.DivisorFrames.SplitTorusBaseChangeSemiabelian
import Development.AutomorphicArithmetic.DivisorFrames.RosatiPolarisedDescendsFiniteField
import Development.AutomorphicArithmetic.DivisorFrames.RosatiActionPullback
import Development.AutomorphicArithmetic.DivisorFrames.WtGeneric
import Development.AutomorphicArithmetic.DivisorFrames.SplitTorusPullbackGenericFibre
import Development.AutomorphicArithmetic.DivisorFrames.TorusWeightUnitLocal
import Development.AutomorphicArithmetic.DivisorFrames.WeightUnitsSectionAtPoint
import Development.AutomorphicArithmetic.DivisorFrames.SmoothPointQuasiFiniteNeighbourhood
import Development.AutomorphicArithmetic.DivisorFrames.FiniteCoverOfQuasiFinite
import Development.AutomorphicArithmetic.DivisorFrames.QuasiFiniteRationalAfterExtension
import Development.AutomorphicArithmetic.DivisorFrames.FlatRationalSectionExtends
import Development.AutomorphicArithmetic.DivisorFrames.GoodOpenTranslateSection
import Development.AutomorphicArithmetic.DivisorFrames.GoodOpenPullback
import Development.AutomorphicArithmetic.DivisorFrames.SplitTorusClosedImmersion
import Development.AutomorphicArithmetic.DivisorFrames.SemiabelianQuotientTorusInvariants
import Development.AutomorphicArithmetic.DivisorFrames.LieQuotientKernelTorus
import Development.AutomorphicArithmetic.DivisorFrames.AbelianQuotientInheritsAction
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section TorusPartProof
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU GlobalTheory.TorusPart
open scoped CategoryTheory.Obj
set_option autoImplicit false

/- English proof (translation)
Establish `hw : φ₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f` using `by rw [h₂.1.1.w, Category.assoc]`. Establish `e₁` using `h₁.1.1.lift_fst φ₂ (G₂.hom ≫ g) hw`. Establish `e₂` using `h₁.1.1.lift_snd φ₂ (G₂.hom ≫ g) hw`. Use `⟨_, e₁, h₁.1.cancel (h₂.1.congr rfl e₁.symm) e₂, fun a => h₁.1.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, e₁, h₂.2, Category.assoc, h₁.2, ← Category.assoc, e₁]`.

Rewrite using `[Category.assoc, e₂, Category.assoc, Over.w, e₂, Over.w_assoc]`.
-/
private theorem TP.exists_factor {O : Type} [CommRing O] {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂}
    [GrpObj G] [GrpObj G₁] [GrpObj G₂] {i : OAct O G} {i₁ : OAct O G₁} {i₂ : OAct O G₂} {f : S₁ ⟶ S} {g : S₂ ⟶ S₁}
    {φ₁ : G₁.left ⟶ G.left} {φ₂ : G₂.left ⟶ G.left} (h₁ : IsActPull i₁ i f φ₁) (h₂ : IsActPull i₂ i (g ≫ f) φ₂) :
    ∃ χ : G₂.left ⟶ G₁.left, χ ≫ φ₁ = φ₂ ∧ IsActPull i₂ i₁ g χ := by
  have hw : φ₂ ≫ G.hom = (G₂.hom ≫ g) ≫ f := by rw [h₂.1.1.w, Category.assoc]
  have e₁ := h₁.1.1.lift_fst φ₂ (G₂.hom ≫ g) hw
  have e₂ := h₁.1.1.lift_snd φ₂ (G₂.hom ≫ g) hw
  refine ⟨_, e₁, h₁.1.cancel (h₂.1.congr rfl e₁.symm) e₂, fun a => h₁.1.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, e₁, h₂.2, Category.assoc, h₁.2, ← Category.assoc, e₁]
  · rw [Category.assoc, e₂, Category.assoc, Over.w, e₂, Over.w_assoc]

/- English proof (translation)
Use `Over.OverMorphism.ext (hψ.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))` and prove the remaining obligations. Establish `e : (i.act a).left ≫ q.left = q.left ≫ (j.act a).left` using `by rw [← Over.comp_left, h, Over.comp_left]`. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ.2, ← w, ← Category.assoc, hφ.2, Category.assoc, e, ← Category.assoc, w, Category.assoc]`.
-/
private theorem TP.equivariant_of_pull {O : Type} [CommRing O] {S S' : Scheme.{0}} {G B : Over S} {G' B' : Over S'}
    [GrpObj G] [GrpObj B] [GrpObj G'] [GrpObj B'] {i : OAct O G} {i' : OAct O G'} {j : OAct O B} {j' : OAct O B'}
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left} (hφ : IsActPull i' i f φ) (hψ : IsActPull j' j f ψ)
    {q : G ⟶ B} {q' : G' ⟶ B'} (w : φ ≫ q.left = q'.left ≫ ψ) (h : ∀ a, i.act a ≫ q = q ≫ j.act a) (a : O) :
    i'.act a ≫ q' = q' ≫ j'.act a := by
  refine Over.OverMorphism.ext (hψ.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have e : (i.act a).left ≫ q.left = q.left ≫ (j.act a).left := by rw [← Over.comp_left, h, Over.comp_left]
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ.2, ← w, ← Category.assoc, hφ.2,
    Category.assoc, e, ← Category.assoc, w, Category.assoc]

/- English proof (translation)
Introduce `C _ K _ x hx`. Use `hx.1` as an intermediate fact. Use `hx.2` as an intermediate fact. Establish `hg : x (IsLocalRing.closedPoint K) = genericPoint C`. Establish `e : (IsLocalRing.closedPoint K : Sp K) = genericPoint (Sp K)` using `Subsingleton.elim _ _`.

Rewrite using `[e]`. Use `((genericPoint_spec (Sp K)).image x.continuous).eq ?_` and prove the remaining obligations. Rewrite using `[Set.image_univ, x.denseRange.closure_range]`. Conclude with `genericPoint_spec C`. Establish `h1 : IsIso (x.stalkMap (IsLocalRing.closedPoint K))`.

Use `(ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, x.stalkMap_surjective _⟩` and prove the remaining obligations. Establish `hF : IsField (C.presheaf.stalk (x (IsLocalRing.closedPoint K)))`. Rewrite using `[hg]`. Conclude with `Field.toIsField C.functionField`. Use `letI := hF.toField`.

Establish `hN : ∀ z : Sp K, Nontrivial ((Sp K).presheaf.stalk z)` using `fun z => inferInstance`. Use `hN (IsLocalRing.closedPoint K)` as an intermediate fact. Conclude with `RingHom.injective _`. Establish `h2 : IsIso (Scheme.stalkClosedPointTo (R` using `CommRingCat.of K) x) := by`. Unfold `Scheme.stalkClosedPointTo`.

Use `infer_instance`. Establish `hs : genericPoint C ⤳ x (IsLocalRing.closedPoint K)` using `(genericPoint_spec C).specializes trivial`. Use `⟨(inv (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x) ≫ C.presheaf.stalkSpecializes hs).hom, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map (inv (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x) ≫ C.presheaf.stalkSpecializes hs) ≫ x = C.fromSpecStalk (genericPoint C)`. Establish `h3` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of K) x`.

Rewrite using `[← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs]`. Use `Eq.trans (congrArg (_ ≫ ·) h3.symm) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id_assoc]`.
-/
private theorem TP.genpt : ∀ (C : Scheme.{0}) [IsIntegral C] (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
    ∃ β : K →+* C.functionField, spMap β ≫ x = genPt C := by
  intro C _ K _ x hx
  have := hx.1
  have := hx.2
  have hg : x (IsLocalRing.closedPoint K) = genericPoint C := by
    have e : (IsLocalRing.closedPoint K : Sp K) = genericPoint (Sp K) := Subsingleton.elim _ _
    rw [e]
    refine ((genericPoint_spec (Sp K)).image x.continuous).eq ?_
    rw [Set.image_univ, x.denseRange.closure_range]
    exact genericPoint_spec C
  have h1 : IsIso (x.stalkMap (IsLocalRing.closedPoint K)) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, x.stalkMap_surjective _⟩
    have hF : IsField (C.presheaf.stalk (x (IsLocalRing.closedPoint K))) := by
      rw [hg]; exact Field.toIsField C.functionField
    letI := hF.toField
    have hN : ∀ z : Sp K, Nontrivial ((Sp K).presheaf.stalk z) := fun z => inferInstance
    have := hN (IsLocalRing.closedPoint K)
    exact RingHom.injective _
  have h2 : IsIso (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x) := by
    unfold Scheme.stalkClosedPointTo
    infer_instance
  have hs : genericPoint C ⤳ x (IsLocalRing.closedPoint K) := (genericPoint_spec C).specializes trivial
  refine ⟨(inv (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x) ≫ C.presheaf.stalkSpecializes hs).hom, ?_⟩
  change Spec.map (inv (Scheme.stalkClosedPointTo (R := CommRingCat.of K) x) ≫ C.presheaf.stalkSpecializes hs) ≫ x =
    C.fromSpecStalk (genericPoint C)
  have h3 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of K) x
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs]
  refine Eq.trans (congrArg (_ ≫ ·) h3.symm) ?_
  rw [← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id_assoc]

/- English proof (translation)
Introduce `S S' π Z K K₁ _ _ β x x₁ hx h Ω _ β₁ y hy`. Establish `hy' : y ≫ pullback.snd Z.hom π = spMap β₁ ≫ x₁` using `hy`. Take `⟨y₁, h₁, h₂⟩` from `h Ω β₁ (y ≫ pullback.fst Z.hom π) (by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hy', Category.assoc, hx])`. Use `⟨pullback.lift y₁ x₁ (h₁.trans hx.symm), pullback.lift_snd _ _ _, pullback.hom_ext ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, pullback.lift_fst, h₂]`. Rewrite using `[Category.assoc, pullback.lift_snd, hy']`.
-/
private theorem TP.ratpull : ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (Z : Over S) (K K₁ : Type) [Field K] [Field K₁] (β : K →+* K₁)
    (x : Sp K ⟶ S) (x₁ : Sp K₁ ⟶ S'), x₁ ≫ π = spMap β ≫ x → RatOver Z (spMap β ≫ x) →
    RatOver ((Over.pullback π).obj Z) x₁ := by
  intro S S' π Z K K₁ _ _ β x x₁ hx h Ω _ β₁ y hy
  have hy' : y ≫ pullback.snd Z.hom π = spMap β₁ ≫ x₁ := hy
  obtain ⟨y₁, h₁, h₂⟩ := h Ω β₁ (y ≫ pullback.fst Z.hom π) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy', Category.assoc, hx])
  refine ⟨pullback.lift y₁ x₁ (h₁.trans hx.symm), pullback.lift_snd _ _ _, pullback.hom_ext ?_ ?_⟩
  · rw [Category.assoc, pullback.lift_fst, h₂]
  · rw [Category.assoc, pullback.lift_snd, hy']

/- English proof (translation)
Introduce `S T G B _ _ u q ⟨_, h₂, h₃, h₄, h₅⟩ _ hu`. Establish `hc : UniversallyClosed (η[B]).left` using `MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (h₅.map (Over.forget _)) ⟨⟨h₃, h₂⟩, h₄⟩ (inferInstanceAs (UniversallyClosed u.left))`. Establish `hi : IsImmersion (η[B]).left`. Establish `: IsImmersion ((η[B]).left ≫ B.hom)`. Rewrite using `[Over.w]`.

Conclude with `inferInstanceAs (IsImmersion (𝟙 S))`. Conclude with `IsImmersion.of_comp _ B.hom`. Establish `: IsClosedImmersion (η[B]).left` using `IsClosedImmersion.of_isPreimmersion _ (η[B]).left.isClosedMap.isClosed_range`. Conclude with `GlobalTheory.TorusQuotientGlue.isSeparated_of_unit B`.
-/
private theorem TP.sepquot : ∀ (S : Scheme.{0}) (T G B : Over S) [GrpObj G] [GrpObj B] (u : T ⟶ G) (q : G ⟶ B), IsKer u q →
    LocallyOfFinitePresentation q.left → IsClosedImmersion u.left → IsSeparated B.hom := by
  intro S T G B _ _ u q ⟨_, h₂, h₃, h₄, h₅⟩ _ hu
  have hc : UniversallyClosed (η[B]).left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (h₅.map (Over.forget _)) ⟨⟨h₃, h₂⟩, h₄⟩ (inferInstanceAs (UniversallyClosed u.left))
  have hi : IsImmersion (η[B]).left := by
    have : IsImmersion ((η[B]).left ≫ B.hom) := by
      rw [Over.w]
      exact inferInstanceAs (IsImmersion (𝟙 S))
    exact IsImmersion.of_comp _ B.hom
  have : IsClosedImmersion (η[B]).left :=
    IsClosedImmersion.of_isPreimmersion _ (η[B]).left.isClosedMap.isClosed_range
  exact GlobalTheory.TorusQuotientGlue.isSeparated_of_unit B

/- English proof (translation)
Introduce `p _ k _ _ S _ T G B _ _ _ u q hG ⟨_, hq, _, hsu, _, _, hc, hs, hsep, hqc, hg⟩`. Use `⟨hc, hs, hsep, hqc, hg, fun Ω _ _ x => ?_⟩` and prove the remaining obligations. Establish `h₂ : SmConn ((Over.pullback x).obj B)`. Use `⟨inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Smooth (pullback.snd B.hom x)`.

Use `infer_instance`. Use `show IsSeparated (pullback.snd B.hom x)`. Use `infer_instance`. Use `show QuasiCompact (pullback.snd B.hom x)`. Use `infer_instance`.

Use `show GeometricallyConnected (pullback.snd B.hom x)`. Use `infer_instance`. Use `GlobalTheory.T.nonempty_torusExtension_of_surjective_points' Ω ((Over.pullback x).obj G) ((Over.pullback x).obj B) h₂ (hG.fibres Ω x) ((Over.pullback x).map q) inferInstance fun y => ?_` and prove the remaining obligations. Use `hG.smooth` as an intermediate fact. Establish `: LocallyOfFiniteType (q.left ≫ B.hom)` using `by rw [Over.w]; infer_instance`.

Establish `: LocallyOfFiniteType q.left` using `locallyOfFiniteType_of_comp _ B.hom`. Establish `sq` using `isPullback_pullback_map_left x q`. Establish `: Surjective ((Over.pullback x).map q).left` using `MorphismProperty.of_isPullback (P := @Surjective) sq hsu`. Establish `: LocallyOfFiniteType ((Over.pullback x).map q).left` using `MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance`. Set `s : pullback ((Over.pullback x).map q).left y.left ⟶ Sp Ω` to `pullback.snd _ _`.

Establish `: LocallyOfFiniteType s` using `inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))`. Establish `: Surjective s` using `inferInstanceAs (Surjective (pullback.snd _ _))`. Establish `: JacobsonSpace ↥(pullback ((Over.pullback x).map q).left y.left)` using `LocallyOfFiniteType.jacobsonSpace s`. Take `⟨z₀, -⟩` from `s.surjective (IsLocalRing.closedPoint Ω)`. Take `⟨z, -, hz⟩` from `nonempty_inter_closedPoints (Z := Set.univ) ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed`.

Establish `hz₁ : pointOfClosedPoint s z hz ≫ s = 𝟙 _` using `pointOfClosedPoint_comp s z hz`. Establish `e : (pointOfClosedPoint s z hz ≫ pullback.fst _ _) ≫ ((Over.pullback x).map q).left = y.left`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc]`. Conclude with `(congrArg (· ≫ y.left) hz₁).trans (Category.id_comp _)`. Use `⟨Over.homMk (pointOfClosedPoint s z hz ≫ pullback.fst _ _) ?_, Over.OverMorphism.ext e⟩` and prove the remaining obligations.

Rewrite using `[← Over.w ((Over.pullback x).map q), ← Category.assoc, e]`. Conclude with `Over.w y`.
-/
private theorem TP.semiab : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (S : Scheme.{0}) [Algebra k Γ(S, ⊤)]
    (T G B : Over S) [GrpObj T] [GrpObj G] [GrpObj B] (u : T ⟶ G) (q : G ⟶ B), IsSemiAbelian G → IsQuot u q → IsSemiAbelian B := by
  intro p _ k _ _ S _ T G B _ _ _ u q hG ⟨_, hq, _, hsu, _, _, hc, hs, hsep, hqc, hg⟩
  refine ⟨hc, hs, hsep, hqc, hg, fun Ω _ _ x => ?_⟩
  have h₂ : SmConn ((Over.pullback x).obj B) := by
    refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
    · show Smooth (pullback.snd B.hom x); infer_instance
    · show IsSeparated (pullback.snd B.hom x); infer_instance
    · show QuasiCompact (pullback.snd B.hom x); infer_instance
    · show GeometricallyConnected (pullback.snd B.hom x); infer_instance
  refine GlobalTheory.T.nonempty_torusExtension_of_surjective_points' Ω ((Over.pullback x).obj G) ((Over.pullback x).obj B) h₂ (hG.fibres Ω x)
    ((Over.pullback x).map q) inferInstance fun y => ?_
  have := hG.smooth
  have : LocallyOfFiniteType (q.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp _ B.hom
  have sq := isPullback_pullback_map_left x q
  have : Surjective ((Over.pullback x).map q).left := MorphismProperty.of_isPullback (P := @Surjective) sq hsu
  have : LocallyOfFiniteType ((Over.pullback x).map q).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  let s : pullback ((Over.pullback x).map q).left y.left ⟶ Sp Ω := pullback.snd _ _
  have : LocallyOfFiniteType s := inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : Surjective s := inferInstanceAs (Surjective (pullback.snd _ _))
  have : JacobsonSpace ↥(pullback ((Over.pullback x).map q).left y.left) := LocallyOfFiniteType.jacobsonSpace s
  obtain ⟨z₀, -⟩ := s.surjective (IsLocalRing.closedPoint Ω)
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨z₀, trivial⟩ isClosed_univ.isLocallyClosed
  have hz₁ : pointOfClosedPoint s z hz ≫ s = 𝟙 _ := pointOfClosedPoint_comp s z hz
  have e : (pointOfClosedPoint s z hz ≫ pullback.fst _ _) ≫ ((Over.pullback x).map q).left = y.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ y.left) hz₁).trans (Category.id_comp _)
  refine ⟨Over.homMk (pointOfClosedPoint s z hz ≫ pullback.fst _ _) ?_, Over.OverMorphism.ext e⟩
  rw [← Over.w ((Over.pullback x).map q), ← Category.assoc, e]
  exact Over.w y

/- English proof (translation)
Introduce `O _ c S S' f G _ G' _ hc i i' φ hφ X _ u u' hT K K' _ _ β x x' hx ⟨G₀, _, i₀, φ₀, u₀, P, q, j, h₀, hT₀, hk, he, hr⟩`. Establish `: IsCommMonObj G'` using `GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hφ.1`. Take `⟨P', j', ψ, hψ, hr'⟩` from `UpperTheory.rosati_action_pullback O c _ _ (spMap β) P j hr`. Establish `h₁` using `exists_isActPull x' i'`. Establish `h₂` using `h₁.comp hφ`.

Rewrite `h₂` using `[hx]`. Take `⟨χ, hχ, hχ'⟩` from `TP.exists_factor h₀ h₂`. Take `⟨u'', hT'', -⟩` from `existsUnique_torusCompat (S' := Sp K') (G' := (Over.pullback x').obj G') h₁.1.1 u'`. Establish `h₃` using `hT''.trans hT`. Rewrite `h₃` using `[hx, ← hχ]`.

Take `⟨q', hk', hq'⟩` from `hk.baseChange hχ'.1 hψ.1 (TorusCompat.of_comp_right h₀.1.1 hχ'.1.1.w h₃ hT₀)`. Conclude with `⟨_, _, _, _, u'', P', q', j', h₁, hT'', hk', TP.equivariant_of_pull hχ' hψ hq'.w he, hr'⟩`.
-/
private theorem TP.torpolbc : ∀ (O : Type) [CommRing O] (c : O →+* O) (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'],
    IsCommMonObj G → ∀ (i : OAct O G) (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i f φ →
    ∀ (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G) (u' : splitTorus S' X ⟶ G'), TorusCompat f φ u' u →
    ∀ (K K' : Type) [Field K] [Field K'] (β : K →+* K') (x : Sp K ⟶ S) (x' : Sp K' ⟶ S'), x' ≫ f = spMap β ≫ x →
    TorPol c i u x → TorPol c i' u' x' := by
  intro O _ c S S' f G _ G' _ hc i i' φ hφ X _ u u' hT K K' _ _ β x x' hx ⟨G₀, _, i₀, φ₀, u₀, P, q, j, h₀, hT₀, hk, he, hr⟩
  have : IsCommMonObj G' := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hφ.1
  obtain ⟨P', j', ψ, hψ, hr'⟩ := UpperTheory.rosati_action_pullback O c _ _ (spMap β) P j hr
  have h₁ := exists_isActPull x' i'
  have h₂ := h₁.comp hφ
  rw [hx] at h₂
  obtain ⟨χ, hχ, hχ'⟩ := TP.exists_factor h₀ h₂
  obtain ⟨u'', hT'', -⟩ := existsUnique_torusCompat (S' := Sp K') (G' := (Over.pullback x').obj G') h₁.1.1 u'
  have h₃ := hT''.trans hT
  rw [hx, ← hχ] at h₃
  obtain ⟨q', hk', hq'⟩ := hk.baseChange hχ'.1 hψ.1 (TorusCompat.of_comp_right h₀.1.1 hχ'.1.1.w h₃ hT₀)
  exact ⟨_, _, _, _, u'', P', q', j', h₁, hT'', hk', TP.equivariant_of_pull hχ' hψ hq'.w he, hr'⟩

/- English proof (translation)
Introduce `O _ _ c K Ω _ _ _ _ G _ hG i G' _ i' φ hφ ⟨T, P, e, j, hm, ha, hr⟩`. Set `_` to `T.addCommGroup`. Set `_` to `T.free`. Set `_` to `T.finite`. Set `_` to `T.grpB`.

Use `hG.comm` as an intermediate fact. Take `⟨F, hF, G₀, _, i₀, φ₀, Y, _, _, _, u₀, B, _, q₀, j₀, ψ, h₀, hB, hu₀, hk₀, ha₀, hψ⟩` from `UpperTheory.split_torus_base_change_semiabelian O K Ω G hG i G' i' φ hφ T.X T.i P.A (T.q ≫ e.hom) j P.isAb T.i_hom ((isKer_torusExtension T).comp_iso e hm) ha`. Take `⟨F', hF', P₁, j₁, ψ₁, h₁, hr₁⟩` from `UpperTheory.rosati_polarised_descends_finite_field O c F Ω B hB j₀ P j ψ hψ hr`. Establish `: IsCommMonObj G₀` using `GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback h₀.1`. Establish `h₂` using `exists_isActPull (spMap (algebraMap F F')) i₀`.

Establish `h₃` using `h₂.comp h₀`. Establish `hc : spMap (algebraMap F F') ≫ spMap (algebraMap K F) = spMap (algebraMap K F')`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite `h₃` using `[hc]`.

Take `⟨u₂, hT₂, -⟩` from `existsUnique_torusCompat (S' := Sp F') (G' := (Over.pullback (spMap (algebraMap F F'))).obj G₀) h₂.1.1 u₀`. Take `⟨q₂, hk₂, hq₂⟩` from `hk₀.baseChange h₂.1 h₁.1 hT₂`. Conclude with `⟨F', inferInstance, inferInstance, Module.Finite.trans F F', _, _, _, _, Y, _, inferInstance, inferInstance, u₂, P₁, q₂, j₁, h₃, hT₂.isMonHom h₂.1, hk₂, TP.equivariant_of_pull h₂ h₁ hq₂.w ha₀, hr₁⟩`.
-/
private theorem TP.poldesc : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (c : O →+* O) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (G : Over (Sp K)) [GrpObj G], IsSemiAbelian G → ∀ (i : OAct O G) (G' : Over (Sp Ω)) [GrpObj G']
    (i' : OAct O G') (φ : G'.left ⟶ G.left), IsActPull i' i (spMap (algebraMap K Ω)) φ → PolPart c i' →
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K'), FiniteDimensional K K' ∧
      ∃ (G₂ : Over (Sp K')) (_ : GrpObj G₂) (i₂ : OAct O G₂) (φ₂ : G₂.left ⟶ G.left)
        (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u₂ : splitTorus (Sp K') X ⟶ G₂)
        (P : Out.PolAV (Sp K')) (q₂ : G₂ ⟶ P.A) (j₂ : OAct O P.A),
        IsActPull i₂ i (spMap (algebraMap K K')) φ₂ ∧ IsMonHom u₂ ∧ IsKer u₂ q₂ ∧
        (∀ a, i₂.act a ≫ q₂ = q₂ ≫ j₂.act a) ∧ IsRosati c P j₂ := by
  intro O _ _ c K Ω _ _ _ _ G _ hG i G' _ i' φ hφ ⟨T, P, e, j, hm, ha, hr⟩
  let _ := T.addCommGroup
  let _ := T.free
  let _ := T.finite
  let _ := T.grpB
  have := hG.comm
  obtain ⟨F, hF, G₀, _, i₀, φ₀, Y, _, _, _, u₀, B, _, q₀, j₀, ψ, h₀, hB, hu₀, hk₀, ha₀, hψ⟩ :=
    UpperTheory.split_torus_base_change_semiabelian O K Ω G hG i G' i' φ hφ T.X T.i P.A (T.q ≫ e.hom) j P.isAb T.i_hom
      ((isKer_torusExtension T).comp_iso e hm) ha
  obtain ⟨F', hF', P₁, j₁, ψ₁, h₁, hr₁⟩ := UpperTheory.rosati_polarised_descends_finite_field O c F Ω B hB j₀ P j ψ hψ hr
  have : IsCommMonObj G₀ := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback h₀.1
  have h₂ := exists_isActPull (spMap (algebraMap F F')) i₀
  have h₃ := h₂.comp h₀
  have hc : spMap (algebraMap F F') ≫ spMap (algebraMap K F) = spMap (algebraMap K F') := by
    rw [← Spec.map_comp]; rfl
  rw [hc] at h₃
  obtain ⟨u₂, hT₂, -⟩ := existsUnique_torusCompat (S' := Sp F')
    (G' := (Over.pullback (spMap (algebraMap F F'))).obj G₀) h₂.1.1 u₀
  obtain ⟨q₂, hk₂, hq₂⟩ := hk₀.baseChange h₂.1 h₁.1 hT₂
  exact ⟨F', inferInstance, inferInstance, Module.Finite.trans F F', _, _, _, _, Y, _, inferInstance, inferInstance, u₂, P₁,
    q₂, j₁, h₃, hT₂.isMonHom h₂.1, hk₂, TP.equivariant_of_pull h₂ h₁ hq₂.w ha₀, hr₁⟩

namespace GlobalTheory.TorusPart

/- English proof (translation)
Use `h.isIntegral` as an intermediate fact. Use `h.smooth` as an intermediate fact. Establish `: LocallyOfFiniteType (strHom k C)` using `inferInstance`. Use `⟨NefCurveTest.smoothOfRelativeDimension_one _ h.dim_eq, h.isProjOver, ?_⟩` and prove the remaining obligations. Conclude with `geometricallyConnected_of_isAlgClosed _`.
-/
private theorem isCurve_of_isSmoothProjCurve {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
    (h : IsSmoothProjCurve k C) : IsCurve k C := by
  have := h.isIntegral
  have := h.smooth
  have : LocallyOfFiniteType (strHom k C) := inferInstance
  refine ⟨NefCurveTest.smoothOfRelativeDimension_one _ h.dim_eq, h.isProjOver, ?_⟩
  exact geometricallyConnected_of_isAlgClosed _

/- English proof (translation)
Take `⟨hs, hp, hc⟩` from `h`. Establish `: IsIntegral C` using `GlobalTheory.LieSemineg.isIntegral_curve hs hc`. Conclude with `⟨⟨inferInstance, GlobalTheory.LieSemineg.dim_curve hs, hp⟩, SmoothOfRelativeDimension.smooth 1 _⟩`.
-/
private theorem isSmoothProjCurve_of_isCurve {k : Type} [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] (h : IsCurve k C) :
    IsSmoothProjCurve k C := by
  obtain ⟨hs, hp, hc⟩ := h
  have : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hs hc
  exact ⟨⟨inferInstance, GlobalTheory.LieSemineg.dim_curve hs, hp⟩, SmoothOfRelativeDimension.smooth 1 _⟩

/- English proof (translation)
Take `⟨hcomm, hsm, hsep, hqc, hgc⟩` from `hG`. Take `⟨B, q, H⟩` from `UpperTheory.semiabelian_quotient_torus_invariants S G X u hu hc`. Establish `haff : IsAffineHom q.left` using `isAffineHom_of_forall_exists_isAffineOpen _ fun b => by`. Take `⟨V, hb, hV, hg, -⟩` from `H b`. Conclude with `⟨V, hb, hV, hg.1⟩`.

Take `⟨hm, hf, hs, hsB, hfib⟩` from `GlobalTheory.T.locallyTrivial_torusQuotient_flat_surjective_cosets _ X G B u q hu haff fun b => by`. Take `⟨V, hb, hV, hg, h₁, h₂⟩` from `H b`. Conclude with `⟨V, hb, hV, h₁, h₂, hg.2⟩`. Take `⟨_, hcB, hq, hker⟩` from `GlobalTheory.grpObj_of_flat_coset_quotient _ G _ B u q hu hm hf hs inferInstance hfib`. Establish `hsB` using `hsB hsm`.

Establish `hw : q.left ≫ B.hom = G.hom` using `Over.w q`. Establish `hgB : GeometricallyConnected B.hom`. Establish `: GeometricallyConnected (q.left ≫ B.hom)` using `hw ▸ hgc`. Conclude with `GlobalTheory.TorusQuotientGlue.geometricallyConnected_of_comp q.left B.hom`. Establish `hqB : QuasiCompact B.hom`.

Use `⟨fun U hU hK => ?_⟩` and prove the remaining obligations. Establish `h1` using `hqc.isCompact_preimage U hU hK`. Establish `e : q.left '' (G.hom ⁻¹' U) = B.hom ⁻¹' U`. Rewrite using `[← hw, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq _ q.left.surjective]`. Conclude with `e ▸ h1.image q.left.continuous`.

Establish `hsq : Smooth q.left`. Use `MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ((H1.torsor_pullback u q hker).map (Over.forget _)).flip ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_` and prove the remaining obligations. Conclude with `smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) (H1.torus_dim _ X).smooth`. Establish `hcl : IsClosedImmersion u.left` using `UpperTheory.split_torus_closed_immersion S G hsep hqc X u hu hm hc`. Establish `hsepB : IsSeparated B.hom` using `TP.sepquot S _ G B u q ⟨hq, hf, hs, inferInstance, hker⟩ inferInstance hcl`.

Conclude with `⟨B, _, q, ⟨hu, hq, hf, hs, haff, hker, hcB, hsB, hsepB, hqB, hgB⟩, hsq, hcl⟩`.
-/
private theorem exists_isQuot {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : SmConn G) (X : Type) [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [hu : IsMonHom u] (hc : GoodCover u) :
    ∃ (B : Over S) (_ : GrpObj B) (q : G ⟶ B), IsQuot u q ∧ Smooth q.left ∧ IsClosedImmersion u.left := by
  obtain ⟨hcomm, hsm, hsep, hqc, hgc⟩ := hG
  obtain ⟨B, q, H⟩ := UpperTheory.semiabelian_quotient_torus_invariants S G X u hu hc
  have haff : IsAffineHom q.left := isAffineHom_of_forall_exists_isAffineOpen _ fun b => by
    obtain ⟨V, hb, hV, hg, -⟩ := H b
    exact ⟨V, hb, hV, hg.1⟩
  obtain ⟨hm, hf, hs, hsB, hfib⟩ := GlobalTheory.T.locallyTrivial_torusQuotient_flat_surjective_cosets _ X G B u q hu haff fun b => by
    obtain ⟨V, hb, hV, hg, h₁, h₂⟩ := H b
    exact ⟨V, hb, hV, h₁, h₂, hg.2⟩
  obtain ⟨_, hcB, hq, hker⟩ := GlobalTheory.grpObj_of_flat_coset_quotient _ G _ B u q hu hm hf hs inferInstance hfib
  have hsB := hsB hsm
  have hw : q.left ≫ B.hom = G.hom := Over.w q
  have hgB : GeometricallyConnected B.hom := by
    have : GeometricallyConnected (q.left ≫ B.hom) := hw ▸ hgc
    exact GlobalTheory.TorusQuotientGlue.geometricallyConnected_of_comp q.left B.hom
  have hqB : QuasiCompact B.hom := by
    refine ⟨fun U hU hK => ?_⟩
    have h1 := hqc.isCompact_preimage U hU hK
    have e : q.left '' (G.hom ⁻¹' U) = B.hom ⁻¹' U := by
      rw [← hw, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
        Set.image_preimage_eq _ q.left.surjective]
    exact e ▸ h1.image q.left.continuous
  have hsq : Smooth q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback u q hker).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) (H1.torus_dim _ X).smooth
  have hcl : IsClosedImmersion u.left := UpperTheory.split_torus_closed_immersion S G hsep hqc X u hu hm hc
  have hsepB : IsSeparated B.hom := TP.sepquot S _ G B u q ⟨hq, hf, hs, inferInstance, hker⟩ inferInstance hcl
  exact ⟨B, _, q, ⟨hu, hq, hf, hs, haff, hker, hcB, hsB, hsepB, hqB, hgB⟩, hsq, hcl⟩

/- English proof (translation)
Introduce `g`. Establish `hs : SmoothOfRelativeDimension 1 (strHom k C₁)` using `hC₁.1`. Establish `: Smooth (strHom k C₁)` using `SmoothOfRelativeDimension.smooth 1 _`. Set `s₁` to `G₁.hom ≫ strHom k C₁`. Establish `: LocallyOfFiniteType s₁` using `inferInstance`.

Establish `: JacobsonSpace G₁.left` using `LocallyOfFiniteType.jacobsonSpace s₁`. Take `⟨y, hy, hyc⟩` from `nonempty_inter_closedPoints (Z := closure {g}) ⟨g, subset_closure rfl⟩ isClosed_closure.isLocallyClosed`. Set `yp` to `pointOfClosedPoint s₁ y hyc`. Establish `hyp : yp ≫ s₁ = 𝟙 _` using `pointOfClosedPoint_comp s₁ y hyc`. Set `p₁` to `yp ≫ G₁.hom`.

Establish `hp₁ : p₁ ≫ strHom k C₁ = 𝟙 _` using `by simpa [p₁, s₁] using hyp`. Set `p₀` to `p₁ ≫ π`. Establish `hp₀ : p₀ ≫ strHom k C₀ = 𝟙 _` using `by simp only [p₀, Category.assoc, hπ, hp₁]`. Set `y₁ : Over.mk p₁ ⟶ G₁` to `Over.homMk yp rfl`. Set `y₀ : Over.mk p₀ ⟶ G₀` to `Over.homMk (yp ≫ φ) (by`.

Express the relevant statement in the definitionally equal form `(yp ≫ φ) ≫ G₀.hom = p₁ ≫ π`. Rewrite using `[Category.assoc, hφ.1.w, ← Category.assoc])`. Take `⟨m, g₀, w, hwW, hy₀⟩` from `hcov p₀ hp₀ y₀`. Set `Z'` to `(Over.pullback π).obj (Z m)`. Establish `hfl : Flat Z'.hom`.

Use `(hZ m).1` as an intermediate fact. Conclude with `inferInstanceAs (Flat (pullback.snd (Z m).hom π))`. Establish `hlft : LocallyOfFiniteType Z'.hom`. Use `(hZ m).2.1` as an intermediate fact. Conclude with `inferInstanceAs (LocallyOfFiniteType (pullback.snd (Z m).hom π))`.

Establish `hg₀w : g₀.left ≫ (Z m).hom = p₁ ≫ π` using `Over.w g₀`. Set `g₀' : Over.mk p₁ ⟶ Z'` to `Over.homMk (pullback.lift g₀.left p₁ hg₀w) (pullback.lift_snd _ _ _)`. Take `⟨U, σ, p', hp'⟩` from `UpperTheory.flat_rational_section_extends k C₁ hC₁ K₁ x₁ hx₁ Z' hfl hlft (hrat m) k p₁ g₀'`. Take `⟨e, he, heφ⟩` from `grpPullback_iso (isGrpPullback_pullback G₀ π) hφ`. Set `σ₁ : Over.mk U.ι ⟶ G₁` to `σ ≫ (Over.pullback π).map (z m) ≫ e.hom`.

Establish `hww : w.left ≫ G₀.hom = p₁ ≫ π` using `Over.w w`. Set `w₁ : Over.mk p₁ ⟶ G₁` to `(Over.homMk (pullback.lift w.left p₁ hww) (pullback.lift_snd _ _ _) : Over.mk p₁ ⟶ (Over.pullback π).obj G₀) ≫ e.hom`. Establish `hw₁ : w₁.left ≫ φ = w.left`. Simplify using `only [w₁, Over.comp_left, Category.assoc, heφ, Over.homMk_left, pullback.lift_fst]`. Establish `pt : Sp k` using `IsLocalRing.closedPoint k`.

Take `⟨V, hwV, hV⟩` from `hW _ (hwW (Set.mem_univ pt))`. Establish `hV₁` using `UpperTheory.good_open_pullback C₀ C₁ π inferInstance G₀ G₁ φ hφ X u₀ u₁ hT V hV`. Establish `hmem : w₁.left pt ∈ φ ⁻¹ᵁ V`. Express the relevant statement in the definitionally equal form `φ (w₁.left pt) ∈ V`. Rewrite using `[← Scheme.Hom.comp_apply, hw₁]`.

Conclude with `hwV`. Take `⟨V', hV', hmem'⟩` from `UpperTheory.good_open_translate_section C₁ G₁ inferInstance X u₁ hu₁ _ hV₁ U σ₁ (Over.mk p₁) p' w₁ pt hmem`. Establish `key : (p' ≫ σ₁) * w₁ = y₁`. Establish `h₁ : (p' ≫ σ₁).left ≫ φ = (g₀ ≫ z m).left`. Establish `a : p'.left ≫ σ.left = g₀'.left` using `by rw [← Over.comp_left, hp']`.

Simplify using `only [σ₁, Over.comp_left, Category.assoc, heφ]`. Rewrite using `[← Category.assoc p'.left, a, GlobalTheory.ExtUnique.pullback_map_left_fst]`. Simplify using `only [g₀', Over.homMk_left, pullback.lift_fst_assoc]`. Establish `h₂` using `hφ.2 (Over.mk p₁) (p' ≫ σ₁) w₁ (g₀ ≫ z m) w h₁.symm hw₁.symm`. Rewrite `h₂` using `[← hy₀]`.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `hφ.1.hom_ext ?_ ?_` and prove the remaining obligations. Conclude with `h₂.symm`. Rewrite using `[Over.w, Over.w]`. Use `⟨V', ?_, hV'⟩` and prove the remaining obligations.

Establish `hyV' : y ∈ V'`. Rewrite `hmem'` using `[key]`. Express the relevant statement in the definitionally equal form `yp pt ∈ V' at hmem'`. Rewrite `hmem'` using `[pointOfClosedPoint_apply s₁ y hyc pt]`. Then use the resulting hypothesis. Conclude with `(specializes_iff_mem_closure.2 hy).mem_open V'.isOpen hyV'`.
-/
private theorem goodCover_of_cover {k : Type} [Field k] [IsAlgClosed k] {C₀ C₁ : Scheme.{0}} [Algebra k Γ(C₀, ⊤)]
    [Algebra k Γ(C₁, ⊤)] (hC₁ : IsCurve k C₁) {K₁ : Type} [Field K₁] (x₁ : Sp K₁ ⟶ C₁) (hx₁ : IsGen x₁)
    (π : C₁ ⟶ C₀) [IsAffineHom π] (hπ : π ≫ strHom k C₀ = strHom k C₁) {G₀ : Over C₀} [GrpObj G₀] {G₁ : Over C₁}
    [GrpObj G₁] [IsCommMonObj G₁] [LocallyOfFiniteType G₁.hom] (φ : G₁.left ⟶ G₀.left) (hφ : IsGrpPullback G₁ G₀ π φ)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u₀ : splitTorus C₀ X ⟶ G₀)
    (u₁ : splitTorus C₁ X ⟶ G₁) [hu₁ : IsMonHom u₁] (hT : TorusCompat π φ u₁ u₀) (W : G₀.left.Opens)
    (hW : ∀ x ∈ W, ∃ V, x ∈ V ∧ GoodOpen u₀ V) {n : ℕ} (Z : Fin n → Over C₀) (z : ∀ m, Z m ⟶ G₀)
    (hZ : ∀ m, QFin (Z m))
    (hcov : ∀ p : Sp k ⟶ C₀, p ≫ strHom k C₀ = 𝟙 _ → ∀ y : Over.mk p ⟶ G₀,
      ∃ (m : Fin n) (g₀ : Over.mk p ⟶ Z m) (w : Over.mk p ⟶ G₀), ⊤ ≤ w.left ⁻¹ᵁ W ∧ y = (g₀ ≫ z m) * w)
    (hrat : ∀ m, RatOver ((Over.pullback π).obj (Z m)) x₁) : GoodCover u₁ := by
  intro g
  have hs : SmoothOfRelativeDimension 1 (strHom k C₁) := hC₁.1
  have : Smooth (strHom k C₁) := SmoothOfRelativeDimension.smooth 1 _
  let s₁ := G₁.hom ≫ strHom k C₁
  have : LocallyOfFiniteType s₁ := inferInstance
  have : JacobsonSpace G₁.left := LocallyOfFiniteType.jacobsonSpace s₁
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (Z := closure {g}) ⟨g, subset_closure rfl⟩
    isClosed_closure.isLocallyClosed
  let yp := pointOfClosedPoint s₁ y hyc
  have hyp : yp ≫ s₁ = 𝟙 _ := pointOfClosedPoint_comp s₁ y hyc
  let p₁ := yp ≫ G₁.hom
  have hp₁ : p₁ ≫ strHom k C₁ = 𝟙 _ := by simpa [p₁, s₁] using hyp
  let p₀ := p₁ ≫ π
  have hp₀ : p₀ ≫ strHom k C₀ = 𝟙 _ := by simp only [p₀, Category.assoc, hπ, hp₁]
  let y₁ : Over.mk p₁ ⟶ G₁ := Over.homMk yp rfl
  let y₀ : Over.mk p₀ ⟶ G₀ := Over.homMk (yp ≫ φ) (by
    change (yp ≫ φ) ≫ G₀.hom = p₁ ≫ π
    rw [Category.assoc, hφ.1.w, ← Category.assoc])
  obtain ⟨m, g₀, w, hwW, hy₀⟩ := hcov p₀ hp₀ y₀
  let Z' := (Over.pullback π).obj (Z m)
  have hfl : Flat Z'.hom := by
    have := (hZ m).1
    exact inferInstanceAs (Flat (pullback.snd (Z m).hom π))
  have hlft : LocallyOfFiniteType Z'.hom := by
    have := (hZ m).2.1
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd (Z m).hom π))
  have hg₀w : g₀.left ≫ (Z m).hom = p₁ ≫ π := Over.w g₀
  let g₀' : Over.mk p₁ ⟶ Z' := Over.homMk (pullback.lift g₀.left p₁ hg₀w) (pullback.lift_snd _ _ _)
  obtain ⟨U, σ, p', hp'⟩ := UpperTheory.flat_rational_section_extends k C₁ hC₁ K₁ x₁ hx₁ Z' hfl hlft (hrat m) k p₁ g₀'
  obtain ⟨e, he, heφ⟩ := grpPullback_iso (isGrpPullback_pullback G₀ π) hφ
  let σ₁ : Over.mk U.ι ⟶ G₁ := σ ≫ (Over.pullback π).map (z m) ≫ e.hom
  have hww : w.left ≫ G₀.hom = p₁ ≫ π := Over.w w
  let w₁ : Over.mk p₁ ⟶ G₁ :=
    (Over.homMk (pullback.lift w.left p₁ hww) (pullback.lift_snd _ _ _) : Over.mk p₁ ⟶ (Over.pullback π).obj G₀) ≫ e.hom
  have hw₁ : w₁.left ≫ φ = w.left := by
    simp only [w₁, Over.comp_left, Category.assoc, heφ, Over.homMk_left, pullback.lift_fst]
  have pt : Sp k := IsLocalRing.closedPoint k
  obtain ⟨V, hwV, hV⟩ := hW _ (hwW (Set.mem_univ pt))
  have hV₁ := UpperTheory.good_open_pullback C₀ C₁ π inferInstance G₀ G₁ φ hφ X u₀ u₁ hT V hV
  have hmem : w₁.left pt ∈ φ ⁻¹ᵁ V := by
    change φ (w₁.left pt) ∈ V
    rw [← Scheme.Hom.comp_apply, hw₁]
    exact hwV
  obtain ⟨V', hV', hmem'⟩ := UpperTheory.good_open_translate_section C₁ G₁ inferInstance X u₁ hu₁ _ hV₁ U σ₁ (Over.mk p₁) p' w₁ pt hmem
  have key : (p' ≫ σ₁) * w₁ = y₁ := by
    have h₁ : (p' ≫ σ₁).left ≫ φ = (g₀ ≫ z m).left := by
      have a : p'.left ≫ σ.left = g₀'.left := by rw [← Over.comp_left, hp']
      simp only [σ₁, Over.comp_left, Category.assoc, heφ]
      rw [← Category.assoc p'.left, a, GlobalTheory.ExtUnique.pullback_map_left_fst]
      simp only [g₀', Over.homMk_left, pullback.lift_fst_assoc]
    have h₂ := hφ.2 (Over.mk p₁) (p' ≫ σ₁) w₁ (g₀ ≫ z m) w h₁.symm hw₁.symm
    rw [← hy₀] at h₂
    apply Over.OverMorphism.ext
    refine hφ.1.hom_ext ?_ ?_
    · exact h₂.symm
    · rw [Over.w, Over.w]
  refine ⟨V', ?_, hV'⟩
  have hyV' : y ∈ V' := by
    rw [key] at hmem'
    change yp pt ∈ V' at hmem'
    rwa [pointOfClosedPoint_apply s₁ y hyc pt] at hmem'
  exact (specializes_iff_mem_closure.2 hy).mem_open V'.isOpen hyV'

/- English proof (translation)
Take `⟨h₁, h₂, h₃, h₄, h₅⟩` from `h`. Use `⟨h₁, h₂, h₃, h₄, ?_⟩` and prove the remaining obligations. Use `h₅.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp) (by simp)` and prove the remaining obligations.
-/
private theorem IsKer.precomp {S : Scheme.{0}} {T T' G B : Over S} [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) (e : T' ≅ T) : IsKer (e.hom ≫ u) q := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨h₁, h₂, h₃, h₄, ?_⟩
  refine h₅.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (toUnit_unique _ _) (by simp) (by simp)

/- English proof (translation)
Establish `: IsMonHom (Iso.refl G).hom` using `inferInstanceAs (IsMonHom (𝟙 G))`. Conclude with `⟨isGrpPullback_of_iso (Iso.refl G), fun a => by simp⟩`.
-/
private theorem isActPull_id {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] (i : OAct O G) :
    IsActPull i i (𝟙 S) (𝟙 G.left) := by
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  exact ⟨isGrpPullback_of_iso (Iso.refl G), fun a => by simp⟩

/- English proof (translation)
Use `⟨h, fun a => hG.1.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hc, Category.assoc, hG.2]`. Rewrite using `[Category.assoc, Category.assoc, Over.w, h.1.w, Over.w_assoc]`.
-/
private theorem IsActPull.of_comp {O : Type} [CommRing O] {S S₁ S₂ : Scheme.{0}} {G : Over S} {G₁ : Over S₁} {G₂ : Over S₂}
    [GrpObj G] [GrpObj G₁] [GrpObj G₂] {i : OAct O G} {i₁ : OAct O G₁} {i₂ : OAct O G₂} {π : S₁ ⟶ S} {x : S₂ ⟶ S₁}
    {φ : G₁.left ⟶ G.left} {φ₀ : G₂.left ⟶ G₁.left} (hG : IsActPull i₁ i π φ) (h : IsGrpPullback G₂ G₁ x φ₀)
    (hc : ∀ a, (i₂.act a).left ≫ φ₀ ≫ φ = φ₀ ≫ φ ≫ (i.act a).left) : IsActPull i₂ i₁ x φ₀ := by
  refine ⟨h, fun a => hG.1.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hc, Category.assoc, hG.2]
  · rw [Category.assoc, Category.assoc, Over.w, h.1.w, Over.w_assoc]

/- English proof (translation)
Establish `hw : φ ≫ G.hom = (G₂.hom ≫ g) ≫ f` using `by rw [h.1.1.w, Category.assoc]`. Use `⟨pullback.lift φ (G₂.hom ≫ g) hw, pullback.lift_fst _ _ _, ?_⟩` and prove the remaining obligations. Establish `hK` using `exists_isActPull f i`. Use `IsActPull.of_comp hK ((isGrpPullback_pullback G f).cancel (h.1.congr rfl (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)) fun a => ?_` and prove the remaining obligations. Rewrite using `[pullback.lift_fst, pullback.lift_fst_assoc, h.2]`.
-/
private theorem IsActPull.cancel_pullback {O : Type} [CommRing O] {S S₁ S₂ : Scheme.{0}} {G : Over S} [GrpObj G]
    [IsCommMonObj G] {G₂ : Over S₂} [GrpObj G₂] {i : OAct O G} {i₂ : OAct O G₂} (f : S₁ ⟶ S) (g : S₂ ⟶ S₁)
    {φ : G₂.left ⟶ G.left} (h : IsActPull i₂ i (g ≫ f) φ) :
    ∃ φ' : G₂.left ⟶ ((Over.pullback f).obj G).left, φ' ≫ pullback.fst G.hom f = φ ∧
      IsActPull i₂ (OAct.pullback f G i) g φ' := by
  have hw : φ ≫ G.hom = (G₂.hom ≫ g) ≫ f := by rw [h.1.1.w, Category.assoc]
  refine ⟨pullback.lift φ (G₂.hom ≫ g) hw, pullback.lift_fst _ _ _, ?_⟩
  have hK := exists_isActPull f i
  refine IsActPull.of_comp hK ((isGrpPullback_pullback G f).cancel (h.1.congr rfl (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)) fun a => ?_
  rw [pullback.lift_fst, pullback.lift_fst_assoc, h.2]

/- English proof (translation)
Introduce `_ _ E _ _ _ H q _ k _ _ _ C _ _ hC G _ hG i hPol`. Use `hG.comm` as an intermediate fact. Establish `hCv` using `isCurve_of_isSmoothProjCurve hC`. Use `hC.isIntegral` as an intermediate fact. Take `⟨G', _, i', φ, hφ, hPP⟩` from `hPol`.

Take `⟨φ', -, hφ'⟩` from `IsActPull.cancel_pullback (genPt C) _ hφ`. Establish `hGK` using `IsSemiAbelian.pullback (genPt C) G hG`. Take `⟨K', _, _, hfin, G₂, _, i₂, φ₂, X, _, _, _, u₂, P, q₂, j₂, h₂, hu₂, hk₂, he₂, hros⟩` from `TP.poldesc (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) C.functionField (AlgebraicClosure C.functionField) _ hGK _ G' i' φ' hφ' hPP`. Take `⟨C₀, _, π₀, x₀, hC₀, hx₀, hπ₀, hfπ₀, hsπ₀, hxπ₀⟩` from `UpperTheory.finite_extension_curve_cover k C hCv C.functionField (genPt C) (isGen_fromSpecStalk C) K' hfin`. Establish `hC₀i : IsIntegral C₀` using `GlobalTheory.LieSemineg.isIntegral_curve hC₀.1 hC₀.2.2`.

Set `G₀` to `(Over.pullback π₀).obj G`. Set `i₀` to `OAct.pullback π₀ G i`. Establish `hact₀ : IsActPull i₀ i π₀ (pullback.fst G.hom π₀)` using `exists_isActPull π₀ i`. Establish `hG₀ : IsSemiAbelian G₀` using `IsSemiAbelian.pullback π₀ G hG`. Use `hG₀.comm` as an intermediate fact.

Establish `hcomp` using `(h₂.comp (exists_isActPull (genPt C) i))`. Rewrite `hcomp` using `[← hxπ₀]`. Take `⟨φ₀', -, hφ₀'⟩` from `IsActPull.cancel_pullback π₀ x₀ hcomp`. Take `⟨e₂, he₂m, he₂φ⟩` from `grpPullback_iso hφ₀'.1 (isGrpPullback_pullback G₀ x₀)`. Take `⟨u, ψ, hu, hψ, hψu⟩` from `exists_torus_hom_extension k C₀ hC₀ K' x₀ hx₀ G₀ hG₀ X (u₂ ≫ e₂.hom)`.

Take `⟨e₃, he₃m, he₃ψ⟩` from `grpPullback_iso (SplitTorus.isGrpPullback_bcMap x₀ X) hψ`. Establish `hTC : TorusCompat x₀ φ₀' (e₃.hom ≫ u₂) u`. Rewrite using `[torusCompat_iff, ← he₃ψ, Category.assoc, hψu, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, he₂φ]`. Establish `hTP₀ : TorPol (H.bar : 𝓞 E →+* 𝓞 E) i₀ u x₀` using `⟨G₂, _, i₂, φ₀', e₃.hom ≫ u₂, P, q₂, j₂, hφ₀', hTC, hk₂.precomp e₃, he₂, hros⟩`. Establish `hG₂c : IsCommMonObj G₂` using `GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hφ₀'.1`.

Take `⟨hq₂m, hq₂f, hq₂s, hq₂c, hq₂k⟩` from `hk₂.precomp e₃`. Take `⟨O', h₁', h₂', h₃', hd⟩` from `GlobalTheory.T.exists_splitExtDatum_of_splitTorus_extension (Sp K') X G₂ P.A P.isAb q₂ (e₃.hom ≫ u₂) hq₂m inferInstance hq₂f hq₂s hq₂c hq₂k`. Take `⟨d, hdq, hdi⟩` from `hd P.isAb`. Establish `hwt : ∀ χ : X, ∃ (U' : G₂.left.Opens) (f' : Γ(G₂.left, U')), (U' : Set G₂.left).Nonempty ∧ IsUnit f' ∧ Wt (e₃.hom ≫ u₂) U' f' χ`. Introduce `χ`.

Take `⟨V, hb, w, hw⟩` from `(TQ.ofGtDatum d).loc ((η[P.A]).left (IsLocalRing.closedPoint K')) χ`. Establish `: Surjective d.q.left` using `d.q_surjective`. Take `⟨g, hg⟩` from `d.q.left.surjective ((η[P.A]).left (IsLocalRing.closedPoint K'))`. Use `⟨_, w.val, ⟨g, ?_⟩, w.isUnit, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `d.q.left g ∈ V`.

Rewrite using `[hg]`. Conclude with `hb`. Conclude with `hdi ▸ hw`. Use `hG₀.smooth` as an intermediate fact. Use `hG₀.quasiCompact` as an intermediate fact.

Establish `hwf : ∀ (χ : X) (s : C₀), ∃ (U : G₀.left.Opens) (f : Γ(G₀.left, U)), (∃ y ∈ U, G₀.hom y = s) ∧ IsUnit f ∧ Wt u U f χ`. Introduce `χ s`. Take `⟨U', f', hne, hun, hw⟩` from `hwt χ`. Take `⟨U, f, hne', hun', hw'⟩` from `UpperTheory.split_torus_pullback_generic_fibre UpperTheory.wt_generic k C₀ hC₀ K' x₀ hx₀ G₀ hG₀ X u hu G₂ φ₀' (e₃.hom ≫ u₂) hφ₀'.1 hTC χ U' f' hne hun hw`. Conclude with `UpperTheory.torus_weight_unit_local UpperTheory.wt_generic k C₀ hC₀ G₀ hG₀ X u hu χ U f hne' hun' hw' s`.

Establish `hsl` using `UpperTheory.weight_units_section_at_point k C₀ hC₀ G₀ hG₀ X u hu hwf`. Set `W : G₀.left.Opens` to `sSup {V | GoodOpen u V}`. Establish `hW : ∀ x ∈ W, ∃ V, x ∈ V ∧ GoodOpen u V`. Introduce `x hx`. Take `⟨V, hV, hxV⟩` from `TopologicalSpace.Opens.mem_sSup.1 hx`.

Conclude with `⟨V, hxV, hV⟩`. Establish `hWp : ∀ p : Sp k ⟶ C₀, p ≫ strHom k C₀ = 𝟙 _ → ∃ w : Over.mk p ⟶ G₀, ⊤ ≤ w.left ⁻¹ᵁ W` using `fun p hp => by`. Take `⟨V, w, hV, hw⟩` from `hsl p hp`. Conclude with `⟨w, hw.trans (w.left.preimage_mono (le_sSup hV))⟩`. Take `⟨n, Z, z, hZ, hcov⟩` from `UpperTheory.finite_cover_of_quasi_finite k C₀ hC₀ G₀ inferInstance inferInstance W hWp (UpperTheory.smooth_point_quasi_finite_neighbourhood k C₀ hC₀ G₀ inferInstance)`.

Take `⟨K₁, _, _, hfin₁, hrat⟩` from `UpperTheory.quasi_finite_rational_after_extension C₀ n Z hZ K' x₀`. Take `⟨C₁, _, π₁, x₁, hC₁, hx₁, hπ₁, hfπ₁, hsπ₁, hxπ₁⟩` from `UpperTheory.finite_extension_curve_cover k C₀ hC₀ K' x₀ hx₀ K₁ hfin₁`. Set `G₁` to `(Over.pullback π₁).obj G₀`. Set `i₁` to `OAct.pullback π₁ G₀ i₀`. Establish `hact₁ : IsActPull i₁ i₀ π₁ (pullback.fst G₀.hom π₁)` using `exists_isActPull π₁ i₀`.

Establish `hG₁ : IsSemiAbelian G₁` using `IsSemiAbelian.pullback π₁ G₀ hG₀`. Use `hG₁.comm` as an intermediate fact. Use `hG₁.smooth` as an intermediate fact. Take `⟨u₁, hT₁, -⟩` from `existsUnique_torusCompat (S := C₀) (S' := C₁) (G' := G₁) (G := G₀) (f := π₁) (F := pullback.fst G₀.hom π₁) (isGrpPullback_pullback G₀ π₁).1 u`. Establish `hu₁ : IsMonHom u₁` using `TorusCompat.isMonHom (isGrpPullback_pullback G₀ π₁) hT₁`.

Establish `hrat₁ : ∀ m, RatOver ((Over.pullback π₁).obj (Z m)) x₁` using `fun m => TP.ratpull C₀ C₁ π₁ (Z m) K' K₁ (algebraMap K' K₁) x₀ x₁ hxπ₁ (hrat m)`. Establish `hgc : GoodCover u₁` using `goodCover_of_cover hC₁ x₁ hx₁ π₁ hπ₁ (pullback.fst G₀.hom π₁) (isGrpPullback_pullback G₀ π₁) u u₁ hT₁ W hW Z z hZ hcov hrat₁`. Establish `hsm₁ : SmConn G₁` using `⟨hG₁.comm, hG₁.smooth, hG₁.separated, hG₁.quasiCompact, hG₁.geomConnected⟩`. Take `⟨B, _, qB, hQ, hsq, hcl⟩` from `exists_isQuot G₁ hsm₁ X u₁ hgc`. Establish `hB : IsSemiAbelian B` using `TP.semiab q k C₁ (splitTorus C₁ X) G₁ B u₁ qB hG₁ hQ`.

Establish `hTP₁ : TorPol (H.bar : 𝓞 E →+* 𝓞 E) i₁ u₁ x₁` using `TP.torpolbc (𝓞 E) _ C₀ C₁ π₁ G₀ G₁ inferInstance i₀ i₁ _ hact₁ X u u₁ hT₁ K' K₁ (algebraMap K' K₁) x₀ x₁ hxπ₁ hTP₀`. Establish `hC₁i : IsIntegral C₁` using `GlobalTheory.LieSemineg.isIntegral_curve hC₁.1 hC₁.2.2`. Take `⟨β, hβ⟩` from `TP.genpt C₁ K₁ x₁ hx₁`. Establish `hTPg : TorPol (H.bar : 𝓞 E →+* 𝓞 E) i₁ u₁ (genPt C₁)` using `TP.torpolbc (𝓞 E) _ C₁ C₁ (𝟙 C₁) G₁ G₁ inferInstance i₁ i₁ (𝟙 _) (isActPull_id i₁) X u₁ u₁ (TorusCompat.refl u₁) K₁ C₁.functionField β x₁ (genPt C₁) (by rw [Category.comp_id, hβ]) hTP₁`. Use `hQ.2.1` as an intermediate fact.

Take `⟨i', hi', hab⟩` from `UpperTheory.abelian_quotient_inherits_action (𝓞 E) _ C₁ G₁ B hG₁ hB i₁ X u₁ qB hu₁ (isKer_of_isQuot hQ) hTPg`. Take `⟨hepi, ⟨eL⟩⟩` from `UpperTheory.lie_quotient_kernel_torus C₁ G₁ B X u₁ qB hsm₁ hQ hgc`. Use `⟨C₁, inferInstance, hC₁i, π₁ ≫ π₀, isSmoothProjCurve_of_isCurve hC₁, ⟨inferInstance, inferInstance, by rw [Category.assoc, hπ₀, hπ₁]⟩, G₁, inferInstance, hG₁, i₁, _, hact₁.comp hact₀, B, inferInstance, hB, i', qB, hQ.2.1, hi', hepi, ⟨_, ⟨eL ≪≫ (isFrame_dlogChar C₁ (Module.finBasi …` and prove the remaining obligations.
-/
private theorem main : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
  (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C],
  IsSmoothProjCurve k C → ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct (𝓞 E) G), PolGen (H.bar : 𝓞 E →+* 𝓞 E) i →
  ∃ (C₁ : Scheme.{0}) (_ : Algebra k Γ(C₁, ⊤)) (_ : IsIntegral C₁) (π : C₁ ⟶ C), IsSmoothProjCurve k C₁ ∧ IsCover k π ∧
    ∃ (G₁ : Over C₁) (_ : GrpObj G₁) (_ : IsSemiAbelian G₁) (i₁ : OAct (𝓞 E) G₁) (φ : G₁.left ⟶ G.left), IsActPull i₁ i π φ ∧
    ∃ (G' : Over C₁) (_ : GrpObj G') (_ : IsSemiAbelian G') (i' : OAct (𝓞 E) G') (ρ : G₁ ⟶ G') (_ : IsMonHom ρ),
      (∀ a, i₁.act a ≫ ρ = ρ ≫ i'.act a) ∧ Epi (lieMap ρ) ∧
      (∃ r : ℕ, Nonempty (kernel (lieMap ρ) ≅ GlobalTheory.QCoh.freeModule C₁ (Fin r))) ∧ AbGen (H.bar : 𝓞 E →+* 𝓞 E) i' := by
  intro _ _ E _ _ _ H q _ k _ _ _ C _ _ hC G _ hG i hPol
  have := hG.comm
  have hCv := isCurve_of_isSmoothProjCurve hC
  have := hC.isIntegral

  obtain ⟨G', _, i', φ, hφ, hPP⟩ := hPol
  obtain ⟨φ', -, hφ'⟩ := IsActPull.cancel_pullback (genPt C) _ hφ
  have hGK := IsSemiAbelian.pullback (genPt C) G hG
  obtain ⟨K', _, _, hfin, G₂, _, i₂, φ₂, X, _, _, _, u₂, P, q₂, j₂, h₂, hu₂, hk₂, he₂, hros⟩ :=
    TP.poldesc (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) C.functionField (AlgebraicClosure C.functionField) _ hGK _ G' i' φ' hφ' hPP

  obtain ⟨C₀, _, π₀, x₀, hC₀, hx₀, hπ₀, hfπ₀, hsπ₀, hxπ₀⟩ :=
    UpperTheory.finite_extension_curve_cover k C hCv C.functionField (genPt C) (isGen_fromSpecStalk C) K' hfin
  have hC₀i : IsIntegral C₀ := GlobalTheory.LieSemineg.isIntegral_curve hC₀.1 hC₀.2.2
  let G₀ := (Over.pullback π₀).obj G
  let i₀ := OAct.pullback π₀ G i
  have hact₀ : IsActPull i₀ i π₀ (pullback.fst G.hom π₀) := exists_isActPull π₀ i
  have hG₀ : IsSemiAbelian G₀ := IsSemiAbelian.pullback π₀ G hG
  have := hG₀.comm
  have hcomp := (h₂.comp (exists_isActPull (genPt C) i))
  rw [← hxπ₀] at hcomp
  obtain ⟨φ₀', -, hφ₀'⟩ := IsActPull.cancel_pullback π₀ x₀ hcomp
  obtain ⟨e₂, he₂m, he₂φ⟩ := grpPullback_iso hφ₀'.1 (isGrpPullback_pullback G₀ x₀)
  obtain ⟨u, ψ, hu, hψ, hψu⟩ := exists_torus_hom_extension k C₀ hC₀ K' x₀ hx₀ G₀ hG₀ X (u₂ ≫ e₂.hom)
  obtain ⟨e₃, he₃m, he₃ψ⟩ := grpPullback_iso (SplitTorus.isGrpPullback_bcMap x₀ X) hψ
  have hTC : TorusCompat x₀ φ₀' (e₃.hom ≫ u₂) u := by
    rw [torusCompat_iff, ← he₃ψ, Category.assoc, hψu, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc,
      he₂φ]
  have hTP₀ : TorPol (H.bar : 𝓞 E →+* 𝓞 E) i₀ u x₀ :=
    ⟨G₂, _, i₂, φ₀', e₃.hom ≫ u₂, P, q₂, j₂, hφ₀', hTC, hk₂.precomp e₃, he₂, hros⟩
  have hG₂c : IsCommMonObj G₂ := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hφ₀'.1
  obtain ⟨hq₂m, hq₂f, hq₂s, hq₂c, hq₂k⟩ := hk₂.precomp e₃
  obtain ⟨O', h₁', h₂', h₃', hd⟩ := GlobalTheory.T.exists_splitExtDatum_of_splitTorus_extension (Sp K') X G₂ P.A P.isAb q₂ (e₃.hom ≫ u₂) hq₂m inferInstance hq₂f hq₂s
    hq₂c hq₂k
  obtain ⟨d, hdq, hdi⟩ := hd P.isAb
  have hwt : ∀ χ : X, ∃ (U' : G₂.left.Opens) (f' : Γ(G₂.left, U')), (U' : Set G₂.left).Nonempty ∧ IsUnit f' ∧
      Wt (e₃.hom ≫ u₂) U' f' χ := by
    intro χ
    obtain ⟨V, hb, w, hw⟩ := (TQ.ofGtDatum d).loc ((η[P.A]).left (IsLocalRing.closedPoint K')) χ
    have : Surjective d.q.left := d.q_surjective
    obtain ⟨g, hg⟩ := d.q.left.surjective ((η[P.A]).left (IsLocalRing.closedPoint K'))
    refine ⟨_, w.val, ⟨g, ?_⟩, w.isUnit, ?_⟩
    · change d.q.left g ∈ V
      rw [hg]
      exact hb
    · exact hdi ▸ hw
  have := hG₀.smooth
  have := hG₀.quasiCompact
  have hwf : ∀ (χ : X) (s : C₀), ∃ (U : G₀.left.Opens) (f : Γ(G₀.left, U)), (∃ y ∈ U, G₀.hom y = s) ∧ IsUnit f ∧
      Wt u U f χ := by
    intro χ s
    obtain ⟨U', f', hne, hun, hw⟩ := hwt χ
    obtain ⟨U, f, hne', hun', hw'⟩ := UpperTheory.split_torus_pullback_generic_fibre UpperTheory.wt_generic k C₀ hC₀ K' x₀ hx₀ G₀ hG₀ X u hu G₂ φ₀'
      (e₃.hom ≫ u₂) hφ₀'.1 hTC χ U' f' hne hun hw
    exact UpperTheory.torus_weight_unit_local UpperTheory.wt_generic k C₀ hC₀ G₀ hG₀ X u hu χ U f hne' hun' hw' s
  have hsl := UpperTheory.weight_units_section_at_point k C₀ hC₀ G₀ hG₀ X u hu hwf
  let W : G₀.left.Opens := sSup {V | GoodOpen u V}
  have hW : ∀ x ∈ W, ∃ V, x ∈ V ∧ GoodOpen u V := by
    intro x hx
    obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
    exact ⟨V, hxV, hV⟩
  have hWp : ∀ p : Sp k ⟶ C₀, p ≫ strHom k C₀ = 𝟙 _ → ∃ w : Over.mk p ⟶ G₀, ⊤ ≤ w.left ⁻¹ᵁ W := fun p hp => by
    obtain ⟨V, w, hV, hw⟩ := hsl p hp
    exact ⟨w, hw.trans (w.left.preimage_mono (le_sSup hV))⟩
  obtain ⟨n, Z, z, hZ, hcov⟩ := UpperTheory.finite_cover_of_quasi_finite k C₀ hC₀ G₀ inferInstance inferInstance W hWp
    (UpperTheory.smooth_point_quasi_finite_neighbourhood k C₀ hC₀ G₀ inferInstance)
  obtain ⟨K₁, _, _, hfin₁, hrat⟩ := UpperTheory.quasi_finite_rational_after_extension C₀ n Z hZ K' x₀
  obtain ⟨C₁, _, π₁, x₁, hC₁, hx₁, hπ₁, hfπ₁, hsπ₁, hxπ₁⟩ := UpperTheory.finite_extension_curve_cover k C₀ hC₀ K' x₀ hx₀ K₁ hfin₁
  let G₁ := (Over.pullback π₁).obj G₀
  let i₁ := OAct.pullback π₁ G₀ i₀
  have hact₁ : IsActPull i₁ i₀ π₁ (pullback.fst G₀.hom π₁) := exists_isActPull π₁ i₀
  have hG₁ : IsSemiAbelian G₁ := IsSemiAbelian.pullback π₁ G₀ hG₀
  have := hG₁.comm
  have := hG₁.smooth
  obtain ⟨u₁, hT₁, -⟩ := existsUnique_torusCompat (S := C₀) (S' := C₁) (G' := G₁) (G := G₀) (f := π₁)
    (F := pullback.fst G₀.hom π₁) (isGrpPullback_pullback G₀ π₁).1 u
  have hu₁ : IsMonHom u₁ := TorusCompat.isMonHom (isGrpPullback_pullback G₀ π₁) hT₁
  have hrat₁ : ∀ m, RatOver ((Over.pullback π₁).obj (Z m)) x₁ := fun m =>
    TP.ratpull C₀ C₁ π₁ (Z m) K' K₁ (algebraMap K' K₁) x₀ x₁ hxπ₁ (hrat m)
  have hgc : GoodCover u₁ := goodCover_of_cover hC₁ x₁ hx₁ π₁ hπ₁ (pullback.fst G₀.hom π₁)
    (isGrpPullback_pullback G₀ π₁) u u₁ hT₁ W hW Z z hZ hcov hrat₁
  have hsm₁ : SmConn G₁ := ⟨hG₁.comm, hG₁.smooth, hG₁.separated, hG₁.quasiCompact, hG₁.geomConnected⟩
  obtain ⟨B, _, qB, hQ, hsq, hcl⟩ := exists_isQuot G₁ hsm₁ X u₁ hgc
  have hB : IsSemiAbelian B := TP.semiab q k C₁ (splitTorus C₁ X) G₁ B u₁ qB hG₁ hQ
  have hTP₁ : TorPol (H.bar : 𝓞 E →+* 𝓞 E) i₁ u₁ x₁ := TP.torpolbc (𝓞 E) _ C₀ C₁ π₁ G₀ G₁ inferInstance i₀ i₁ _
    hact₁ X u u₁ hT₁ K' K₁ (algebraMap K' K₁) x₀ x₁ hxπ₁ hTP₀
  have hC₁i : IsIntegral C₁ := GlobalTheory.LieSemineg.isIntegral_curve hC₁.1 hC₁.2.2
  obtain ⟨β, hβ⟩ := TP.genpt C₁ K₁ x₁ hx₁
  have hTPg : TorPol (H.bar : 𝓞 E →+* 𝓞 E) i₁ u₁ (genPt C₁) := TP.torpolbc (𝓞 E) _ C₁ C₁ (𝟙 C₁) G₁ G₁
    inferInstance i₁ i₁ (𝟙 _) (isActPull_id i₁) X u₁ u₁ (TorusCompat.refl u₁) K₁ C₁.functionField β x₁ (genPt C₁)
    (by rw [Category.comp_id, hβ]) hTP₁
  have := hQ.2.1
  obtain ⟨i', hi', hab⟩ := UpperTheory.abelian_quotient_inherits_action (𝓞 E) _ C₁ G₁ B hG₁ hB i₁ X u₁ qB hu₁ (isKer_of_isQuot hQ) hTPg
  obtain ⟨hepi, ⟨eL⟩⟩ := UpperTheory.lie_quotient_kernel_torus C₁ G₁ B X u₁ qB hsm₁ hQ hgc
  refine ⟨C₁, inferInstance, hC₁i, π₁ ≫ π₀, isSmoothProjCurve_of_isCurve hC₁,
    ⟨inferInstance, inferInstance, by rw [Category.assoc, hπ₀, hπ₁]⟩, G₁, inferInstance, hG₁, i₁, _,
    hact₁.comp hact₀, B, inferInstance, hB, i', qB, hQ.2.1, hi', hepi, ⟨_, ⟨eL ≪≫
      (isFrame_dlogChar C₁ (Module.finBasis ℤ X)).dual.iso (isFrame_freeFrame C₁ _)⟩⟩, hab⟩

end GlobalTheory.TorusPart

end TorusPartProof

/- English proof (translation)
The claim follows from `GlobalTheory.TorusPart.main`.
-/
theorem _root_.GlobalTheory.T.exists_cover_semiabelian_polarization : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
  (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C],
  IsSmoothProjCurve k C → ∀ (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct (𝓞 E) G), PolGen (H.bar : 𝓞 E →+* 𝓞 E) i →
  ∃ (C₁ : Scheme.{0}) (_ : Algebra k Γ(C₁, ⊤)) (_ : IsIntegral C₁) (π : C₁ ⟶ C), IsSmoothProjCurve k C₁ ∧ IsCover k π ∧
    ∃ (G₁ : Over C₁) (_ : GrpObj G₁) (_ : IsSemiAbelian G₁) (i₁ : OAct (𝓞 E) G₁) (φ : G₁.left ⟶ G.left), IsActPull i₁ i π φ ∧
    ∃ (G' : Over C₁) (_ : GrpObj G') (_ : IsSemiAbelian G') (i' : OAct (𝓞 E) G') (ρ : G₁ ⟶ G') (_ : IsMonHom ρ),
      (∀ a, i₁.act a ≫ ρ = ρ ≫ i'.act a) ∧ Epi (lieMap ρ) ∧
      (∃ r : ℕ, Nonempty (kernel (lieMap ρ) ≅ GlobalTheory.QCoh.freeModule C₁ (Fin r))) ∧ AbGen (H.bar : 𝓞 E →+* 𝓞 E) i' :=
  GlobalTheory.TorusPart.main
