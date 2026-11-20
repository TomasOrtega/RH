import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricGenericPointStalkOfFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantGeometricGenericPointSpecDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFormallyUnramifiedOfEqAtClosedPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

/- English proof (translation)
Establish `h₀' : y₀ ≫ σ ≫ g = z₀ ≫ ℓ` using `by rw [reassoc_of% h₀, hs]`. Establish `: IsReduced (pullback (σ ≫ g) ℓ)` using `isReduced_of_isOpenImmersion (pullback.fst (σ ≫ g) ℓ)`. Establish `hd : IsDominant (pullback.lift y₀ z₀ h₀')`. Prove the components needed by the constructor for the conclusion. Establish `h1 : Dense (Set.range y₀)` using `y₀.denseRange`.

Establish `h2` using `h1.preimage (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.isOpenMap`. Use `h2.mono ?_` and prove the remaining obligations. Introduce and unpack `u ⟨t, ht⟩`. Use `⟨t, (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← ht, ← Scheme.Hom.comp_apply, pullback.lift_fst]`.

Establish `key : pullback.fst (σ ≫ g) ℓ ≫ σ = pullback.snd (σ ≫ g) ℓ ≫ s`. Use `ext_of_isDominant_of_isSeparated (s := g) ?_ (pullback.lift y₀ z₀ h₀') ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hs, pullback.condition]`. Rewrite using `[pullback.lift_fst_assoc, pullback.lift_snd_assoc, h₀]`. Use `pullback.lift y z h ≫= key` as an intermediate fact.

Rewrite `this` using `[pullback.lift_fst_assoc, pullback.lift_snd_assoc]`. Then use the resulting hypothesis.
-/
theorem eq_section_of_isDominant {D G X' V Y₀ Y : Scheme.{0}} [IsReduced D] (g : G ⟶ X') [IsSeparated g]
    (ℓ : V ⟶ X') [IsOpenImmersion ℓ] (σ : D ⟶ G) (s : V ⟶ G) (hs : s ≫ g = ℓ) (y₀ : Y₀ ⟶ D) [IsDominant y₀]
    (z₀ : Y₀ ⟶ V) (h₀ : y₀ ≫ σ = z₀ ≫ s) (y : Y ⟶ D) (z : Y ⟶ V) (h : y ≫ σ ≫ g = z ≫ ℓ) :
    y ≫ σ = z ≫ s := by
  have h₀' : y₀ ≫ σ ≫ g = z₀ ≫ ℓ := by rw [reassoc_of% h₀, hs]
  have : IsReduced (pullback (σ ≫ g) ℓ) := isReduced_of_isOpenImmersion (pullback.fst (σ ≫ g) ℓ)
  have hd : IsDominant (pullback.lift y₀ z₀ h₀') := by
    constructor
    have h1 : Dense (Set.range y₀) := y₀.denseRange
    have h2 := h1.preimage (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.isOpenMap
    refine h2.mono ?_
    rintro u ⟨t, ht⟩
    refine ⟨t, (pullback.fst (σ ≫ g) ℓ).isOpenEmbedding.injective ?_⟩
    rw [← ht, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  have key : pullback.fst (σ ≫ g) ℓ ≫ σ = pullback.snd (σ ≫ g) ℓ ≫ s := by
    refine ext_of_isDominant_of_isSeparated (s := g) ?_ (pullback.lift y₀ z₀ h₀') ?_
    · rw [Category.assoc, Category.assoc, hs, pullback.condition]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, h₀]
  have := pullback.lift y z h ≫= key
  rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this

/- English proof (translation)
Take `rfl : x = IsLocalRing.closedPoint K` from `Subsingleton.elim _ _`. Establish `hι : torsion.ι G n ≫ mulN G n = 1`. Rewrite using `[Hom.one_def]`. Conclude with `pullback.condition.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))`. Establish `h0 : (MonObj.one : 𝟙_ (Over X') ⟶ G) ≫ mulN G n = (MonObj.one : 𝟙_ (Over X') ⟶ G)`.

Establish `e : (MonObj.one : 𝟙_ (Over X') ⟶ G) = 1`. Rewrite using `[Hom.one_def]`. Conclude with `(Category.id_comp _).symm.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))`. Rewrite using `[GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, e, one_pow]`. Take `⟨u₁, hu₁⟩` from `exists_lift_torsion n (torsion.ι G n ≫ a) (by rw [Category.assoc, ha, ← Category.assoc, hι, MonObj.one_comp])`.

Take `⟨u₂, hu₂⟩` from `exists_lift_torsion n (1 : torsion G n ⟶ G) (by rw [Hom.one_def, Category.assoc, h0])`. Establish `e₁ : u₁.left ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ a.left` using `congrArg (·.left) hu₁`. Establish `e₂ : u₂.left ≫ (torsion.ι G n).left = (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left`. Use `congrArg (·.left) hu₂` as an intermediate fact. Simplify using `only [Hom.one_def, Over.comp_left] at this`.

Rewrite using `[this]`. Use `congr 1`. Use `mono_torsion_ι G n` as an intermediate fact. Establish `key : (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₁.left = (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₂.left`. Use `GlobalTheory.T.eq_of_formallyUnramified_of_eq_at_closedPoint (torsion G n).hom _ _ _ ?_ K (Spec.map (Scheme.stalkClosedPointTo P)) ?_ ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, Category.assoc, Over.w, Over.w]`. Introduce `x`. Take `rfl : x = IsLocalRing.closedPoint K` from `Subsingleton.elim _ _`. Conclude with `IsLocalRing.comap_closedPoint (Scheme.stalkClosedPointTo P).hom`. Rewrite using `[← Category.assoc, ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, ← cancel_mono (torsion.ι G n).left, Category.assoc, Category.assoc, e₁, e₂, hP]`.

Rewrite using `[← e₁, ← e₂, reassoc_of% key]`.
-/
theorem fromSpecStalk_killed {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) [Etale (torsion G n).hom]
    (a : G ⟶ G) [IsMonHom a] (ha : a ≫ mulN G n = mulN G n ≫ a)
    (K : Type) [Field K] (P : Sp K ⟶ (torsion G n).left)
    (hP : P ≫ (torsion.ι G n).left ≫ a.left =
      P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K) :
    (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left ≫ a.left =
      (torsion G n).left.fromSpecStalk (P x) ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
  obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  have hι : torsion.ι G n ≫ mulN G n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))
  have h0 : (MonObj.one : 𝟙_ (Over X') ⟶ G) ≫ mulN G n = (MonObj.one : 𝟙_ (Over X') ⟶ G) := by
    have e : (MonObj.one : 𝟙_ (Over X') ⟶ G) = 1 := by
      rw [Hom.one_def]
      exact (Category.id_comp _).symm.trans (congrArg (· ≫ _) (CartesianMonoidalCategory.toUnit_unique _ _))
    rw [GlobalTheory.GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, e, one_pow]
  obtain ⟨u₁, hu₁⟩ := exists_lift_torsion n (torsion.ι G n ≫ a)
    (by rw [Category.assoc, ha, ← Category.assoc, hι, MonObj.one_comp])
  obtain ⟨u₂, hu₂⟩ := exists_lift_torsion n (1 : torsion G n ⟶ G)
    (by rw [Hom.one_def, Category.assoc, h0])
  have e₁ : u₁.left ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ a.left := congrArg (·.left) hu₁
  have e₂ : u₂.left ≫ (torsion.ι G n).left = (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left := by
    have := congrArg (·.left) hu₂
    simp only [Hom.one_def, Over.comp_left] at this
    rw [this]
    congr 1
  have := mono_torsion_ι G n
  have key : (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₁.left =
      (torsion G n).left.fromSpecStalk (P (IsLocalRing.closedPoint K)) ≫ u₂.left := by
    refine GlobalTheory.T.eq_of_formallyUnramified_of_eq_at_closedPoint (torsion G n).hom _ _ _ ?_ K (Spec.map (Scheme.stalkClosedPointTo P)) ?_ ?_
    · rw [Category.assoc, Category.assoc, Over.w, Over.w]
    · intro x
      obtain rfl : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      exact IsLocalRing.comap_closedPoint (Scheme.stalkClosedPointTo P).hom
    · rw [← Category.assoc, ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
        ← cancel_mono (torsion.ι G n).left, Category.assoc, Category.assoc, e₁, e₂, hP]
  rw [← e₁, ← e₂, reassoc_of% key]

/- English proof (translation)
Introduce `E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ act I hex K _ _ P hP x`. Use `GlobalTheory.GrpTangent.etale_torsion G hn` as an intermediate fact. Use `isDomain_stalk_of_etale (torsion G n).hom (P x)` as an intermediate fact. Take `⟨Ω, _, _, y₀, hy₀, _⟩` from `GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain ((torsion G n).left.presheaf.stalk (P x))`. Take `⟨z₀, hz₀⟩` from `GlobalTheory.T.exists_lift_geometricGenericPoint_stalk_of_flat (torsion G n).hom (P x) ℓ Ω y₀ hy₀`.

Establish `hw' : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom` using `Over.w _`. Take `⟨c, hc⟩` from `hex Ω z₀ (y₀ ≫ (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left) (by rw [Category.assoc, Category.assoc, hw', hz₀]) (fun a ha => by`. Use `act.hom a` as an intermediate fact. Establish `h` using `fromSpecStalk_killed G n (act.act a) (by rw [← act_natCast act, ← act.mul, ← act.mul, mul_comm]) K P (hP a ha) x`. Simplify using `only [Category.assoc]`.

Rewrite using `[h, reassoc_of% hw'])`. Use `⟨c, fun Ω' _ _ y z h => ?_⟩` and prove the remaining obligations. Conclude with `eq_section_of_isDominant G.hom ℓ _ (w c) (hw c) y₀ z₀ hc y z (by rw [Category.assoc, hw', h])`.
-/
theorem exists_valAt : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [IsSeparated G.hom] (act : OAct (𝓞 E) G) (I : Ideal (𝓞 E))
    (hex : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (P : Sp Ω ⟶ G.left), P ≫ G.hom = x ≫ ℓ →
      (∀ a ∈ I, P ≫ (act.act a).left = P ≫ G.hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) → ∃ c, P = x ≫ w c)
    (K : Type) [Field K] [IsAlgClosed K] (P : Sp K ⟶ (torsion G n).left)
    (hP : ∀ a ∈ I, P ≫ (torsion.ι G n).left ≫ (act.act a).left = P ≫ (torsion G n).hom ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G).left) (x : Sp K), ∃ c, GlobalTheory.TorsSpec.ValAt G n ℓ w (P x) c := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ act I hex K _ _ P hP x
  have := GlobalTheory.GrpTangent.etale_torsion G hn
  have := isDomain_stalk_of_etale (torsion G n).hom (P x)
  obtain ⟨Ω, _, _, y₀, hy₀, _⟩ := GlobalTheory.T.exists_dominant_geometricGenericPoint_spec_domain ((torsion G n).left.presheaf.stalk (P x))
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.T.exists_lift_geometricGenericPoint_stalk_of_flat (torsion G n).hom (P x) ℓ Ω y₀ hy₀
  have hw' : (torsion.ι G n).left ≫ G.hom = (torsion G n).hom := Over.w _
  obtain ⟨c, hc⟩ := hex Ω z₀ (y₀ ≫ (torsion G n).left.fromSpecStalk (P x) ≫ (torsion.ι G n).left)
    (by rw [Category.assoc, Category.assoc, hw', hz₀]) (fun a ha => by
      have := act.hom a
      have h := fromSpecStalk_killed G n (act.act a)
        (by rw [← act_natCast act, ← act.mul, ← act.mul, mul_comm]) K P (hP a ha) x
      simp only [Category.assoc]
      rw [h, reassoc_of% hw'])
  refine ⟨c, fun Ω' _ _ y z h => ?_⟩
  exact eq_section_of_isDominant G.hom ℓ _ (w c) (hw c) y₀ z₀ hc y z (by rw [Category.assoc, hw', h])

end GlobalTheory.TorsSpec
