import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.NormalFiniteLift

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FiniteSectionLift.lift_of_finite`. Consider the case `exact _root_.GlobalTheory.FiniteSectionLift.lift_of_finite`. Consider the case `(apply _root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FiniteSectionLift.lift_of_finite ..)`.
-/
theorem finite_lift_of_integral (R K : CommRingCat.{0}) (φ : R ⟶ K) (hinj : Function.Injective φ.hom)
    (H : ∀ x : K, φ.hom.IsIntegralElem x → ∃ r : R, φ.hom r = x)
    (Z P : Scheme.{0}) (p : Z ⟶ P) (ξ₀ : Spec R ⟶ P) (y : Spec K ⟶ Z)
    (hp : IsFinite p) (hy : y ≫ p = Spec.map φ ≫ ξ₀) :
    ∃ ξ : Spec R ⟶ Z, Spec.map φ ≫ ξ = y ∧ ξ ≫ p = ξ₀ := by
  first
  | exact @_root_.GlobalTheory.FiniteSectionLift.lift_of_finite
  | exact _root_.GlobalTheory.FiniteSectionLift.lift_of_finite
  | (apply _root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteSectionLift.lift_of_finite <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteSectionLift.lift_of_finite ..)

/- English proof (translation)
Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[DenseRange, dense_iff_inter_open]`. Introduce and unpack `O hO ⟨t, ht⟩`. Take `⟨t', ht', e⟩ : genericPoint S ∈ r '' O` from `((genericPoint_spec S).mem_open_set_iff (r.isOpenEmbedding.isOpenMap O hO)).2 ⟨r t, Set.mem_univ _, t, ht, rfl⟩`. Use `⟨w (IsLocalRing.closedPoint K), ?_, ⟨_, rfl⟩⟩` and prove the remaining obligations.

Rewrite using `[← r.isOpenEmbedding.injective (e.trans hw.symm)]`. Conclude with `ht'`.
-/
theorem isDominant_of_generic {T S : Scheme.{0}} [IsIntegral S] (r : T ⟶ S) [IsOpenImmersion r]
    (K : CommRingCat.{0}) [IsLocalRing K] (w : Spec K ⟶ T)
    (hw : r (w (IsLocalRing.closedPoint K)) = genericPoint S) : IsDominant w := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_inter_open]
  rintro O hO ⟨t, ht⟩
  obtain ⟨t', ht', e⟩ : genericPoint S ∈ r '' O :=
    ((genericPoint_spec S).mem_open_set_iff (r.isOpenEmbedding.isOpenMap O hO)).2 ⟨r t, Set.mem_univ _, t, ht, rfl⟩
  refine ⟨w (IsLocalRing.closedPoint K), ?_, ⟨_, rfl⟩⟩
  rw [← r.isOpenEmbedding.injective (e.trans hw.symm)]
  exact ht'

end GlobalTheory.NormalFiniteLift

namespace GlobalTheory.NormalFiniteLift

/- English proof (translation)
Introduce `o _ N S' X Z U c i p h _ hN _ hU _ hp _ _ e`. Use `GlobalTheory.IsNormalScheme.of_pred hN` as an intermediate fact. Establish `hη : ∀ V : S'.Opens, (V : Set S').Nonempty → genericPoint S' ∈ V` using `fun V hV => ((genericPoint_spec S').mem_open_set_iff V.isOpen).2 (by simpa using hV)`. Establish `hηU : genericPoint S' ∈ U` using `hη U hU.nonempty`. Set `gS : Spec S'.functionField ⟶ S'` to `S'.fromSpecStalk (genericPoint S')`.

Establish `hgS : gS (IsLocalRing.closedPoint S'.functionField) = genericPoint S'` using `Scheme.fromSpecStalk_closedPoint`. Establish `hrO : ∀ O : S'.Opens, genericPoint S' ∈ O → Set.range gS ⊆ Set.range O.ι`. Introduce and unpack `O hO _ ⟨q, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Establish `: gS q ⤳ genericPoint S'` using `(S'.range_fromSpecStalk (x := genericPoint S')).le ⟨q, rfl⟩`.

Conclude with `this.mem_open O.isOpen hO`. Set `gO : ∀ O : S'.Opens, genericPoint S' ∈ O → (Spec S'.functionField ⟶ O.toScheme)` to `fun O hO => IsOpenImmersion.lift O.ι gS (hrO O hO)`. Establish `hgO : ∀ O hO, gO O hO ≫ O.ι = gS` using `fun O hO => IsOpenImmersion.lift_fac _ _ _`. Set `y : Spec S'.functionField ⟶ Z` to `gO U hηU ≫ c ≫ i`. Establish `hy : y ≫ p = gS ≫ h`.

Simplify using `only [y, Category.assoc, ← e]`. Rewrite using `[← Category.assoc, hgO U hηU]`. Establish `loc : ∀ (V : S'.Opens) (hV : IsAffineOpen V) (hηV : genericPoint S' ∈ V), ∃ m : V.toScheme ⟶ Z, m ≫ p = V.ι ≫ h ∧ gO V hηV ≫ m = y`. Introduce `V hV hηV`. Establish `: Nonempty V` using `⟨⟨_, hηV⟩⟩`.

Establish `: IsIntegrallyClosed Γ(S', V)` using `GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hV`. Establish `: IsFractionRing Γ(S', V) S'.functionField` using `functionField_isFractionRing_of_isAffineOpen S' V hV`. Establish `hsp : Spec.map (S'.germToFunctionField V) ≫ hV.fromSpec = gS` using `hV.fromSpecStalk_eq_fromSpecStalk hηV`. Take `⟨ξ, h1, h2⟩` from `finite_lift_of_integral Γ(S', V) S'.functionField (S'.germToFunctionField V) (S'.germToFunctionField_injective V) (fun x hx => IsIntegrallyClosed.isIntegral_iff.1 hx) Z _ p (hV.fromSpec ≫ h) y hp (by rw [hy, ← Category.assoc, hsp])`. Establish `hg : gO V hηV ≫ hV.isoSpec.hom = Spec.map (S'.germToFunctionField V)`.

Rewrite using `[← cancel_mono hV.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, hgO V hηV, hsp]`. Use `⟨hV.isoSpec.hom ≫ ξ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, h2, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]`. Rewrite using `[← Category.assoc, hg, h1]`. Use `choose V hVa hxV _ using fun x : S' => exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := x) (by simp)`.

Establish `hcov : TopologicalSpace.IsOpenCover V` using `eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩`. Establish `hηV : ∀ x, genericPoint S' ∈ V x` using `fun x => hη (V x) ⟨x, hxV x⟩`. Use `choose m hm hmy using fun x => loc (V x) (hVa x) (hηV x)`. Set `𝒰` to `S'.openCoverOfIsOpenCover V hcov`. Establish `hc : ∀ a b, pullback.fst (V a).ι (V b).ι ≫ m a = pullback.snd (V a).ι (V b).ι ≫ m b`.

Introduce `a b`. Set `r` to `pullback.fst (V a).ι (V b).ι ≫ (V a).ι`. Establish `: IsReduced (pullback (V a).ι (V b).ι)` using `isReduced_of_isOpenImmersion r`. Set `w : Spec S'.functionField ⟶ pullback (V a).ι (V b).ι` to `pullback.lift (gO (V a) (hηV a)) (gO (V b) (hηV b)) ((hgO (V a) (hηV a)).trans (hgO (V b) (hηV b)).symm)`. Establish `: IsDominant w` using `isDominant_of_generic r _ w (by show (w ≫ pullback.fst _ _ ≫ (V a).ι) (IsLocalRing.closedPoint _) = _`.

Rewrite using `[pullback.lift_fst_assoc, hgO (V a) (hηV a)]`. Conclude with `hgS)`. Use `ext_of_isDominant_of_isSeparated p ?_ w ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hm, hm, pullback.condition_assoc]`. Rewrite using `[pullback.lift_fst_assoc, pullback.lift_snd_assoc, hmy, hmy]`.

Establish `hg : ∀ a, (V a).ι ≫ 𝒰.glueMorphisms m hc = m a` using `fun a => 𝒰.ι_glueMorphisms m hc a`. Set `π` to `𝒰.glueMorphisms m hc`. Establish `hπp : π ≫ p = h` using `𝒰.hom_ext _ _ fun a => ((reassoc_of% hg a) p).trans (hm a)`. Use `⟨π, ?_, hπp⟩` and prove the remaining obligations. Establish `: IsReduced U.toScheme` using `isReduced_of_isOpenImmersion U.ι`.

Establish `: IsDominant (gO U hηU)` using `isDominant_of_generic U.ι _ _ (by show (gO U hηU ≫ U.ι) (IsLocalRing.closedPoint _) = _`. Rewrite using `[hgO U hηU]`. Conclude with `hgS)`. Use `ext_of_isDominant_of_isSeparated p ?_ (gO U hηU) ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hπp, e]`.

Simplify using `only [Category.assoc]`. Set `x` to `genericPoint S'`. Rewrite using `[← Category.assoc, hgO U hηU, ← hgO (V x) (hηV x), Category.assoc, hg, hmy]`.
-/
theorem exists_lift_of_finite : ∀ (o : Type) [CommRing o] (N : ℕ) (S' X Z : Scheme.{0}) (U : S'.Opens)
    (c : U.toScheme ⟶ X) (i : X ⟶ Z) (p : Z ⟶ PSpace o N) (h : S' ⟶ PSpace o N), IsIntegral S' →
    Geo.Tor.IsNormalScheme S' → IsIntegral Z → Dense (U : Set S') → IsDominant c → IsFinite p →
    IsOpenImmersion i → Dense (Set.range i) → U.ι ≫ h = c ≫ i ≫ p →
    ∃ π : S' ⟶ Z, U.ι ≫ π = c ≫ i ∧ π ≫ p = h := by
  intro o _ N S' X Z U c i p h _ hN _ hU _ hp _ _ e
  have := GlobalTheory.IsNormalScheme.of_pred hN
  have hη : ∀ V : S'.Opens, (V : Set S').Nonempty → genericPoint S' ∈ V := fun V hV =>
    ((genericPoint_spec S').mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hηU : genericPoint S' ∈ U := hη U hU.nonempty
  let gS : Spec S'.functionField ⟶ S' := S'.fromSpecStalk (genericPoint S')
  have hgS : gS (IsLocalRing.closedPoint S'.functionField) = genericPoint S' := Scheme.fromSpecStalk_closedPoint
  have hrO : ∀ O : S'.Opens, genericPoint S' ∈ O → Set.range gS ⊆ Set.range O.ι := by
    rintro O hO _ ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : gS q ⤳ genericPoint S' := (S'.range_fromSpecStalk (x := genericPoint S')).le ⟨q, rfl⟩
    exact this.mem_open O.isOpen hO
  let gO : ∀ O : S'.Opens, genericPoint S' ∈ O → (Spec S'.functionField ⟶ O.toScheme) := fun O hO =>
    IsOpenImmersion.lift O.ι gS (hrO O hO)
  have hgO : ∀ O hO, gO O hO ≫ O.ι = gS := fun O hO => IsOpenImmersion.lift_fac _ _ _
  let y : Spec S'.functionField ⟶ Z := gO U hηU ≫ c ≫ i
  have hy : y ≫ p = gS ≫ h := by
    simp only [y, Category.assoc, ← e]
    rw [← Category.assoc, hgO U hηU]

  have loc : ∀ (V : S'.Opens) (hV : IsAffineOpen V) (hηV : genericPoint S' ∈ V),
      ∃ m : V.toScheme ⟶ Z, m ≫ p = V.ι ≫ h ∧ gO V hηV ≫ m = y := by
    intro V hV hηV
    have : Nonempty V := ⟨⟨_, hηV⟩⟩
    have : IsIntegrallyClosed Γ(S', V) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hV
    have : IsFractionRing Γ(S', V) S'.functionField := functionField_isFractionRing_of_isAffineOpen S' V hV
    have hsp : Spec.map (S'.germToFunctionField V) ≫ hV.fromSpec = gS :=
      hV.fromSpecStalk_eq_fromSpecStalk hηV
    obtain ⟨ξ, h1, h2⟩ := finite_lift_of_integral Γ(S', V) S'.functionField (S'.germToFunctionField V)
      (S'.germToFunctionField_injective V) (fun x hx => IsIntegrallyClosed.isIntegral_iff.1 hx) Z _ p
      (hV.fromSpec ≫ h) y hp (by rw [hy, ← Category.assoc, hsp])
    have hg : gO V hηV ≫ hV.isoSpec.hom = Spec.map (S'.germToFunctionField V) := by
      rw [← cancel_mono hV.fromSpec, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec, hgO V hηV, hsp]
    refine ⟨hV.isoSpec.hom ≫ ξ, ?_, ?_⟩
    · rw [Category.assoc, h2, ← Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
    · rw [← Category.assoc, hg, h1]

  choose V hVa hxV _ using fun x : S' => exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := x) (by simp)
  have hcov : TopologicalSpace.IsOpenCover V := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxV x⟩
  have hηV : ∀ x, genericPoint S' ∈ V x := fun x => hη (V x) ⟨x, hxV x⟩
  choose m hm hmy using fun x => loc (V x) (hVa x) (hηV x)
  let 𝒰 := S'.openCoverOfIsOpenCover V hcov
  have hc : ∀ a b, pullback.fst (V a).ι (V b).ι ≫ m a = pullback.snd (V a).ι (V b).ι ≫ m b := by
    intro a b
    let r := pullback.fst (V a).ι (V b).ι ≫ (V a).ι
    have : IsReduced (pullback (V a).ι (V b).ι) := isReduced_of_isOpenImmersion r
    let w : Spec S'.functionField ⟶ pullback (V a).ι (V b).ι :=
      pullback.lift (gO (V a) (hηV a)) (gO (V b) (hηV b)) ((hgO (V a) (hηV a)).trans (hgO (V b) (hηV b)).symm)
    have : IsDominant w := isDominant_of_generic r _ w (by
      show (w ≫ pullback.fst _ _ ≫ (V a).ι) (IsLocalRing.closedPoint _) = _
      rw [pullback.lift_fst_assoc, hgO (V a) (hηV a)]; exact hgS)
    refine ext_of_isDominant_of_isSeparated p ?_ w ?_
    · rw [Category.assoc, Category.assoc, hm, hm, pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hmy, hmy]
  have hg : ∀ a, (V a).ι ≫ 𝒰.glueMorphisms m hc = m a := fun a => 𝒰.ι_glueMorphisms m hc a
  let π := 𝒰.glueMorphisms m hc
  have hπp : π ≫ p = h := 𝒰.hom_ext _ _ fun a => ((reassoc_of% hg a) p).trans (hm a)
  refine ⟨π, ?_, hπp⟩
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : IsDominant (gO U hηU) := isDominant_of_generic U.ι _ _ (by
    show (gO U hηU ≫ U.ι) (IsLocalRing.closedPoint _) = _
    rw [hgO U hηU]; exact hgS)
  refine ext_of_isDominant_of_isSeparated p ?_ (gO U hηU) ?_
  · rw [Category.assoc, hπp, e]; simp only [Category.assoc]
  · let x := genericPoint S'
    rw [← Category.assoc, hgO U hηU, ← hgO (V x) (hηV x), Category.assoc, hg, hmy]
end GlobalTheory.NormalFiniteLift
