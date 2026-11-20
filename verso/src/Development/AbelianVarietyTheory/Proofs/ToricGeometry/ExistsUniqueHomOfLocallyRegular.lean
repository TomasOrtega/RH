import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace PointwiseRegular

/- English proof (translation)
Use `Scheme.hom_ext_of_forall _ _ fun z => ?_` and prove the remaining obligations. Take `⟨_, ⟨D, hD, rfl⟩, hz, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f z)) isOpen_univ`. Establish `hle : f ⁻¹ᵁ D ≤ g ⁻¹ᵁ D` using `ComplexPoints.opens_le_of_complexPoints p _ _ fun y hy hyD => by`. Rewrite `hyD`, the goal using `[← top_le_preimage_comp]`. Rewrite using `[← h y hy]` and apply the resulting hypothesis.

Use `⟨f ⁻¹ᵁ D, hz, ?_⟩` and prove the remaining obligations. Establish `: IsAffine (Scheme.Opens.toScheme (X` using `X) D) := hD`. Establish `key : f.resLE D (f ⁻¹ᵁ D) le_rfl = g.resLE D (f ⁻¹ᵁ D) hle`. Use `ComplexPoints.hom_ext_of_points ((f ⁻¹ᵁ D).ι ≫ p) (terminal.from _) (terminal.hom_ext _ _) fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← cancel_mono (Scheme.Opens.ι (X := X) D), Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι, ← Category.assoc, ← Category.assoc]`.

Conclude with `h _ (by rw [Category.assoc]; exact hx)`. Rewrite using `[← Scheme.Hom.resLE_comp_ι f le_rfl, key, Scheme.Hom.resLE_comp_ι]`.
-/
theorem hom_ext {X Y : Scheme.{0}} (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] [IsReduced Y] {f g : Y ⟶ X}
    (h : ∀ y : Sp ℂ ⟶ Y, y ≫ p = 𝟙 _ → y ≫ f = y ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall _ _ fun z => ?_
  obtain ⟨_, ⟨D, hD, rfl⟩, hz, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f z)) isOpen_univ
  have hle : f ⁻¹ᵁ D ≤ g ⁻¹ᵁ D := ComplexPoints.opens_le_of_complexPoints p _ _ fun y hy hyD => by
    rw [← top_le_preimage_comp] at hyD ⊢
    rwa [← h y hy]
  refine ⟨f ⁻¹ᵁ D, hz, ?_⟩
  have : IsAffine (Scheme.Opens.toScheme (X := X) D) := hD
  have key : f.resLE D (f ⁻¹ᵁ D) le_rfl = g.resLE D (f ⁻¹ᵁ D) hle := by
    refine ComplexPoints.hom_ext_of_points ((f ⁻¹ᵁ D).ι ≫ p) (terminal.from _) (terminal.hom_ext _ _) fun x hx => ?_
    rw [← cancel_mono (Scheme.Opens.ι (X := X) D), Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, ← Category.assoc]
    exact h _ (by rw [Category.assoc]; exact hx)
  rw [← Scheme.Hom.resLE_comp_ι f le_rfl, key, Scheme.Hom.resLE_comp_ι]

def ofRingHom {X Y : Scheme.{0}} (U : Y.Opens) {D : X.Opens} (hD : IsAffineOpen D) (r : Γ(X, D) →+* Γ(Y, U)) :
    U.toScheme ⟶ X :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom r) ≫ hD.fromSpec

/- English proof (translation)
Rewrite using `[top_le_preimage_comp]`. Simplify using the standard rewrite rules.
-/
theorem top_le_preimage_ι {Y : Scheme.{0}} (U : Y.Opens) (y : Sp ℂ ⟶ U.toScheme) : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := by
  rw [top_le_preimage_comp]
  simp

/- English proof (translation)
Establish `hy` using `top_le_preimage_ι U y`. Establish `e1 : CommRingCat.ofHom r ≫ (y ≫ U.ι).appLE U ⊤ hy = x.appLE D ⊤ hx`. Rewrite using `[← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]`. Use extensionality with `φ`. Use `h φ` as an intermediate fact.

Rewrite `this` using `[valAt'_eq_valAt _ hy, valAt'_eq_valAt _ hx]`. Conclude with `this`. Establish `e2 : (isAffineOpen_top (Sp ℂ)).fromSpec ≫ y ≫ U.toSpecΓ = Spec.map ((y ≫ U.ι).appLE U ⊤ hy)`. Rewrite using `[IsAffineOpen.fromSpec_top, Iso.inv_comp_eq, Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp]`. Use `congr 2`.

Rewrite using `[← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Establish `: IsIso (isAffineOpen_top (Sp ℂ)).fromSpec`. Rewrite using `[IsAffineOpen.fromSpec_top]`. Use `infer_instance`.

Rewrite using `[← cancel_epi (isAffineOpen_top (Sp ℂ)).fromSpec, ← hD.SpecMap_appLE_fromSpec x _ hx, ← e1, ofRingHom, reassoc_of% e2, Spec.map_comp_assoc]`.
-/
theorem comp_ofRingHom {X Y : Scheme.{0}} (U : Y.Opens) {D : X.Opens} (hD : IsAffineOpen D)
    (r : Γ(X, D) →+* Γ(Y, U)) (y : Sp ℂ ⟶ U.toScheme) (x : Sp ℂ ⟶ X) (hx : ⊤ ≤ x ⁻¹ᵁ D)
    (h : ∀ φ, valAt' (y ≫ U.ι) U (r φ) = valAt' x D φ) : y ≫ ofRingHom U hD r = x := by
  have hy := top_le_preimage_ι U y
  have e1 : CommRingCat.ofHom r ≫ (y ≫ U.ι).appLE U ⊤ hy = x.appLE D ⊤ hx := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    ext φ
    have := h φ
    rw [valAt'_eq_valAt _ hy, valAt'_eq_valAt _ hx] at this
    exact this
  have e2 : (isAffineOpen_top (Sp ℂ)).fromSpec ≫ y ≫ U.toSpecΓ = Spec.map ((y ≫ U.ι).appLE U ⊤ hy) := by
    rw [IsAffineOpen.fromSpec_top, Iso.inv_comp_eq, Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc,
      ← Spec.map_comp]
    congr 2
    rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  have : IsIso (isAffineOpen_top (Sp ℂ)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi (isAffineOpen_top (Sp ℂ)).fromSpec, ← hD.SpecMap_appLE_fromSpec x _ hx, ← e1, ofRingHom,
    reassoc_of% e2, Spec.map_comp_assoc]

/- English proof (translation)
Use `choose r hr using h`. Establish `ext : ∀ a b : Γ(Y.left, U), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U → valAt' y.left U a = valAt' y.left U b) → a = b` using `fun a b hab => ComplexPoints.eq_of_valAt'_eq Y.hom U a b fun x hx hU => hab (Over.homMk x hx) hU`. Use `⟨⟨⟨⟨r, ?_⟩, ?_⟩, ?_, ?_⟩, hr⟩` and prove the remaining obligations. Conclude with `ext _ _ fun y hy => by`. Rewrite using `[hr _ y hy]`.

Conclude with `(valAt'_one _ (hF y hy)).trans (valAt'_one _ hy).symm`. Conclude with `fun a b => ext _ _ fun y hy => by`. Use `(hr _ y hy).trans (((valAt'_mul _ _ _ _).trans ?_).trans (valAt'_mul _ _ _ _).symm)` and prove the remaining obligations. Rewrite using `[hr _ y hy, hr _ y hy]`. Conclude with `ext _ _ fun y hy => (hr _ y hy).trans ((valAt'_zero _ _).trans (valAt'_zero _ _).symm)`.

Conclude with `fun a b => ext _ _ fun y hy => by`. Use `(hr _ y hy).trans (((valAt'_add _ _ _ _).trans ?_).trans (valAt'_add _ _ _ _).symm)` and prove the remaining obligations. Conclude with `congrArg₂ (· + ·) (hr _ y hy).symm (hr _ y hy).symm`.
-/
theorem exists_ringHom {X Y : Over (Sp ℂ)} [IsReduced Y.left] [LocallyOfFiniteType Y.hom]
    (F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : Y.left.Opens) (D : X.left.Opens)
    (hF : ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U → ⊤ ≤ (F y).left ⁻¹ᵁ D)
    (h : ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U ρ = valAt' (F y).left D φ) :
    ∃ r : Γ(X.left, D) →+* Γ(Y.left, U), ∀ φ, ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U (r φ) = valAt' (F y).left D φ := by
  choose r hr using h
  have ext : ∀ a b : Γ(Y.left, U), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U a = valAt' y.left U b) → a = b := fun a b hab =>
    ComplexPoints.eq_of_valAt'_eq Y.hom U a b fun x hx hU => hab (Over.homMk x hx) hU
  refine ⟨⟨⟨⟨r, ?_⟩, ?_⟩, ?_, ?_⟩, hr⟩
  · exact ext _ _ fun y hy => by
      rw [hr _ y hy]; exact (valAt'_one _ (hF y hy)).trans (valAt'_one _ hy).symm
  · exact fun a b => ext _ _ fun y hy => by
      refine (hr _ y hy).trans (((valAt'_mul _ _ _ _).trans ?_).trans (valAt'_mul _ _ _ _).symm)
      rw [hr _ y hy, hr _ y hy]
  · exact ext _ _ fun y hy => (hr _ y hy).trans ((valAt'_zero _ _).trans (valAt'_zero _ _).symm)
  · exact fun a b => ext _ _ fun y hy => by
      refine (hr _ y hy).trans (((valAt'_add _ _ _ _).trans ?_).trans (valAt'_add _ _ _ _).symm)
      exact congrArg₂ (· + ·) (hr _ y hy).symm (hr _ y hy).symm

/- English proof (translation)
Use `choose U D hU hD hF hρ using h`. Establish `loc : ∀ i, ∃ m : (U i).toScheme ⟶ X.left, ∀ (z : Sp ℂ ⟶ (U i).toScheme) (y : 𝟙_ (Over (Sp ℂ)) ⟶ Y), y.left = z ≫ (U i).ι → z ≫ m = (F y).left` using `fun i => by`. Take `⟨r, hr⟩` from `exists_ringHom F (U i) (D i) (hF i) (hρ i)`. Use `⟨ofRingHom (U i) (hD i) r, fun z y hy => ?_⟩` and prove the remaining obligations. Establish `hyU : ⊤ ≤ y.left ⁻¹ᵁ U i` using `by rw [hy]; exact top_le_preimage_ι _ z`.

Use `comp_ofRingHom _ _ r z _ (hF i y hyU) fun φ => ?_` and prove the remaining obligations. Rewrite using `[← hr φ y hyU, hy]`. Use `choose m hm using loc`. Establish `hcov : TopologicalSpace.IsOpenCover U` using `ComplexPoints.iSup_eq_top_of_complexPoints Y.hom U fun x hx => ⟨Over.homMk x hx, hU _⟩`. Set `𝒰` to `Y.left.openCoverOfIsOpenCover U hcov`.

Establish `hc : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ m i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ m j` using `fun i j => by`. Establish `: IsReduced (pullback (𝒰.f i) (𝒰.f j))` using `isReduced_of_isOpenImmersion (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)`. Use `hom_ext ((pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) ≫ Y.hom) fun z hz => ?_` and prove the remaining obligations. Set `y : 𝟙_ (Over (Sp ℂ)) ⟶ Y` to `Over.homMk (z ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) ((Category.assoc _ _ _).trans hz)`. Use `(Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))` and prove the remaining obligations.

Use `(hm i _ y (Category.assoc _ _ _).symm).trans (hm j _ y ?_).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `z ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i = (z ≫ pullback.snd (𝒰.f i) (𝒰.f j)) ≫ 𝒰.f j`. Rewrite using `[pullback.condition, Category.assoc]`. Establish `hg : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ Y, y.left ≫ 𝒰.glueMorphisms m hc = (F y).left` using `fun y => by`. Establish `hr : Set.range y.left ⊆ Set.range (U y).ι`.

Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hU y (Set.mem_univ a)`. Establish `e` using `IsOpenImmersion.lift_fac (U y).ι y.left hr`. Establish `e2 : (U y).ι ≫ 𝒰.glueMorphisms m hc = m y` using `𝒰.ι_glueMorphisms m hc y`.

Use `Eq.trans ?_ (hm y _ y e.symm)` and prove the remaining obligations. Rewrite using `[← e2, ← Category.assoc, e]`. Establish `hw : 𝒰.glueMorphisms m hc ≫ X.hom = Y.hom`. Use `hom_ext Y.hom fun z hz => ?_` and prove the remaining obligations. Use `hg (Over.homMk z hz)` as an intermediate fact.

Rewrite using `[hz, ← Category.assoc]`. Conclude with `(congrArg (· ≫ X.hom) this).trans (Over.w (F _))`. Use `⟨Over.homMk _ hw, fun y => Over.OverMorphism.ext (hg y), fun m' hm' => Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Use `hom_ext Y.hom fun z hz => ?_` and prove the remaining obligations. Conclude with `(congrArg (fun φ => φ.left) (hm' (Over.homMk z hz))).trans (hg (Over.homMk z hz)).symm`.
-/
theorem existsUnique_hom {X Y : Over (Sp ℂ)} [IsReduced Y.left] [LocallyOfFiniteType Y.hom]
    (F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (h : ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ y.left ⁻¹ᵁ U ∧ IsAffineOpen D ∧
      (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y'.left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧
      ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y'.left ⁻¹ᵁ U →
        valAt' y'.left U ρ = valAt' (F y').left D φ) :
    ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y := by
  choose U D hU hD hF hρ using h
  have loc : ∀ i, ∃ m : (U i).toScheme ⟶ X.left, ∀ (z : Sp ℂ ⟶ (U i).toScheme) (y : 𝟙_ (Over (Sp ℂ)) ⟶ Y),
      y.left = z ≫ (U i).ι → z ≫ m = (F y).left := fun i => by
    obtain ⟨r, hr⟩ := exists_ringHom F (U i) (D i) (hF i) (hρ i)
    refine ⟨ofRingHom (U i) (hD i) r, fun z y hy => ?_⟩
    have hyU : ⊤ ≤ y.left ⁻¹ᵁ U i := by rw [hy]; exact top_le_preimage_ι _ z
    refine comp_ofRingHom _ _ r z _ (hF i y hyU) fun φ => ?_
    rw [← hr φ y hyU, hy]
  choose m hm using loc
  have hcov : TopologicalSpace.IsOpenCover U :=
    ComplexPoints.iSup_eq_top_of_complexPoints Y.hom U fun x hx => ⟨Over.homMk x hx, hU _⟩
  let 𝒰 := Y.left.openCoverOfIsOpenCover U hcov
  have hc : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ m i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ m j := fun i j => by
    have : IsReduced (pullback (𝒰.f i) (𝒰.f j)) :=
      isReduced_of_isOpenImmersion (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
    refine hom_ext ((pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) ≫ Y.hom) fun z hz => ?_
    let y : 𝟙_ (Over (Sp ℂ)) ⟶ Y := Over.homMk (z ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i)
      ((Category.assoc _ _ _).trans hz)
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ (Category.assoc _ _ _))
    refine (hm i _ y (Category.assoc _ _ _).symm).trans (hm j _ y ?_).symm
    change z ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i = (z ≫ pullback.snd (𝒰.f i) (𝒰.f j)) ≫ 𝒰.f j
    rw [pullback.condition, Category.assoc]
  have hg : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ Y, y.left ≫ 𝒰.glueMorphisms m hc = (F y).left := fun y => by
    have hr : Set.range y.left ⊆ Set.range (U y).ι := by
      rintro _ ⟨a, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hU y (Set.mem_univ a)
    have e := IsOpenImmersion.lift_fac (U y).ι y.left hr
    have e2 : (U y).ι ≫ 𝒰.glueMorphisms m hc = m y := 𝒰.ι_glueMorphisms m hc y
    refine Eq.trans ?_ (hm y _ y e.symm)
    rw [← e2, ← Category.assoc, e]
  have hw : 𝒰.glueMorphisms m hc ≫ X.hom = Y.hom := by
    refine hom_ext Y.hom fun z hz => ?_
    have := hg (Over.homMk z hz)
    rw [hz, ← Category.assoc]
    exact (congrArg (· ≫ X.hom) this).trans (Over.w (F _))
  refine ⟨Over.homMk _ hw, fun y => Over.OverMorphism.ext (hg y), fun m' hm' => Over.OverMorphism.ext ?_⟩
  refine hom_ext Y.hom fun z hz => ?_
  exact (congrArg (fun φ => φ.left) (hm' (Over.homMk z hz))).trans (hg (Over.homMk z hz)).symm

end PointwiseRegular

/- English proof (translation)
Introduce `_ _ _ _ _ _ F h` and use `PointwiseRegular.existsUnique_hom F h`.
-/
theorem existsUnique_hom_of_locally_regular : (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X Y : Over (Sp ℂ)), IsReduced Y.left → LocallyOfFiniteType Y.hom → ∀ F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ∃ (U : Y.left.Opens) (D : X.left.Opens), ⊤ ≤ (y).left ⁻¹ᵁ U ∧ IsAffineOpen D ∧ (∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → ⊤ ≤ (F y').left ⁻¹ᵁ D) ∧ ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y' : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ (y').left ⁻¹ᵁ U → valAt' y'.left U ρ = valAt' (F y').left D φ) → ∃! m : Y ⟶ X, ∀ y, y ≫ m = F y) :=
  fun _ _ _ _ _ _ F h => PointwiseRegular.existsUnique_hom F h

end GlobalTheory
