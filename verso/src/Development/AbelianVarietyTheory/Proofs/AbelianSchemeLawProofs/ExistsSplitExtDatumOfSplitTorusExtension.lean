import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenAndBijectiveOfWeightUnits
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLocalUnitOfWeight

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ToSplit

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Germs

variable {X Y Z : Scheme.{0}}

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[gm_val (κ ≫ f) z U h]`. Express the relevant statement in the definitionally equal form `_ = (κ.stalkMap z).hom (gm f (κ z) U a).val`. Rewrite using `[gm_val f (κ z) U h]`. Conclude with `(Scheme.Hom.germ_stalkMap_apply κ (f ⁻¹ᵁ U) z h _).symm`.
-/
theorem gm_comp (κ : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (κ z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (κ ≫ f) z U a = Units.map (κ.stalkMap z).hom.toMonoidHom (gm f (κ z) U a) := by
  apply Units.ext
  rw [gm_val (κ ≫ f) z U h]
  change _ = (κ.stalkMap z).hom (gm f (κ z) U a).val
  rw [gm_val f (κ z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply κ (f ⁻¹ᵁ U) z h _).symm

/- English proof (translation)
The claim follows from `(gm_res r z hle h _).trans (gm_pull r f z U (hle h) a)`.
-/
theorem gm_res_pull (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) {U : X.Opens} {V : Y.Opens} (hle : V ≤ f ⁻¹ᵁ U)
    (h : r z ∈ V) (a : Γ(X, U)ˣ) : gm r z V (res hle (pullU f U a)) = gm (r ≫ f) z U a :=
  (gm_res r z hle h _).trans (gm_pull r f z U (hle h) a)

/- English proof (translation)
The claim follows from `gm_res r z hle h a`.
-/
theorem gm_res_pre (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) {U : Y.Opens} {V : X.Opens} (hle : f ⁻¹ᵁ V ≤ U)
    (h : f (r z) ∈ V) (a : Γ(Y, U)ˣ) : gm r z (f ⁻¹ᵁ V) (res hle a) = gm r z U a :=
  gm_res r z hle h a

/- English proof (translation)
Rewrite using `[gm_res_pull (𝟙 Y) f y hle h, Category.id_comp]`.
-/
theorem gm_id_res_pull (f : Y ⟶ X) (y : Y) {U : X.Opens} {V : Y.Opens} (hle : V ≤ f ⁻¹ᵁ U)
    (h : y ∈ V) (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res hle (pullU f U a)) = gm f y U a := by
  rw [gm_res_pull (𝟙 Y) f y hle h, Category.id_comp]

/- English proof (translation)
Rewrite using `[gm_pull (𝟙 Y) f y U h, Category.id_comp]`.
-/
theorem gm_id_pull' (f : Y ⟶ X) (y : Y) {U : X.Opens} (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm (𝟙 Y) y (f ⁻¹ᵁ U) (pullU f U a) = gm f y U a := by
  rw [gm_pull (𝟙 Y) f y U h, Category.id_comp]

/- English proof (translation)
Establish `: pullU π U a = pullU π U b` using `unit_ext fun y hy => by`. Rewrite using `[gm_id_pull' π y hy, gm_id_pull' π y hy, h y hy]`. Conclude with `Units.ext (FunDescent.app_injective π U (congrArg Units.val this))`.
-/
theorem unit_ext_of_cover (π : Y ⟶ X) [Flat π] [Surjective π] {U : X.Opens} {a b : Γ(X, U)ˣ}
    (h : ∀ y, π y ∈ U → gm π y U a = gm π y U b) : a = b := by
  have : pullU π U a = pullU π U b := unit_ext fun y hy => by
    rw [gm_id_pull' π y hy, gm_id_pull' π y hy, h y hy]
  exact Units.ext (FunDescent.app_injective π U (congrArg Units.val this))

end Germs

section Descent

variable {S : Scheme.{0}} {X Y : Over S} (π : Y ⟶ X) [Flat π.left] [Surjective π.left]
  [QuasiCompact π.left]

/- English proof (translation)
Take `⟨a, ha⟩` from `FunDescent.exists_app_eq π.left U f.val fun Z g₁ g₂ h₁ h₂ e => by`. Set `Z' : Over S` to `Over.mk (g₂ ≫ Y.hom)`. Set `k₂ : Z' ⟶ Y` to `Over.homMk g₂ rfl`. Set `k₁ : Z' ⟶ Y` to `Over.homMk g₁ (by`. Express the relevant statement in the definitionally equal form `g₁ ≫ Y.hom = g₂ ≫ Y.hom`.

Rewrite using `[← Over.w π, reassoc_of% e])`. Establish `: res h₁ (pullU g₁ _ f) = res h₂ (pullU g₂ _ f)` using `unit_ext fun z hz => by`. Rewrite using `[gm_id_res_pull g₁ z h₁ hz, gm_id_res_pull g₂ z h₂ hz]`. Conclude with `hf Z' k₁ k₂ z (Over.OverMorphism.ext e) (h₁ hz) (h₂ hz)`. Conclude with `congrArg Units.val this`.

Establish `hu : IsUnit a` using `FunDescent.isUnit_of_isUnit_app π.left U a (ha ▸ f.isUnit)`. Conclude with `⟨hu.unit, Units.ext ha⟩`.
-/
theorem exists_unit_descent (U : X.left.Opens) (f : Γ(Y.left, π.left ⁻¹ᵁ U)ˣ)
    (hf : ∀ (Z : Over S) (g₁ g₂ : Z ⟶ Y) (z : Z.left), g₁ ≫ π = g₂ ≫ π → π.left (g₁.left z) ∈ U →
      π.left (g₂.left z) ∈ U → gm g₁.left z _ f = gm g₂.left z _ f) :
    ∃ a : Γ(X.left, U)ˣ, pullU π.left U a = f := by
  obtain ⟨a, ha⟩ := FunDescent.exists_app_eq π.left U f.val fun Z g₁ g₂ h₁ h₂ e => by
    let Z' : Over S := Over.mk (g₂ ≫ Y.hom)
    let k₂ : Z' ⟶ Y := Over.homMk g₂ rfl
    let k₁ : Z' ⟶ Y := Over.homMk g₁ (by
      change g₁ ≫ Y.hom = g₂ ≫ Y.hom
      rw [← Over.w π, reassoc_of% e])
    have : res h₁ (pullU g₁ _ f) = res h₂ (pullU g₂ _ f) := unit_ext fun z hz => by
      rw [gm_id_res_pull g₁ z h₁ hz, gm_id_res_pull g₂ z h₂ hz]
      exact hf Z' k₁ k₂ z (Over.OverMorphism.ext e) (h₁ hz) (h₂ hz)
    exact congrArg Units.val this
  have hu : IsUnit a := FunDescent.isUnit_of_isUnit_app π.left U a (ha ▸ f.isUnit)
  exact ⟨hu.unit, Units.ext ha⟩

/- English proof (translation)
Use `choose a ha using fun j => exists_unit_descent π (M.U j) (f j) (hf j)`. Use `⟨⟨a⟩, fun j j' => unit_ext_of_cover π.left fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy, ← gm_id_pull' π.left y hy.1 (a j), ← gm_id_pull' π.left y hy.2 (a j'), ha, ha]`. Conclude with `hg j j' y hy.1 hy.2`.
-/
theorem exists_gen_descent (M : LB X.left) (f : ∀ j, Γ(Y.left, π.left ⁻¹ᵁ M.U j)ˣ)
    (hf : ∀ j (Z : Over S) (g₁ g₂ : Z ⟶ Y) (z : Z.left), g₁ ≫ π = g₂ ≫ π →
      π.left (g₁.left z) ∈ M.U j → π.left (g₂.left z) ∈ M.U j →
      gm g₁.left z _ (f j) = gm g₂.left z _ (f j))
    (hg : ∀ j j' (y : Y.left), π.left y ∈ M.U j → π.left y ∈ M.U j' →
      gm (𝟙 _) y _ (f j) = gm π.left y (M.U j ⊓ M.U j') (M.g j j') * gm (𝟙 _) y _ (f j')) :
    ∃ t : LB.Gen M, t.IsGen := by
  choose a ha using fun j => exists_unit_descent π (M.U j) (f j) (hf j)
  refine ⟨⟨a⟩, fun j j' => unit_ext_of_cover π.left fun y hy => ?_⟩
  rw [map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy, ← gm_id_pull' π.left y hy.1 (a j),
    ← gm_id_pull' π.left y hy.2 (a j'), ha, ha]
  exact hg j j' y hy.1 hy.2

end Descent

section Weight

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]

noncomputable def charGerm {Z : Over S} (z : Z.left) :
    (Z ⟶ splitTorus S X) →* (Multiplicative X →* (Z.left.presheaf.stalk z)ˣ) :=
  (MonoidHom.compHom (gm (𝟙 Z.left) z ⊤)).comp (splitTorusPointsEquiv S X Z).toMonoidHom

/- English proof (translation)
Rewrite using `[← gm_id_pull' t.left z (U := ⊤) trivial]`. Conclude with `congrArg (gm (𝟙 Z.left) z ⊤) (Units.ext (splitTorusPointsEquiv_val S X Z t χ))`.
-/
theorem charGerm_eq {Z : Over S} (z : Z.left) (t : Z ⟶ splitTorus S X) (χ : X) :
    charGerm z t (Multiplicative.ofAdd χ) = gm t.left z ⊤ (charUnit S X χ) := by
  rw [← gm_id_pull' t.left z (U := ⊤) trivial]
  exact congrArg (gm (𝟙 Z.left) z ⊤) (Units.ext (splitTorusPointsEquiv_val S X Z t χ))

def HasWeight (q : G ⟶ B) (i : splitTorus S X ⟶ G) (χ : X) (V : B.left.Opens)
    (u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), q.left (g.left z) ∈ V →
    gm ((t ≫ i) * g).left z _ u = charGerm z t (Multiplicative.ofAdd χ) * gm g.left z _ u

variable {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk

/- English proof (translation)
Rewrite using `[MonObj.mul_comp, Category.assoc, hk.w, ← Category.assoc, comp_toUnit]`. Conclude with `_root_.one_mul _`.
-/
theorem act_comp {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) :
    ((t ≫ i) * g) ≫ q = g ≫ q := by
  rw [MonObj.mul_comp, Category.assoc, hk.w, ← Category.assoc, comp_toUnit]
  exact _root_.one_mul _

/- English proof (translation)
The claim follows from `congr(($(act_comp hk t g)).left z)`.
-/
theorem act_apply {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) :
    q.left (((t ≫ i) * g).left z) = q.left (g.left z) :=
  congr(($(act_comp hk t g)).left z)

/- English proof (translation)
Establish `w : (g₁ * g₂⁻¹) ≫ q = toUnit Z ≫ η[B]`. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]`. Both sides reduce to the same expression. Conclude with `⟨hk.lift _ _ w, by rw [hk.lift_fst, inv_mul_cancel_right]⟩`.
-/
theorem exists_act {Z : Over S} {g₁ g₂ : Z ⟶ G} (e : g₁ ≫ q = g₂ ≫ q) :
    ∃ t : Z ⟶ splitTorus S X, g₁ = (t ≫ i) * g₂ := by
  have w : (g₁ * g₂⁻¹) ≫ q = toUnit Z ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
    rfl
  exact ⟨hk.lift _ _ w, by rw [hk.lift_fst, inv_mul_cancel_right]⟩

omit hk [GrpObj B] [IsMonHom q] in
/- English proof (translation)
Establish `: res h₁ (pullU _ _ u) = splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ) * res h₂ (pullU _ _ u)` using `unit_ext fun z hz => by`. Rewrite using `[gm_id_res_pull _ z h₁ hz, hu Z t g z (h₂ hz), map_mul, gm_id_res_pull _ z h₂ hz]`. Both sides reduce to the same expression. Rewrite using `[← splitTorusPointsEquiv_val]`. Conclude with `congrArg Units.val this`.
-/
theorem HasWeight.appLE {χ : X} {V : B.left.Opens} {u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ}
    (hu : HasWeight q i χ V u) (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
    (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) :
    (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u.val =
      t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u.val := by
  have : res h₁ (pullU _ _ u) =
      splitTorusPointsEquiv S X Z t (Multiplicative.ofAdd χ) * res h₂ (pullU _ _ u) :=
    unit_ext fun z hz => by
      rw [gm_id_res_pull _ z h₁ hz, hu Z t g z (h₂ hz), map_mul, gm_id_res_pull _ z h₂ hz]
      rfl
  rw [← splitTorusPointsEquiv_val]
  exact congrArg Units.val this

/- English proof (translation)
Introduce `Z t g z hz`. Set `W : Z.left.Opens` to `g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)`. Set `Z' : Over S` to `Over.mk (W.ι ≫ Z.hom)`. Set `κ : Z' ⟶ Z` to `Over.homMk W.ι rfl`. Establish `h₂ : ⊤ ≤ (κ ≫ g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)` using `fun x _ => x.2`.

Establish `h₁ : ⊤ ≤ (((κ ≫ t) ≫ i) * (κ ≫ g)).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)` using `fun x hx => by`. Express the relevant statement in the definitionally equal form `q.left _ ∈ V`. Rewrite using `[act_apply hk]`. Conclude with `h₂ hx`. Establish `e : res h₁ (pullU _ _ u) = splitTorusPointsEquiv S X Z' (κ ≫ t) (Multiplicative.ofAdd χ) * res h₂ (pullU _ _ u)` using `Units.ext ((hu Z' (κ ≫ t) (κ ≫ g) h₁ h₂).trans (by rw [← splitTorusPointsEquiv_val]; rfl))`.

Set `z' : Z'.left` to `(⟨z, hz⟩ : W)`. Establish `e'` using `(gm_id_res_pull _ z' h₁ trivial u).symm.trans ((congrArg (gm (𝟙 _) z' ⊤) e).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (charGerm_eq z' (κ ≫ t) χ) (gm_id_res_pull _ z' h₂ trivial _))))`. Establish `e₁ : ((κ ≫ t) ≫ i) * (κ ≫ g) = κ ≫ ((t ≫ i) * g)`. Rewrite using `[MonObj.comp_mul, Category.assoc]`. Establish `hz' : q.left (((t ≫ i) * g).left z) ∈ V` using `by rwa [act_apply hk]`.

Rewrite `e'` using `[e₁]`. Establish `e''` using `(gm_comp W.ι ((t ≫ i) * g).left ⟨z, hz⟩ (q.left ⁻¹ᵁ V) hz' u).symm.trans (e'.trans ((congrArg₂ (· * ·) (gm_comp W.ι t.left ⟨z, hz⟩ ⊤ trivial _) (gm_comp W.ι g.left ⟨z, hz⟩ (q.left ⁻¹ᵁ V) hz u)).trans (map_mul _ _ _).symm))`. Rewrite using `[charGerm_eq]`. Establish `: IsIso (W.ι.stalkMap ⟨z, hz⟩)` using `IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _`. Conclude with `Units.ext ((ConcreteCategory.bijective_of_isIso (W.ι.stalkMap ⟨z, hz⟩)).1 (congrArg Units.val e''))`.
-/
theorem hasWeight_of_appLE {χ : X} {V : B.left.Opens} {u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ}
    (hu : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G)
      (h₁ : ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V)) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)),
      (((t ≫ i) * g).left.appLE _ ⊤ h₁).hom u.val =
        t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u.val) :
    HasWeight q i χ V u := by
  intro Z t g z hz
  let W : Z.left.Opens := g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)
  let Z' : Over S := Over.mk (W.ι ≫ Z.hom)
  let κ : Z' ⟶ Z := Over.homMk W.ι rfl
  have h₂ : ⊤ ≤ (κ ≫ g).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) := fun x _ => x.2
  have h₁ : ⊤ ≤ (((κ ≫ t) ≫ i) * (κ ≫ g)).left ⁻¹ᵁ (q.left ⁻¹ᵁ V) := fun x hx => by
    change q.left _ ∈ V
    rw [act_apply hk]
    exact h₂ hx
  have e : res h₁ (pullU _ _ u) =
      splitTorusPointsEquiv S X Z' (κ ≫ t) (Multiplicative.ofAdd χ) * res h₂ (pullU _ _ u) :=
    Units.ext ((hu Z' (κ ≫ t) (κ ≫ g) h₁ h₂).trans (by rw [← splitTorusPointsEquiv_val]; rfl))
  let z' : Z'.left := (⟨z, hz⟩ : W)
  have e' := (gm_id_res_pull _ z' h₁ trivial u).symm.trans
    ((congrArg (gm (𝟙 _) z' ⊤) e).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (charGerm_eq z' (κ ≫ t) χ) (gm_id_res_pull _ z' h₂ trivial _))))
  have e₁ : ((κ ≫ t) ≫ i) * (κ ≫ g) = κ ≫ ((t ≫ i) * g) := by
    rw [MonObj.comp_mul, Category.assoc]
  have hz' : q.left (((t ≫ i) * g).left z) ∈ V := by rwa [act_apply hk]
  rw [e₁] at e'
  have e'' := (gm_comp W.ι ((t ≫ i) * g).left ⟨z, hz⟩ (q.left ⁻¹ᵁ V) hz' u).symm.trans
    (e'.trans ((congrArg₂ (· * ·) (gm_comp W.ι t.left ⟨z, hz⟩ ⊤ trivial _)
      (gm_comp W.ι g.left ⟨z, hz⟩ (q.left ⁻¹ᵁ V) hz u)).trans (map_mul _ _ _).symm))
  rw [charGerm_eq]
  have : IsIso (W.ι.stalkMap ⟨z, hz⟩) := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  exact Units.ext ((ConcreteCategory.bijective_of_isIso (W.ι.stalkMap ⟨z, hz⟩)).1
    (congrArg Units.val e''))

end Weight

section Sums

variable {S : Scheme.{0}}

/- English proof (translation)
Unfold `psum`. Proceed by induction on `(List.finRange n).filter (· ∈ I) with`. Consider the case `nil => rfl`. Consider the case `cons a l ih => rw [List.foldr_cons, ih]`. Both sides reduce to the same expression.
-/
theorem psum_eq_prod (G : Over S) [GrpObj G] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G))
    (I : Finset (Fin n)) : psum G x I = (((List.finRange n).filter (· ∈ I)).map x).prod := by
  unfold psum
  induction (List.finRange n).filter (· ∈ I) with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, ih]; rfl

/- English proof (translation)
Rewrite using `[psum_eq_prod, psum_eq_prod, map_list_prod, List.map_map]`. Both sides reduce to the same expression.
-/
theorem map_psum {G G' : Over S} [GrpObj G] [GrpObj G'] {T T' : Over S} (F : (T ⟶ G) →* (T' ⟶ G'))
    {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    F (psum G x I) = psum G' (fun k => F (x k)) I := by
  rw [psum_eq_prod, psum_eq_prod, map_list_prod, List.map_map]
  rfl

/- English proof (translation)
The claim follows from `map_psum (MonoidHom.mk' (fun a : T ⟶ G => r ≫ a) (fun a b => MonObj.comp_mul r a b)) x I`.
-/
theorem comp_psum (G : Over S) [GrpObj G] {T T' : Over S} (r : T' ⟶ T) {n : ℕ}
    (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    r ≫ psum G x I = psum G (fun k => r ≫ x k) I :=
  map_psum (MonoidHom.mk' (fun a : T ⟶ G => r ≫ a) (fun a b => MonObj.comp_mul r a b)) x I

/- English proof (translation)
The claim follows from `map_psum (MonoidHom.mk' (fun a : T ⟶ G => a ≫ f) (fun a b => MonObj.mul_comp a b f)) x I`.
-/
theorem psum_comp {G G' : Over S} [GrpObj G] [GrpObj G'] (f : G ⟶ G') [IsMonHom f] {T : Over S}
    {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I ≫ f = psum G' (fun k => x k ≫ f) I :=
  map_psum (MonoidHom.mk' (fun a : T ⟶ G => a ≫ f) (fun a b => MonObj.mul_comp a b f)) x I

/- English proof (translation)
Rewrite using `[psum_eq_prod, psum_eq_prod, psum_eq_prod]`. Conclude with `List.prod_map_mul`.
-/
theorem psum_mul (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} {n : ℕ}
    (x y : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G (fun k => x k * y k) I = psum G x I * psum G y I := by
  rw [psum_eq_prod, psum_eq_prod, psum_eq_prod]
  exact List.prod_map_mul

/- English proof (translation)
Use `(Equiv.ulift.{0, 0}.prod_comp (fun I : Finset (Fin 2) => c (psum G x I) ^ ((-1 : ℤ) ^ (2 - I.card)))).trans ?_` and prove the remaining obligations. Establish `: (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}}` using `by decide`. Rewrite using `[this, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]`. Simplify using `only [psum_eq_prod, map_list_prod]`. Simplify using `[List.finRange_succ, mul_comm]`.
-/
theorem prod_square_eq_one {G : Over S} [GrpObj G] {T : Over S} {A : Type} [CommGroup A]
    (c : (T ⟶ G) →* A) (x : Fin 2 → (T ⟶ G)) :
    ∏ I : ULift.{0} (Finset (Fin 2)), c (psum G x I.down) ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  refine (Equiv.ulift.{0, 0}.prod_comp
    (fun I : Finset (Fin 2) => c (psum G x I) ^ ((-1 : ℤ) ^ (2 - I.card)))).trans ?_
  have : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [this, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [psum_eq_prod, map_list_prod]
  simp [List.finRange_succ, mul_comm]

/- English proof (translation)
Establish `: (MonoidHom.toAdditiveRight F).toIntLinearMap = (MonoidHom.toAdditiveRight F').toIntLinearMap` using `b.ext fun k => congrArg Additive.ofMul (h k)`. Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations. Conclude with `congrArg Additive.toMul (LinearMap.congr_fun this x.toAdd)`.
-/
theorem monoidHom_ext_basis {X K A : Type} [AddCommGroup X] [CommGroup A] (b : Module.Basis K ℤ X)
    {F F' : Multiplicative X →* A}
    (h : ∀ k, F (Multiplicative.ofAdd (b k)) = F' (Multiplicative.ofAdd (b k))) : F = F' := by
  have : (MonoidHom.toAdditiveRight F).toIntLinearMap = (MonoidHom.toAdditiveRight F').toIntLinearMap :=
    b.ext fun k => congrArg Additive.ofMul (h k)
  refine MonoidHom.ext fun x => ?_
  exact congrArg Additive.toMul (LinearMap.congr_fun this x.toAdd)

/- English proof (translation)
Simplify using `[div_eq_mul_inv, mul_comm]`.
-/
theorem inv_eq_div_mul_inv {A : Type} [CommGroup A] (a b : A) : a⁻¹ = b / a * b⁻¹ := by
  simp [div_eq_mul_inv, mul_comm]

end Sums

section Bundle

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]

def IsFrame (q : G ⟶ B) (i : splitTorus S X ⟶ G) (χ : X) (O : RigLB B)
    (u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ) : Prop :=
  (∀ j, HasWeight q i χ (O.L.U j) (u j)) ∧
  (∀ j j' (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ O.L.U j →
    q.left (r z) ∈ O.L.U j' → gm (r ≫ q.left) z (O.L.U j ⊓ O.L.U j') (O.L.g j j') =
      gm r z _ (u j') / gm r z _ (u j)) ∧
  ∀ j (z : (𝟙_ (Over S)).left), eSec B z ∈ O.L.U j →
    gm (𝟙 _) z ((O.L.pull (eSec B)).U (fun _ => j)) (O.rig.s (fun _ => j)) =
      (gm (eSec G) z _ (u j))⁻¹

variable {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[B]))

omit [Flat q.left] [Surjective q.left] [QuasiCompact q.left] in
/- English proof (translation)
The claim follows from `congrArg Over.Hom.left (IsMonHom.one_hom q)`.
-/
theorem eSec_comp : eSec G ≫ q.left = eSec B :=
  congrArg Over.Hom.left (IsMonHom.one_hom q)

include hk

omit [Flat q.left] [Surjective q.left] [QuasiCompact q.left] in
/- English proof (translation)
The claim follows from `isAffineHom_of_flatQuotient_of_affine_kernel S G B _ q i ‹_› ‹_› ‹_› ‹_› ‹_› hk (MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _) (by change IsAffineHom (Spec.map _) infer_instance))`.
-/
theorem isAffineHom_left [Flat q.left] [Surjective q.left] [QuasiCompact q.left] :
    IsAffineHom q.left :=
  isAffineHom_of_flatQuotient_of_affine_kernel S G B _ q i ‹_› ‹_› ‹_› ‹_› ‹_› hk
    (MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback _ _) (by
      change IsAffineHom (Spec.map _)
      infer_instance))

/- English proof (translation)
Set `J : Type` to `Σ V : B.left.Opens, {u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ // HasWeight q i χ V u}`. Establish `l₁ : ∀ a b : J, q.left ⁻¹ᵁ (a.1 ⊓ b.1) ≤ q.left ⁻¹ᵁ a.1` using `fun a b x hx => hx.1`. Establish `l₂ : ∀ a b : J, q.left ⁻¹ᵁ (a.1 ⊓ b.1) ≤ q.left ⁻¹ᵁ b.1` using `fun a b x hx => hx.2`. Establish `hd : ∀ a b : J, ∃ g : Γ(B.left, a.1 ⊓ b.1)ˣ, pullU q.left _ g = res (l₂ a b) b.2.1 / res (l₁ a b) a.2.1` using `fun a b => exists_unit_descent q _ _ fun Z g₁ g₂ z e h₁ h₂ => by`. Take `⟨t, rfl⟩` from `exists_act hk e`.

Rewrite using `[map_div, map_div, gm_res_pre _ _ _ _ h₁, gm_res_pre _ _ _ _ h₁, gm_res_pre _ _ _ _ h₂, gm_res_pre _ _ _ _ h₂, a.2.2 Z t g₂ z h₂.1, b.2.2 Z t g₂ z h₂.2, mul_div_mul_left_eq_div]`. Use `choose g hg using hd`. Establish `hg' : ∀ (a b : J) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ a.1 → q.left (r z) ∈ b.1 → gm (r ≫ q.left) z (a.1 ⊓ b.1) (g a b) = gm r z _ b.2.1 / gm r z _ a.2.1` using `fun a b Z r z h₁ h₂ => by`. Establish `hm : q.left (r z) ∈ a.1 ⊓ b.1` using `⟨h₁, h₂⟩`. Rewrite using `[← gm_pull r q.left z _ hm, hg, map_div, gm_res_pre _ _ _ _ hm, gm_res_pre _ _ _ _ hm]`.

Establish `hg'' : ∀ (a b : J) (y : G.left), q.left y ∈ a.1 → q.left y ∈ b.1 → gm q.left y (a.1 ⊓ b.1) (g a b) = gm (𝟙 _) y _ b.2.1 / gm (𝟙 _) y _ a.2.1` using `fun a b y h₁ h₂ => by rw [← hg' a b _ (𝟙 _) y h₁ h₂, Category.id_comp]`. Set `L : LB B.left` to `⟨J, fun a => a.1, g⟩`. Establish `hL : L.IsLB`. Use `⟨?_, fun a => ?_, fun a b c => ?_⟩` and prove the remaining obligations. Use `top_le_iff.1 fun x _ => ?_` and prove the remaining obligations.

Take `⟨V, hV, u, hu⟩` from `exists_local_unit_of_weight S X G B q i ‹_› ‹_› ‹_› ‹_› ‹_› hk (isAffineHom_left hk) χ x`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, u, hasWeight_of_appLE hk hu⟩, hV⟩`. Use `unit_ext_of_cover q.left fun y hy => ?_` and prove the remaining obligations. Rewrite using `[gm_res _ _ _ hy, map_one]`. Conclude with `(hg'' a a y hy hy).trans (div_self' _)`.

Use `unit_ext_of_cover q.left fun y hy => ?_` and prove the remaining obligations. Rewrite using `[map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy, gm_res _ _ _ hy]`. Use `(congrArg₂ (· * ·) (hg'' a b y hy.1.1 hy.1.2) (hg'' b c y hy.1.2 hy.2)).trans (Eq.trans ?_ (hg'' a c y hy.1.1 hy.2).symm)` and prove the remaining obligations. Rewrite using `[mul_comm, div_mul_div_cancel]`. Establish `hm : ∀ (a : J) (z : (𝟙_ (Over S)).left), eSec B z ∈ a.1 → q.left (eSec G z) ∈ a.1` using `fun a z hz => by rwa [← eSec_comp (G := G) (q := q)] at hz`.

Establish `le : ∀ j : PUnit → J, (L.pull (eSec B)).U j ≤ eSec G ⁻¹ᵁ (q.left ⁻¹ᵁ (j PUnit.unit).1)` using `fun j z hz => hm _ z (mem_pull.1 hz)`. Set `rig : LB.Gen (L.pull (eSec B))` to `⟨fun j => (res (le j) (pullU (eSec G) _ (j PUnit.unit).2.1))⁻¹⟩`. Establish `hrig : ∀ (j : PUnit → J) (z : (𝟙_ (Over S)).left), z ∈ (L.pull (eSec B)).U j → gm (𝟙 _) z ((L.pull (eSec B)).U j) (rig.s j) = (gm (eSec G) z _ (j PUnit.unit).2.1)⁻¹` using `fun j z hz => (map_inv _ _).trans (congrArg (·⁻¹) (gm_id_res_pull _ z (le j) hz _))`. Establish `hgen : rig.IsGen` using `fun j j' => unit_ext fun z hz => by`. Rewrite using `[map_mul, gm_res _ _ _ hz, gm_res _ _ _ hz, hrig j z hz.1, hrig j' z hz.2, gm_pull_g L (eSec B) (𝟙 _) z j j' hz.1 hz.2, Category.id_comp]`.

Use `hg' (j PUnit.unit) (j' PUnit.unit) _ (eSec G) z (le j hz.1) (le j' hz.2)` as an intermediate fact. Rewrite `this` using `[eSec_comp]`. Use `Eq.trans ?_ (congrArg (· * _) this.symm)` and prove the remaining obligations. Conclude with `inv_eq_div_mul_inv _ _`. Conclude with `⟨⟨L, rig, hL, hgen⟩, fun a => a.2.1, fun a => a.2.2, hg', fun a z hz => hrig (fun _ => a) z (mem_pull.2 hz)⟩`.
-/
theorem exists_isFrame (χ : X) : ∃ (O : RigLB B) (u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ),
    IsFrame q i χ O u := by
  let J : Type := Σ V : B.left.Opens, {u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ // HasWeight q i χ V u}
  have l₁ : ∀ a b : J, q.left ⁻¹ᵁ (a.1 ⊓ b.1) ≤ q.left ⁻¹ᵁ a.1 := fun a b x hx => hx.1
  have l₂ : ∀ a b : J, q.left ⁻¹ᵁ (a.1 ⊓ b.1) ≤ q.left ⁻¹ᵁ b.1 := fun a b x hx => hx.2
  have hd : ∀ a b : J, ∃ g : Γ(B.left, a.1 ⊓ b.1)ˣ,
      pullU q.left _ g = res (l₂ a b) b.2.1 / res (l₁ a b) a.2.1 := fun a b =>
    exists_unit_descent q _ _ fun Z g₁ g₂ z e h₁ h₂ => by
      obtain ⟨t, rfl⟩ := exists_act hk e
      rw [map_div, map_div, gm_res_pre _ _ _ _ h₁, gm_res_pre _ _ _ _ h₁, gm_res_pre _ _ _ _ h₂,
        gm_res_pre _ _ _ _ h₂,
        a.2.2 Z t g₂ z h₂.1, b.2.2 Z t g₂ z h₂.2, mul_div_mul_left_eq_div]
  choose g hg using hd
  have hg' : ∀ (a b : J) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ a.1 →
      q.left (r z) ∈ b.1 → gm (r ≫ q.left) z (a.1 ⊓ b.1) (g a b) =
        gm r z _ b.2.1 / gm r z _ a.2.1 := fun a b Z r z h₁ h₂ => by
    have hm : q.left (r z) ∈ a.1 ⊓ b.1 := ⟨h₁, h₂⟩
    rw [← gm_pull r q.left z _ hm, hg, map_div, gm_res_pre _ _ _ _ hm, gm_res_pre _ _ _ _ hm]
  have hg'' : ∀ (a b : J) (y : G.left), q.left y ∈ a.1 → q.left y ∈ b.1 →
      gm q.left y (a.1 ⊓ b.1) (g a b) = gm (𝟙 _) y _ b.2.1 / gm (𝟙 _) y _ a.2.1 :=
    fun a b y h₁ h₂ => by rw [← hg' a b _ (𝟙 _) y h₁ h₂, Category.id_comp]
  let L : LB B.left := ⟨J, fun a => a.1, g⟩
  have hL : L.IsLB := by
    refine ⟨?_, fun a => ?_, fun a b c => ?_⟩
    · refine top_le_iff.1 fun x _ => ?_
      obtain ⟨V, hV, u, hu⟩ := exists_local_unit_of_weight S X G B q i ‹_› ‹_› ‹_› ‹_› ‹_› hk
        (isAffineHom_left hk) χ x
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, u, hasWeight_of_appLE hk hu⟩, hV⟩
    · refine unit_ext_of_cover q.left fun y hy => ?_
      rw [gm_res _ _ _ hy, map_one]
      exact (hg'' a a y hy hy).trans (div_self' _)
    · refine unit_ext_of_cover q.left fun y hy => ?_
      rw [map_mul, gm_res _ _ _ hy, gm_res _ _ _ hy, gm_res _ _ _ hy]
      refine (congrArg₂ (· * ·) (hg'' a b y hy.1.1 hy.1.2) (hg'' b c y hy.1.2 hy.2)).trans
        (Eq.trans ?_ (hg'' a c y hy.1.1 hy.2).symm)
      rw [mul_comm, div_mul_div_cancel]
  have hm : ∀ (a : J) (z : (𝟙_ (Over S)).left), eSec B z ∈ a.1 → q.left (eSec G z) ∈ a.1 :=
    fun a z hz => by rwa [← eSec_comp (G := G) (q := q)] at hz
  have le : ∀ j : PUnit → J, (L.pull (eSec B)).U j ≤ eSec G ⁻¹ᵁ (q.left ⁻¹ᵁ (j PUnit.unit).1) :=
    fun j z hz => hm _ z (mem_pull.1 hz)
  let rig : LB.Gen (L.pull (eSec B)) :=
    ⟨fun j => (res (le j) (pullU (eSec G) _ (j PUnit.unit).2.1))⁻¹⟩
  have hrig : ∀ (j : PUnit → J) (z : (𝟙_ (Over S)).left), z ∈ (L.pull (eSec B)).U j →
      gm (𝟙 _) z ((L.pull (eSec B)).U j) (rig.s j) = (gm (eSec G) z _ (j PUnit.unit).2.1)⁻¹ :=
    fun j z hz => (map_inv _ _).trans (congrArg (·⁻¹) (gm_id_res_pull _ z (le j) hz _))
  have hgen : rig.IsGen := fun j j' => unit_ext fun z hz => by
    rw [map_mul, gm_res _ _ _ hz, gm_res _ _ _ hz, hrig j z hz.1, hrig j' z hz.2,
      gm_pull_g L (eSec B) (𝟙 _) z j j' hz.1 hz.2, Category.id_comp]
    have := hg' (j PUnit.unit) (j' PUnit.unit) _ (eSec G) z (le j hz.1) (le j' hz.2)
    rw [eSec_comp] at this
    refine Eq.trans ?_ (congrArg (· * _) this.symm)
    exact inv_eq_div_mul_inv _ _
  exact ⟨⟨L, rig, hL, hgen⟩, fun a => a.2.1, fun a => a.2.2, hg',
    fun a z hz => hrig (fun _ => a) z (mem_pull.2 hz)⟩

end Bundle

section Laws

/- English proof (translation)
Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_div]`. Normalize the expressions using the abelian group laws.
-/
theorem aux_add {A : Type} [CommGroup A] (a a' b b' c c' : A) :
    a⁻¹ * b * c = a' / a * (b' / b)⁻¹ * (c' / c)⁻¹ * (a'⁻¹ * b' * c') := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

/- English proof (translation)
Simplify using `only [mul_inv, mul_zpow, Finset.prod_mul_distrib]`. Simplify using `only [inv_zpow, Finset.prod_inv_distrib, h, inv_one, _root_.one_mul]`.
-/
theorem prod_erase_one_perm_apply_eq_zero {A K : Type} [CommGroup A] [Fintype K] (c a : K → A) (ε : K → ℤ)
    (h : ∏ I, c I ^ ε I = 1) : ∏ I, (c I * a I)⁻¹ ^ ε I = ∏ I, (a I)⁻¹ ^ ε I := by
  simp only [mul_inv, mul_zpow, Finset.prod_mul_distrib]
  simp only [inv_zpow, Finset.prod_inv_distrib, h, inv_one, _root_.one_mul]

/- English proof (translation)
Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem commGroup_weight_cancel_identity {A : Type} [CommGroup A] (x y a b c : A) :
    (x * y * a)⁻¹ * (x * b) * (y * c) = a⁻¹ * b * c := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[B]))

omit [IsMonHom q] [IsMonHom i] [Flat q.left] [Surjective q.left] [QuasiCompact q.left] in
/- English proof (translation)
Rewrite using `[← h.2.1 j j' _ (𝟙 _) y h₁ h₂, Category.id_comp]`.
-/
theorem IsFrame.trans_id {χ : X} {O : RigLB B} {u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ}
    (h : IsFrame q i χ O u) (j j' : O.L.ι) (y : G.left) (h₁ : q.left y ∈ O.L.U j)
    (h₂ : q.left y ∈ O.L.U j') : gm q.left y (O.L.U j ⊓ O.L.U j') (O.L.g j j') =
      gm (𝟙 _) y _ (u j') / gm (𝟙 _) y _ (u j) := by
  rw [← h.2.1 j j' _ (𝟙 _) y h₁ h₂, Category.id_comp]

include hk

omit [IsMonHom i] in

/- English proof (translation)
Use `exists_gen_descent q O.L (fun j => (u j)⁻¹) (fun j Z g₁ g₂ z e h₁ h₂ => ?_) (fun j j' y h₁ h₂ => ?_)` and prove the remaining obligations. Take `⟨t, rfl⟩` from `exists_act hk e`. Rewrite using `[map_inv, map_inv, h.1 j Z t g₂ z h₂, ofAdd_zero, map_one, _root_.one_mul]`. Rewrite using `[map_inv, map_inv, h.trans_id j j' y h₁ h₂]`. Conclude with `inv_eq_div_mul_inv _ _`.
-/
theorem IsFrame.exists_gen_zero {O : RigLB B} {u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ}
    (h : IsFrame q i 0 O u) : ∃ t : LB.Gen O.L, t.IsGen := by
  refine exists_gen_descent q O.L (fun j => (u j)⁻¹) (fun j Z g₁ g₂ z e h₁ h₂ => ?_)
    (fun j j' y h₁ h₂ => ?_)
  · obtain ⟨t, rfl⟩ := exists_act hk e
    rw [map_inv, map_inv, h.1 j Z t g₂ z h₂, ofAdd_zero, map_one, _root_.one_mul]
  · rw [map_inv, map_inv, h.trans_id j j' y h₁ h₂]
    exact inv_eq_div_mul_inv _ _

omit [IsMonHom i] in

/- English proof (translation)
Set `M : LB B.left` to `LB.div (LB.div O''.L O.L) O'.L`. Set `f : ∀ p : (O''.L.ι × O.L.ι) × O'.L.ι, Γ(G.left, q.left ⁻¹ᵁ (O''.L.U p.1.1 ⊓ O.L.U p.1.2 ⊓ O'.L.U p.2))ˣ` to `fun p => (res (q.left.preimage_mono (inf_le_left.trans inf_le_left)) (u'' p.1.1))⁻¹ * res (q.left.preimage_mono (inf_le_left.trans inf_le_right)) (u p.1.2) * res (q.left.preimage_mono inf_le_right) (u' p.2)`. Establish `hf : ∀ (p : (O''.L.ι × O.L.ι) × O'.L.ι) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ O''.L.U p.1.1 ⊓ O.L.U p.1.2 ⊓ O'.L.U p.2 → gm r z _ (f p) = (gm r z _ (u'' p.1.1))⁻¹ * gm r z _ (u p.1.2) * gm r z _ (u' p.2)` using `fun p Z r z hz => by`. Rewrite using `[map_mul, map_mul, map_inv, gm_res_pre _ _ _ _ hz, gm_res_pre _ _ _ _ hz, gm_res_pre _ _ _ _ hz]`. Use `exists_gen_descent q M f (fun p Z g₁ g₂ z e h₁ h₂ => ?_) (fun p p' y h₁ h₂ => ?_)` and prove the remaining obligations.

Take `⟨t, rfl⟩` from `exists_act hk e`. Use `(hf p _ _ z h₁).trans (Eq.trans ?_ (hf p _ _ z h₂).symm)` and prove the remaining obligations. Rewrite using `[h.1 _ Z t g₂ z h₂.1.2, h'.1 _ Z t g₂ z h₂.2, h''.1 _ Z t g₂ z h₂.1.1, ofAdd_add, map_mul]`. Conclude with `commGroup_weight_cancel_identity _ _ _ _ _`. Use `(hf p _ (𝟙 _) y h₁).trans (Eq.trans ?_ (congrArg₂ (· * ·) ((gm_div O'.L (LB.div O''.L O.L) q.left y p p' ⟨h₁, h₂⟩).trans (congrArg₂ (· * ·) ((gm_div O.L O''.L q.left y p.1 p'.1 ⟨h₁.1, h₂.1⟩).trans (congrArg₂ (· * ·⁻¹) (h''.trans_id _ _ y h₁.1.1 h₂.1.1) (h.trans_id _ _ y h₁.1.2 h₂ …` and prove the remaining obligations.

Conclude with `aux_add _ _ _ _ _ _`.
-/
theorem IsFrame.exists_iso_add {χ χ' : X} {O O' O'' : RigLB B}
    {u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ} {u' : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O'.L.U j)ˣ}
    {u'' : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O''.L.U j)ˣ} (h : IsFrame q i χ O u)
    (h' : IsFrame q i χ' O' u') (h'' : IsFrame q i (χ + χ') O'' u'') :
    ∃ t : LB.Iso O'.L (LB.div O''.L O.L), t.IsGen := by
  let M : LB B.left := LB.div (LB.div O''.L O.L) O'.L
  let f : ∀ p : (O''.L.ι × O.L.ι) × O'.L.ι,
      Γ(G.left, q.left ⁻¹ᵁ (O''.L.U p.1.1 ⊓ O.L.U p.1.2 ⊓ O'.L.U p.2))ˣ := fun p =>
    (res (q.left.preimage_mono (inf_le_left.trans inf_le_left)) (u'' p.1.1))⁻¹ *
      res (q.left.preimage_mono (inf_le_left.trans inf_le_right)) (u p.1.2) *
      res (q.left.preimage_mono inf_le_right) (u' p.2)
  have hf : ∀ (p : (O''.L.ι × O.L.ι) × O'.L.ι) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z),
      q.left (r z) ∈ O''.L.U p.1.1 ⊓ O.L.U p.1.2 ⊓ O'.L.U p.2 →
      gm r z _ (f p) = (gm r z _ (u'' p.1.1))⁻¹ * gm r z _ (u p.1.2) * gm r z _ (u' p.2) :=
    fun p Z r z hz => by
      rw [map_mul, map_mul, map_inv, gm_res_pre _ _ _ _ hz, gm_res_pre _ _ _ _ hz,
        gm_res_pre _ _ _ _ hz]
  refine exists_gen_descent q M f (fun p Z g₁ g₂ z e h₁ h₂ => ?_) (fun p p' y h₁ h₂ => ?_)
  · obtain ⟨t, rfl⟩ := exists_act hk e
    refine (hf p _ _ z h₁).trans (Eq.trans ?_ (hf p _ _ z h₂).symm)
    rw [h.1 _ Z t g₂ z h₂.1.2, h'.1 _ Z t g₂ z h₂.2, h''.1 _ Z t g₂ z h₂.1.1, ofAdd_add, map_mul]
    exact commGroup_weight_cancel_identity _ _ _ _ _
  · refine (hf p _ (𝟙 _) y h₁).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      ((gm_div O'.L (LB.div O''.L O.L) q.left y p p' ⟨h₁, h₂⟩).trans (congrArg₂ (· * ·)
        ((gm_div O.L O''.L q.left y p.1 p'.1 ⟨h₁.1, h₂.1⟩).trans (congrArg₂ (· * ·⁻¹)
          (h''.trans_id _ _ y h₁.1.1 h₂.1.1) (h.trans_id _ _ y h₁.1.2 h₂.1.2)))
        (congrArg (·⁻¹) (h'.trans_id _ _ y h₁.2 h₂.2))))
      (hf p' _ (𝟙 _) y h₂)).symm)
    exact aux_add _ _ _ _ _ _

omit hk [IsMonHom q] [GrpObj G] [GrpObj B] in
/- English proof (translation)
Establish `h₁ : IsPullback (fst G G) (q ▷ G) q (fst B G)`. Use `⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => lift c.fst (c.snd ≫ snd _ _)) (fun c => by simp) (fun c => ?_) (fun c m h₁ h₂ => ?_)⟩⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [c.condition]`. Apply the tactic sequence `ext <;> simp [← h₁, ← h₂]`. Establish `h₂ : IsPullback (snd B G) (B ◁ q) q (snd B B)`.

Use `⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => lift (c.snd ≫ fst _ _) c.fst) (fun c => by simp) (fun c => ?_) (fun c m h₁ h₂ => ?_)⟩⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [c.condition]`. Apply the tactic sequence `ext <;> simp [← h₁, ← h₂]`. Establish `hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q.left` using `⟨⟨‹_›, ‹_›⟩, ‹_›⟩`. Take `⟨⟨_, _⟩, _⟩ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (q ▷ G).left` from `⟨⟨MorphismProperty.of_isPullback (h₁.map (Over.forget S)) hq.1.1, MorphismProperty.of_isPullback (h₁.map (Over.forget S)) hq.1.2⟩, MorphismProperty.of_isPullback (h₁.map (Over.forget S)) hq.2⟩`.

Take `⟨⟨_, _⟩, _⟩ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (B ◁ q).left` from `⟨⟨MorphismProperty.of_isPullback (h₂.map (Over.forget S)) hq.1.1, MorphismProperty.of_isPullback (h₂.map (Over.forget S)) hq.1.2⟩, MorphismProperty.of_isPullback (h₂.map (Over.forget S)) hq.2⟩`. Rewrite using `[MonoidalCategory.tensorHom_def, Over.comp_left]`. Conclude with `⟨⟨inferInstance, inferInstance⟩, inferInstance⟩`.
-/
theorem cover_tensorHom : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
    (q ⊗ₘ q).left := by
  have h₁ : IsPullback (fst G G) (q ▷ G) q (fst B G) := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => lift c.fst (c.snd ≫ snd _ _))
      (fun c => by simp) (fun c => ?_) (fun c m h₁ h₂ => ?_)⟩⟩
    · ext <;> simp [c.condition]
    · ext <;> simp [← h₁, ← h₂]
  have h₂ : IsPullback (snd B G) (B ◁ q) q (snd B B) := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => lift (c.snd ≫ fst _ _) c.fst)
      (fun c => by simp) (fun c => ?_) (fun c m h₁ h₂ => ?_)⟩⟩
    · ext <;> simp [c.condition]
    · ext <;> simp [← h₁, ← h₂]
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q.left :=
    ⟨⟨‹_›, ‹_›⟩, ‹_›⟩
  obtain ⟨⟨_, _⟩, _⟩ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
    (q ▷ G).left := ⟨⟨MorphismProperty.of_isPullback (h₁.map (Over.forget S)) hq.1.1,
      MorphismProperty.of_isPullback (h₁.map (Over.forget S)) hq.1.2⟩,
      MorphismProperty.of_isPullback (h₁.map (Over.forget S)) hq.2⟩
  obtain ⟨⟨_, _⟩, _⟩ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0})
    (B ◁ q).left := ⟨⟨MorphismProperty.of_isPullback (h₂.map (Over.forget S)) hq.1.1,
      MorphismProperty.of_isPullback (h₂.map (Over.forget S)) hq.1.2⟩,
      MorphismProperty.of_isPullback (h₂.map (Over.forget S)) hq.2⟩
  rw [MonoidalCategory.tensorHom_def, Over.comp_left]
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

omit hk [IsMonHom q] [IsMonHom i] [Flat q.left] [Surjective q.left] [QuasiCompact q.left] in

/- English proof (translation)
Establish `hm : ∀ (j : K → O.L.ι) (y : Y'.left), π.left y ∈ LB.wchart O.L φ j → ∀ I, q.left ((ψ I).left y) ∈ O.L.U (j I)` using `fun j y hy I => by`. Establish `: (π.left ≫ φ I) y ∈ O.L.U (j I)` using `LB.wchart_le O.L φ j I hy`. Rewrite `this` using `[← hψ]`. Then use the resulting hypothesis. Establish `le : ∀ (j : K → O.L.ι) (I : K), π.left ⁻¹ᵁ LB.wchart O.L φ j ≤ (ψ I).left ⁻¹ᵁ (q.left ⁻¹ᵁ O.L.U (j I))` using `fun j I y hy => hm j y hy I`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f : ∀ j : K → O.L.ι, Γ(Y'.left, π.left ⁻¹ᵁ LB.wchart O.L φ j)ˣ, ∀ (j : K → O.L.ι) (Z : Scheme.{0}) (r : Z ⟶ Y'.left) (z : Z), π.left (r z) ∈ LB.wchart O.L φ j → gm r z _ (f j) = ∏ I, (gm (r ≫ (ψ I).left) z _ (u (j I)))⁻¹ ^ ε I := by`.

Use `⟨fun j => ∏ I, (res (le j I) (pullU (ψ I).left _ (u (j I))))⁻¹ ^ ε I, fun j Z r z hz => ?_⟩` and prove the remaining obligations. Use `(map_prod _ _ _).trans (Finset.prod_congr rfl fun I _ => ?_)` and prove the remaining obligations. Rewrite using `[map_zpow, map_inv, gm_res_pull r _ z (le j I) hz]`. Use `exists_gen_descent π (LB.LinComb O.L φ ε) f (fun j Z g₁ g₂ z e h₁ h₂ => ?_) (fun j j' y h₁ h₂ => ?_)` and prove the remaining obligations. Take `⟨t, hI, h1⟩` from `hinv Z g₁ g₂ z e`.

Establish `hc : ∀ I : K, gm (g₁.left ≫ (ψ I).left) z _ (u (j I)) = charGerm z (t I) (Multiplicative.ofAdd χ) * gm (g₂.left ≫ (ψ I).left) z _ (u (j I))` using `fun I => by`. Use `h.1 (j I) Z (t I) (g₂ ≫ ψ I) z (hm j _ h₂ I)` as an intermediate fact. Rewrite `this` using `[← hI]`. Conclude with `this`. Use `(hf j _ _ z h₁).trans (Eq.trans ?_ (hf j _ _ z h₂).symm)` and prove the remaining obligations.

Rewrite using `[Finset.prod_congr rfl fun I _ => congrArg (·⁻¹ ^ ε I) (hc I)]`. Conclude with `prod_erase_one_perm_apply_eq_zero _ _ _ h1`. Use `(hf j _ (𝟙 _) y h₁).trans (Eq.trans ?_ (congrArg₂ (· * ·) (gm_linComb O.L φ ε π.left y j j' h₁ h₂) (hf j' _ (𝟙 _) y h₂)).symm)` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun I _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_zpow, ← hψ, h.2.1 _ _ _ (ψ I).left y (hm j y h₁ I) (hm j' y h₂ I), Category.id_comp, ← inv_eq_div_mul_inv]`.
-/
theorem IsFrame.exists_gen_linComb {χ : X} {O : RigLB B}
    {u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ} (h : IsFrame q i χ O u) {Y Y' : Over S} (π : Y' ⟶ Y)
    [Flat π.left] [Surjective π.left] [QuasiCompact π.left] {K : Type} [Fintype K]
    (φ : K → (Y.left ⟶ B.left)) (ψ : K → (Y' ⟶ G)) (ε : K → ℤ)
    (hψ : ∀ I, (ψ I).left ≫ q.left = π.left ≫ φ I)
    (hinv : ∀ (Z : Over S) (g₁ g₂ : Z ⟶ Y') (z : Z.left), g₁ ≫ π = g₂ ≫ π →
      ∃ t : K → (Z ⟶ splitTorus S X), (∀ I, g₁ ≫ ψ I = (t I ≫ i) * (g₂ ≫ ψ I)) ∧
        ∏ I, charGerm z (t I) (Multiplicative.ofAdd χ) ^ ε I = 1) :
    ∃ t : LB.Gen (LB.LinComb O.L φ ε), t.IsGen := by
  have hm : ∀ (j : K → O.L.ι) (y : Y'.left), π.left y ∈ LB.wchart O.L φ j →
      ∀ I, q.left ((ψ I).left y) ∈ O.L.U (j I) := fun j y hy I => by
    have : (π.left ≫ φ I) y ∈ O.L.U (j I) := LB.wchart_le O.L φ j I hy
    rwa [← hψ] at this
  have le : ∀ (j : K → O.L.ι) (I : K),
      π.left ⁻¹ᵁ LB.wchart O.L φ j ≤ (ψ I).left ⁻¹ᵁ (q.left ⁻¹ᵁ O.L.U (j I)) :=
    fun j I y hy => hm j y hy I
  obtain ⟨f, hf⟩ : ∃ f : ∀ j : K → O.L.ι, Γ(Y'.left, π.left ⁻¹ᵁ LB.wchart O.L φ j)ˣ,
      ∀ (j : K → O.L.ι) (Z : Scheme.{0}) (r : Z ⟶ Y'.left) (z : Z),
        π.left (r z) ∈ LB.wchart O.L φ j →
        gm r z _ (f j) = ∏ I, (gm (r ≫ (ψ I).left) z _ (u (j I)))⁻¹ ^ ε I := by
    refine ⟨fun j => ∏ I, (res (le j I) (pullU (ψ I).left _ (u (j I))))⁻¹ ^ ε I,
      fun j Z r z hz => ?_⟩
    refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun I _ => ?_)
    rw [map_zpow, map_inv, gm_res_pull r _ z (le j I) hz]
  refine exists_gen_descent π (LB.LinComb O.L φ ε) f (fun j Z g₁ g₂ z e h₁ h₂ => ?_)
    (fun j j' y h₁ h₂ => ?_)
  · obtain ⟨t, hI, h1⟩ := hinv Z g₁ g₂ z e
    have hc : ∀ I : K, gm (g₁.left ≫ (ψ I).left) z _ (u (j I)) =
        charGerm z (t I) (Multiplicative.ofAdd χ) * gm (g₂.left ≫ (ψ I).left) z _ (u (j I)) :=
      fun I => by
        have := h.1 (j I) Z (t I) (g₂ ≫ ψ I) z (hm j _ h₂ I)
        rw [← hI] at this
        exact this
    refine (hf j _ _ z h₁).trans (Eq.trans ?_ (hf j _ _ z h₂).symm)
    rw [Finset.prod_congr rfl fun I _ => congrArg (·⁻¹ ^ ε I) (hc I)]
    exact prod_erase_one_perm_apply_eq_zero _ _ _ h1
  · refine (hf j _ (𝟙 _) y h₁).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_linComb O.L φ ε π.left y j j' h₁ h₂) (hf j' _ (𝟙 _) y h₂)).symm)
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [← mul_zpow, ← hψ, h.2.1 _ _ _ (ψ I).left y (hm j y h₁ I) (hm j' y h₂ I), Category.id_comp,
      ← inv_eq_div_mul_inv]

/- English proof (translation)
Take `⟨⟨_, _⟩, _⟩` from `cover_tensorHom (q := q)`. Apply the tactic sequence `have hx : ∀ k, x2 G k ≫ q = (q ⊗ₘ q) ≫ x2 B k := fun k => by fin_cases k <;> simp [x2]`. Use `h.exists_gen_linComb (q ⊗ₘ q) (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum B (x2 B) I.down).left) (fun I => psum G (x2 G) I.down) (fun I => (-1) ^ (2 - I.down.card)) (fun I => ?_) (fun Z g₁ g₂ z e => ?_)` and prove the remaining obligations. Use `congrArg Over.Hom.left (?_ : psum G (x2 G) I.down ≫ q = (q ⊗ₘ q) ≫ psum B (x2 B) I.down)` and prove the remaining obligations. Rewrite using `[psum_comp, comp_psum, funext hx]`.

Establish `ht : ∀ k, ∃ t : Z ⟶ splitTorus S X, g₁ ≫ x2 G k = (t ≫ i) * (g₂ ≫ x2 G k)` using `fun k => exists_act hk (by rw [Category.assoc, Category.assoc, hx, reassoc_of% e]) choose t ht using ht`. Use `⟨fun I => psum _ t I.down, fun I => ?_, prod_square_eq_one ((MonoidHom.eval (Multiplicative.ofAdd χ)).comp (charGerm z)) t⟩` and prove the remaining obligations. Rewrite using `[comp_psum, comp_psum, psum_comp, ← psum_mul, funext ht]`.
-/
theorem IsFrame.exists_gen_lam [IsCommMonObj G] {χ : X} {O : RigLB B}
    {u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ} (h : IsFrame q i χ O u) :
    ∃ t : LB.Gen (abelian₂ B O.L), t.IsGen := by
  obtain ⟨⟨_, _⟩, _⟩ := cover_tensorHom (q := q)
  have hx : ∀ k, x2 G k ≫ q = (q ⊗ₘ q) ≫ x2 B k := fun k => by
    fin_cases k <;> simp [x2]
  refine h.exists_gen_linComb (q ⊗ₘ q) (K := ULift.{0} (Finset (Fin 2)))
    (fun I => (psum B (x2 B) I.down).left) (fun I => psum G (x2 G) I.down)
    (fun I => (-1) ^ (2 - I.down.card)) (fun I => ?_) (fun Z g₁ g₂ z e => ?_)
  · refine congrArg Over.Hom.left
      (?_ : psum G (x2 G) I.down ≫ q = (q ⊗ₘ q) ≫ psum B (x2 B) I.down)
    rw [psum_comp, comp_psum, funext hx]
  · have ht : ∀ k, ∃ t : Z ⟶ splitTorus S X, g₁ ≫ x2 G k = (t ≫ i) * (g₂ ≫ x2 G k) := fun k =>
      exists_act hk (by rw [Category.assoc, Category.assoc, hx, reassoc_of% e])
    choose t ht using ht
    refine ⟨fun I => psum _ t I.down, fun I => ?_,
      prod_square_eq_one ((MonoidHom.eval (Multiplicative.ofAdd χ)).comp (charGerm z)) t⟩
    rw [comp_psum, comp_psum, psum_comp, ← psum_mul, funext ht]

end Laws

section Datum

attribute [local instance] SplitExt.free SplitExt.finite

variable {S : Scheme.{0}} (E : SplitExt S) {G : Over S} [GrpObj G]
  {q : G ⟶ E.B} {i : splitTorus S E.X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[E.B]))
include hk

/- English proof (translation)
Set `v : ∀ (j : E.ChartIdx) (_ : Module.Free.ChooseBasisIndex ℤ E.X), Γ(G.left, q.left ⁻¹ᵁ E.chart j)ˣ` to `fun j k => res (Scheme.Hom.preimage_mono q.left (E.chart_le j k)) (u (E.basis k) (j k))`. Establish `hv : ∀ j k (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ E.chart j → gm r z _ (v j k) = gm r z _ (u (E.basis k) (j k))` using `fun j k Z r z hz => gm_res_pre _ _ _ _ hz _`. Use `⟨{ q := q i := i q_hom := ‹_› i_hom := ‹_› q_flat := ‹_› q_surjective := ‹_› q_affine := isAffineHom_left hk isKernel := hk u := v coord := fun j V hV h => ?_ trans := fun j j' k => unit_ext fun y hy => ?_ act_le := fun j y hy => ?_ equiv := fun j k => unit_ext fun y hy => ?_ uni …` and prove the remaining obligations. Use `(isAffineOpen_and_bijective_of_weight_units S E.X G E.B q i ‹_› ‹_› ‹_› ‹_› ‹_› hk V hV _ fun χ => HasWeight.appLE ?_).2` and prove the remaining obligations. Introduce `Z t g z hz`.

Establish `hz' : q.left (((t ≫ i) * g).left z) ∈ V` using `by rwa [act_apply hk]`. Set `w : Multiplicative E.X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ` to `AddMonoidHom.toMultiplicativeLeft (E.basis.constr ℤ (fun k => Additive.ofMul (res (Scheme.Hom.preimage_mono q.left h) (v j k)))).toAddMonoidHom`. Establish `hw : ∀ k, w (Multiplicative.ofAdd (E.basis k)) = res (Scheme.Hom.preimage_mono q.left h) (v j k)` using `fun k => congrArg Additive.toMul (E.basis.constr_basis ℤ (fun k => Additive.ofMul (res (Scheme.Hom.preimage_mono q.left h) (v j k))) k)`. Establish `: (gm ((t ≫ i) * g).left z _).comp w = charGerm z t * (gm g.left z _).comp w` using `monoidHom_ext_basis E.basis fun k => by`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hw, gm_res_pre _ _ _ _ hz', gm_res_pre _ _ _ _ hz, hv _ _ _ _ _ (h hz'), hv _ _ _ _ _ (h hz)]`.

Conclude with `(hu _).1 _ Z t g z (E.chart_le j k (h hz))`. Conclude with `DFunLike.congr_fun this (Multiplicative.ofAdd χ)`. Establish `hy' : q.left y ∈ E.chart j ⊓ E.chart j'` using `hy`. Use `((gm_res (𝟙 _) y _ hy _).trans (hv j' k _ (𝟙 _) y hy.2)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_id_pull' _ _ hy' _).trans ((gm_res _ _ _ hy' _).trans ((hu _).trans_id _ _ y (E.chart_le j k hy.1) (E.chart_le j' k hy.2)))) ((gm_res (𝟙 _) y _ hy _).trans ( …` and prove the remaining obligations. Conclude with `(div_mul_cancel _ _).symm`.

Express the relevant statement in the definitionally equal form `q.left (((fst _ G ≫ i) * snd _ G).left y) ∈ E.chart j`. Rewrite using `[act_apply hk]`. Conclude with `hy`. Establish `hy' : q.left (((fst _ G ≫ i) * snd _ G).left y) ∈ E.chart j`. Rewrite using `[act_apply hk]`.

Conclude with `hy`. Use `((gm_id_res_pull _ y _ hy _).trans (hv j k _ _ y hy')).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_id_res_pull _ y _ hy _).trans (charGerm_eq y (fst _ G) (E.basis k)).symm) ((gm_id_pull' _ y hy _).trans (hv j k _ _ y hy)))).symm)` and prove the remaining obligations. Conclude with `(hu _).1 _ _ _ _ y (E.chart_le j k hy)`. Use `(map_mul _ _ _).trans ((congrArg₂ (· * ·) ((gm_id_res_pull _ y _ hy _).trans (hv j k _ _ y hy.1)) ((gm_res (𝟙 _) y _ hy _).trans ((hu _).2.2 (j k) y (mem_pull.1 hy.2)))).trans ?_)` and prove the remaining obligations. Rewrite using `[map_one, mul_inv_cancel]`.
-/
theorem exists_gtDatum (u : ∀ χ j, Γ(G.left, q.left ⁻¹ᵁ (E.O χ).L.U j)ˣ)
    (hu : ∀ χ, IsFrame q i χ (E.O χ) (u χ)) : ∃ d : E.GtDatum G, d.q = q ∧ d.i = i := by
  let v : ∀ (j : E.ChartIdx) (_ : Module.Free.ChooseBasisIndex ℤ E.X),
      Γ(G.left, q.left ⁻¹ᵁ E.chart j)ˣ := fun j k =>
    res (Scheme.Hom.preimage_mono q.left (E.chart_le j k)) (u (E.basis k) (j k))
  have hv : ∀ j k (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ E.chart j →
      gm r z _ (v j k) = gm r z _ (u (E.basis k) (j k)) := fun j k Z r z hz =>
    gm_res_pre _ _ _ _ hz _
  refine ⟨{
    q := q
    i := i
    q_hom := ‹_›
    i_hom := ‹_›
    q_flat := ‹_›
    q_surjective := ‹_›
    q_affine := isAffineHom_left hk
    isKernel := hk
    u := v
    coord := fun j V hV h => ?_
    trans := fun j j' k => unit_ext fun y hy => ?_
    act_le := fun j y hy => ?_
    equiv := fun j k => unit_ext fun y hy => ?_
    unit_norm := fun j k => unit_ext fun y hy => ?_ }, rfl, rfl⟩
  · refine (isAffineOpen_and_bijective_of_weight_units S E.X G E.B q i ‹_› ‹_› ‹_› ‹_› ‹_› hk V hV
      _ fun χ => HasWeight.appLE ?_).2
    intro Z t g z hz
    have hz' : q.left (((t ≫ i) * g).left z) ∈ V := by rwa [act_apply hk]
    let w : Multiplicative E.X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ := AddMonoidHom.toMultiplicativeLeft
      (E.basis.constr ℤ (fun k => Additive.ofMul
        (res (Scheme.Hom.preimage_mono q.left h) (v j k)))).toAddMonoidHom
    have hw : ∀ k, w (Multiplicative.ofAdd (E.basis k)) =
        res (Scheme.Hom.preimage_mono q.left h) (v j k) := fun k =>
      congrArg Additive.toMul (E.basis.constr_basis ℤ (fun k => Additive.ofMul
        (res (Scheme.Hom.preimage_mono q.left h) (v j k))) k)
    have : (gm ((t ≫ i) * g).left z _).comp w = charGerm z t * (gm g.left z _).comp w :=
      monoidHom_ext_basis E.basis fun k => by
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hw,
          gm_res_pre _ _ _ _ hz', gm_res_pre _ _ _ _ hz, hv _ _ _ _ _ (h hz'), hv _ _ _ _ _ (h hz)]
        exact (hu _).1 _ Z t g z (E.chart_le j k (h hz))
    exact DFunLike.congr_fun this (Multiplicative.ofAdd χ)
  · have hy' : q.left y ∈ E.chart j ⊓ E.chart j' := hy
    refine ((gm_res (𝟙 _) y _ hy _).trans (hv j' k _ (𝟙 _) y hy.2)).trans (Eq.trans ?_
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_id_pull' _ _ hy' _).trans
        ((gm_res _ _ _ hy' _).trans
          ((hu _).trans_id _ _ y (E.chart_le j k hy.1) (E.chart_le j' k hy.2))))
        ((gm_res (𝟙 _) y _ hy _).trans (hv j k _ (𝟙 _) y hy.1)))).symm)
    exact (div_mul_cancel _ _).symm
  · change q.left (((fst _ G ≫ i) * snd _ G).left y) ∈ E.chart j
    rw [act_apply hk]
    exact hy
  · have hy' : q.left (((fst _ G ≫ i) * snd _ G).left y) ∈ E.chart j := by
      rw [act_apply hk]
      exact hy
    refine ((gm_id_res_pull _ y _ hy _).trans (hv j k _ _ y hy')).trans (Eq.trans ?_
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_id_res_pull _ y _ hy _).trans
        (charGerm_eq y (fst _ G) (E.basis k)).symm)
        ((gm_id_pull' _ y hy _).trans (hv j k _ _ y hy)))).symm)
    exact (hu _).1 _ _ _ _ y (E.chart_le j k hy)
  · refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) ((gm_id_res_pull _ y _ hy _).trans
      (hv j k _ _ y hy.1)) ((gm_res (𝟙 _) y _ hy _).trans
        ((hu _).2.2 (j k) y (mem_pull.1 hy.2)))).trans ?_)
    rw [map_one, mul_inv_cancel]

end Datum

end ToSplit

/- English proof (translation)
Introduce `S X _ _ _ G B _ _ _ _ q i _ _ _ _ _ hk`. Use `choose O u hu using ToSplit.exists_isFrame hk`. Use `⟨O, fun χ χ' => (hu χ).exists_iso_add hk (hu χ') (hu (χ + χ')), (hu 0).exists_gen_zero hk, fun χ => (hu χ).exists_gen_lam hk, fun hB => ?_⟩` and prove the remaining obligations. Conclude with `ToSplit.exists_gtDatum (SplitExt.mk B hB X O _ _ _) hk u hu`.
-/
theorem exists_gtDatum_of_splitTorus_extension :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (G B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj B], IsAbelianScheme B → ∀ (q : G ⟶ B) (i : splitTorus S X ⟶ G), IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left → IsPullback i (toUnit _) q (η[B]) → ∃ (O : X → RigLB B) (h₁ : _) (h₂ : _) (h₃ : _), ∀ hB : IsAbelianScheme B, ∃ d : (SplitExt.mk B hB X O h₁ h₂ h₃).GtDatum G, d.q = q ∧ d.i = i := by
  intro S X _ _ _ G B _ _ _ _ q i _ _ _ _ _ hk
  choose O u hu using ToSplit.exists_isFrame hk
  refine ⟨O, fun χ χ' => (hu χ).exists_iso_add hk (hu χ') (hu (χ + χ')),
    (hu 0).exists_gen_zero hk, fun χ => (hu χ).exists_gen_lam hk, fun hB => ?_⟩
  exact ToSplit.exists_gtDatum (SplitExt.mk B hB X O _ _ _) hk u hu

end GlobalTheory
