import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section
open scoped CategoryTheory.Obj

/- English proof (translation)
Set `F` to `Over.pullback f`. Set `m : Z ⟶ F.obj (G ⊗ G)` to `lift a b ≫ Functor.LaxMonoidal.μ F G G`. Establish `key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom f) ≫ g.left = (m ≫ F.map g).left ≫ pullback.fst G.hom f`. Introduce `g`. Rewrite using `[Category.assoc, ← SplitTorusPoints.map_left_fst, Over.comp_left]`.

Conclude with `(Category.assoc _ _ _).symm`. Establish `h1 : m ≫ F.map (fst G G) = a` using `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))`. Establish `h2 : m ≫ F.map (snd G G) = b` using `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))`. Establish `h3 : m ≫ F.map μ[G] = a * b` using `Category.assoc _ _ _`. Establish `hq : e ≫ m.left ≫ pullback.fst (G ⊗ G).hom f = (lift za zb).left`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Use `key (fst G G)` as an intermediate fact. Rewrite `this` using `[h1]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (ha.trans (congrArg (fun t => t.left) (lift_fst za zb)).symm))`. Use `key (snd G G)` as an intermediate fact.

Rewrite `this` using `[h2]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (hb.trans (congrArg (fun t => t.left) (lift_snd za zb)).symm))`. Use `key μ[G]` as an intermediate fact. Rewrite `this` using `[h3]`. Rewrite using `[← this, ← Category.assoc, hq]`.

Both sides reduce to the same expression.
-/
private theorem mul_left_fst {S' S : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {Y : Over S} {Z : Over S'}
    (e : Y.left ⟶ Z.left) (a b : Z ⟶ (Over.pullback f).obj G) (za zb : Y ⟶ G)
    (ha : e ≫ a.left ≫ pullback.fst G.hom f = za.left) (hb : e ≫ b.left ≫ pullback.fst G.hom f = zb.left) :
    e ≫ (a * b).left ≫ pullback.fst G.hom f = (za * zb).left := by
  let F := Over.pullback f
  let m : Z ⟶ F.obj (G ⊗ G) := lift a b ≫ Functor.LaxMonoidal.μ F G G
  have key : ∀ g : G ⊗ G ⟶ G, (m.left ≫ pullback.fst (G ⊗ G).hom f) ≫ g.left =
      (m ≫ F.map g).left ≫ pullback.fst G.hom f := by
    intro g
    rw [Category.assoc, ← SplitTorusPoints.map_left_fst, Over.comp_left]
    exact (Category.assoc _ _ _).symm
  have h1 : m ≫ F.map (fst G G) = a := (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_fst F G G)).trans (lift_fst _ _))
  have h2 : m ≫ F.map (snd G G) = b := (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Functor.Monoidal.μ_snd F G G)).trans (lift_snd _ _))
  have h3 : m ≫ F.map μ[G] = a * b := Category.assoc _ _ _
  have hq : e ≫ m.left ≫ pullback.fst (G ⊗ G).hom f = (lift za zb).left := by
    apply pullback.hom_ext
    · have := key (fst G G)
      rw [h1] at this
      exact (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (ha.trans
        (congrArg (fun t => t.left) (lift_fst za zb)).symm))
    · have := key (snd G G)
      rw [h2] at this
      exact (Category.assoc _ _ _).trans ((congrArg (e ≫ ·) this).trans (hb.trans
        (congrArg (fun t => t.left) (lift_snd za zb)).symm))
  have := key μ[G]
  rw [h3] at this
  rw [← this, ← Category.assoc, hq]
  rfl

end

/- English proof (translation)
Establish `: IsClosedImmersion (Out.thick R I e)` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Use `infer_instance`.
-/
private theorem mono_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) : Mono (Out.thick R I e) := by
  have : IsClosedImmersion (Out.thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/- English proof (translation)
Use `⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap R S) h)), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1)))) = Spec.map _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression.
-/
private theorem exists_struct {R : Type} [CommRing R] (I : Ideal R) (k : ℕ) (S : Type) [CommRing S] [Algebra R S]
    (h : Kills I k S) : ∃ s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))),
      s ≫ Out.thick R I k = (sp (R₀ := R) S).hom := by
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap R S) h)), ?_⟩
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (k + 1)))) = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/- English proof (translation)
Set `u : Γ(Spec (CommRingCat.of S), ⊤)ˣ ≃* Sˣ` to `Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.toMulEquiv`. Use `⟨(splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight), fun t χ => ?_⟩` and prove the remaining obligations. Establish `hv : ∀ x : X, ((((splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight)) t (Multiplicative.ofAdd x) : Sˣ) : S) = (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (t.left.appTop.hom (charUnit B X x).val)` using `fun x => congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (splitTorusPointsEquiv_val B X (Over.mk s) t x)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl x`.

Conclude with `(hv x).symm`. Introduce `h`. Use extensionality with `x`. Conclude with `(hv x).trans (h x)`.
-/
private theorem exists_equiv {B : Scheme.{0}} (X : Type) [AddCommGroup X] (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ B) :
    ∃ e : (Over.mk s ⟶ splitTorus B X) ≃* (Multiplicative X →* Sˣ), ∀ t χ, e t = χ ↔
      ∀ x : X, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (t.left.appTop.hom (charUnit B X x).val) = (χ (Multiplicative.ofAdd x) : S) := by
  let u : Γ(Spec (CommRingCat.of S), ⊤)ˣ ≃* Sˣ :=
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.toMulEquiv
  refine ⟨(splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight), fun t χ => ?_⟩
  have hv : ∀ x : X, ((((splitTorusPointsEquiv B X (Over.mk s)).trans (u.monoidHomCongrRight)) t
      (Multiplicative.ofAdd x) : Sˣ) : S) = (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
        (t.left.appTop.hom (charUnit B X x).val) := fun x =>
    congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (splitTorusPointsEquiv_val B X (Over.mk s) t x)
  constructor
  · rintro rfl x
    exact (hv x).symm
  · intro h
    ext x
    exact (hv x).trans (h x)

/- English proof (translation)
Take `⟨e, he⟩` from `exists_equiv D.X S s`. Use `⟨e, fun χ z => ⟨?_, fun h => ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨w, hw, hz⟩`. Use `mono_thick I k` as an intermediate fact. Establish `hws : w ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).hom = s`.

Rewrite using `[← cancel_mono (Out.thick R I k), hs, ← Over.w z, ← hz, ← Over.w c.i]`. Simplify using `only [Category.assoc]`. Conclude with `congrArg (fun g => w ≫ c.i.left ≫ g) (Over.w (Out.fstG I k G)).symm`. Set `t : Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X` to `Over.homMk w hws`. Establish `ht : e t = χ` using `(he t χ).2 hw`.

Rewrite using `[← ht, MulEquiv.symm_apply_apply]`. Conclude with `(Category.assoc _ _ _).trans hz`. Conclude with `⟨(e.symm χ).left, (he _ χ).1 (e.apply_symm_apply χ), (Category.assoc _ _ _).symm.trans h⟩`.
-/
private theorem irel_iff {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegPre R} {k : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G)
    (S : Type) [CommRing S] [Algebra R S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (k + 1))))
    (hs : s ≫ Out.thick R I k = (sp (R₀ := R) S).hom) :
    ∃ e : (Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X) ≃* (Multiplicative D.X →* Sˣ),
      ∀ χ z, IRel c S χ z ↔ (e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k) = z.left := by
  obtain ⟨e, he⟩ := exists_equiv D.X S s
  refine ⟨e, fun χ z => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨w, hw, hz⟩
    have := mono_thick I k
    have hws : w ≫ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).hom = s := by
      rw [← cancel_mono (Out.thick R I k), hs, ← Over.w z, ← hz, ← Over.w c.i]
      simp only [Category.assoc]
      exact congrArg (fun g => w ≫ c.i.left ≫ g) (Over.w (Out.fstG I k G)).symm
    let t : Over.mk s ⟶ splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X := Over.homMk w hws
    have ht : e t = χ := (he t χ).2 hw
    rw [← ht, MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).trans hz
  · exact ⟨(e.symm χ).left, (he _ χ).1 (e.apply_symm_apply χ), (Category.assoc _ _ _).symm.trans h⟩

open scoped CategoryTheory.Obj in

/- English proof (translation)
Introduce `R _ _ I D k G _ _ c`. Use `⟨fun S _ _ hS => ?_, ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `exists_struct I k S hS`. Take `⟨e, he⟩` from `irel_iff c S s hs`. Use `⟨fun χ => ?_, fun χ χ' z z' h h' => ?_, fun χ χ' z h h' => ?_⟩` and prove the remaining obligations.

Use `⟨Over.homMk ((e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k)) ?_, (he _ _).2 rfl, fun z hz => Over.OverMorphism.ext ((he _ _).1 hz).symm⟩` and prove the remaining obligations. Rewrite using `[← hs]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Out.thick R I k) (Over.w (e.symm χ ≫ c.i)))))`. Rewrite `h`, `h'`, the goal using `[he]`. Use `c.i_hom` as an intermediate fact.

Rewrite using `[map_mul, MonObj.mul_comp]`. Conclude with `(Category.id_comp _).symm.trans (mul_left_fst (Out.thick R I k) G (Y := sp S) (Z := Over.mk s) (𝟙 _) _ _ z z' ((Category.id_comp _).trans h) ((Category.id_comp _).trans h'))`. Rewrite `h`, `h'` using `[he]`. Use `mono_thick I k` as an intermediate fact. Establish `h1 : e.symm χ ≫ c.i = e.symm χ' ≫ c.i` using `Over.OverMorphism.ext ((cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (h.trans h'.symm))`.

Conclude with `e.symm.injective (c.isKernel.hom_ext h1 (toUnit_unique _ _))`. Introduce and unpack `S _ _ S' _ _ φ χ z ⟨w, hw, hz⟩`. Use `⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ w, fun x => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, RingHom.comp_apply, hw]`. Both sides reduce to the same expression.

Rewrite using `[Category.assoc, hz]`. Both sides reduce to the same expression.
-/
theorem irel_points : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (k : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (c : Out.GtCoord I D k G), (∀ (S : Type) [CommRing S] [Algebra R S], Kills I k S → (∀ χ, ∃! z, IRel c S χ z) ∧ (∀ χ χ' z z', IRel c S χ z → IRel c S χ' z' → IRel c S (χ * χ') (z * z')) ∧ ∀ χ χ' z, IRel c S χ z → IRel c S χ' z → χ = χ') ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') χ z, IRel c S χ z → IRel c S' ((Units.map (φ : S →* S')).comp χ) (spMap φ ≫ z) := by
  intro R _ _ I D k G _ _ c
  refine ⟨fun S _ _ hS => ?_, ?_⟩
  · obtain ⟨s, hs⟩ := exists_struct I k S hS
    obtain ⟨e, he⟩ := irel_iff c S s hs
    refine ⟨fun χ => ?_, fun χ χ' z z' h h' => ?_, fun χ χ' z h h' => ?_⟩
    · refine ⟨Over.homMk ((e.symm χ ≫ c.i).left ≫ pullback.fst G.hom (Out.thick R I k)) ?_,
        (he _ _).2 rfl, fun z hz => Over.OverMorphism.ext ((he _ _).1 hz).symm⟩
      rw [← hs]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Out.thick R I k) (Over.w (e.symm χ ≫ c.i)))))
    · rw [he] at h h' ⊢
      have := c.i_hom
      rw [map_mul, MonObj.mul_comp]
      exact (Category.id_comp _).symm.trans (mul_left_fst (Out.thick R I k) G (Y := sp S) (Z := Over.mk s) (𝟙 _)
        _ _ z z' ((Category.id_comp _).trans h) ((Category.id_comp _).trans h'))
    · rw [he] at h h'
      have := mono_thick I k
      have h1 : e.symm χ ≫ c.i = e.symm χ' ≫ c.i :=
        Over.OverMorphism.ext ((cancel_mono (pullback.fst G.hom (Out.thick R I k))).1 (h.trans h'.symm))
      exact e.symm.injective (c.isKernel.hom_ext h1 (toUnit_unique _ _))
  · rintro S _ _ S' _ _ φ χ z ⟨w, hw, hz⟩
    refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ w, fun x => ?_, ?_⟩
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← RingHom.comp_apply,
        ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp, RingHom.comp_apply, hw]
      rfl
    · rw [Category.assoc, hz]
      rfl

end GlobalTheory
