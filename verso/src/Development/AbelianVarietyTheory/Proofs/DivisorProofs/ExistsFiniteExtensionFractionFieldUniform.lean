import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFieldOfPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatTors

open Polynomial in

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points`. Consider the case `exact _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points`. Consider the case `(apply _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points ..)`.
-/
theorem exists_split_ext (K : Type) [Field K] (C : Type) [CommRing C] (φ : K →+* C) (hφ : φ.Finite) :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
      ∀ (K₂ Ω : Type) [Field K₂] [Field Ω] (e : E →+* K₂) (j : K₂ →+* Ω) (ψ : C →+* Ω),
        ψ.comp φ = j.comp (e.comp (algebraMap K E)) → ∃ ψ₀ : C →+* K₂, j.comp ψ₀ = ψ := by
  first
  | exact @_root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points
  | exact _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points
  | (apply _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteFieldOfPoints.exists_finite_field_of_points ..)

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

/- English proof (translation)
Establish `hF : IsFinite (mulA A.A n).left` using `(GlobalTheory.firstFiveLaws.1.mulN (Sp K) A n hn).1`. Use `haveI : IsAffine ((𝟙_ (Over (Sp K))).left) := (inferInstance : IsAffine (Sp K))`. Set `f` to `(mulA A.A n).left`. Set `g` to `(η[A.A]).left`. Use `haveI : IsFinite f := hF`.

Use `haveI hY : IsFinite (pullback.snd f g) := inferInstance`. Use `haveI : IsAffine (pullback f g) := isAffine_of_isAffineHom (pullback.snd f g)`. Set `Y` to `pullback f g`. Set `q : Sp Γ(Y, ⊤) ⟶ Sp K` to `Y.isoSpec.inv ≫ pullback.snd f g`. Set `φ₀` to `Spec.preimage q`.

Establish `hq : spMap φ₀.hom = q` using `Spec.map_preimage q`. Establish `hfst : pullback.fst f g ≫ A.A.hom = pullback.snd f g`. Establish `h1 : f ≫ A.A.hom = A.A.hom` using `Over.w (mulA A.A n)`. Establish `h2 : g ≫ A.A.hom = 𝟙 _` using `Over.w (η[A.A])`. Rewrite using `[← h1, ← Category.assoc, pullback.condition, Category.assoc, h2, Category.comp_id]`.

Use `⟨Γ(Y, ⊤), inferInstance, φ₀.hom, Y.isoSpec.inv ≫ pullback.fst f g, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← IsFinite.SpecMap_iff]`. Express the relevant statement in the definitionally equal form `IsFinite (spMap φ₀.hom)`. Rewrite using `[hq]`. Use `infer_instance`.

Rewrite using `[hq, Category.assoc, hfst]`. Introduce `Ω _ y hy`. Set `z : Sp Ω ⟶ Y` to `pullback.lift y (y ≫ A.A.hom) (by rw [hy, Category.assoc])`. Set `w : Sp Ω ⟶ Sp Γ(Y, ⊤)` to `z ≫ Y.isoSpec.hom`. Use `⟨(Spec.preimage w).hom, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `y = Spec.map (Spec.preimage w) ≫ _`. Rewrite using `[Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]`.
-/
theorem exists_finite_tors (K : Type) [Field K] (A : PolAV (Sp K)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (C : Type) (_ : CommRing C) (φ : K →+* C) (p : Sp C ⟶ A.A.left), φ.Finite ∧ p ≫ A.A.hom = spMap φ ∧
      ∀ (Ω : Type) [Field Ω] (y : Sp Ω ⟶ A.A.left),
        y ≫ (mulA A.A n).left = y ≫ A.A.hom ≫ (η[A.A]).left → ∃ ψ : C →+* Ω, y = spMap ψ ≫ p := by
  have hF : IsFinite (mulA A.A n).left := (GlobalTheory.firstFiveLaws.1.mulN (Sp K) A n hn).1
  haveI : IsAffine ((𝟙_ (Over (Sp K))).left) := (inferInstance : IsAffine (Sp K))
  let f := (mulA A.A n).left
  let g := (η[A.A]).left
  haveI : IsFinite f := hF
  haveI hY : IsFinite (pullback.snd f g) := inferInstance
  haveI : IsAffine (pullback f g) := isAffine_of_isAffineHom (pullback.snd f g)
  let Y := pullback f g
  let q : Sp Γ(Y, ⊤) ⟶ Sp K := Y.isoSpec.inv ≫ pullback.snd f g
  let φ₀ := Spec.preimage q
  have hq : spMap φ₀.hom = q := Spec.map_preimage q
  have hfst : pullback.fst f g ≫ A.A.hom = pullback.snd f g := by
    have h1 : f ≫ A.A.hom = A.A.hom := Over.w (mulA A.A n)
    have h2 : g ≫ A.A.hom = 𝟙 _ := Over.w (η[A.A])
    rw [← h1, ← Category.assoc, pullback.condition, Category.assoc, h2, Category.comp_id]
  refine ⟨Γ(Y, ⊤), inferInstance, φ₀.hom, Y.isoSpec.inv ≫ pullback.fst f g, ?_, ?_, ?_⟩
  · rw [← IsFinite.SpecMap_iff]
    change IsFinite (spMap φ₀.hom)
    rw [hq]
    infer_instance
  · rw [hq, Category.assoc, hfst]
  · intro Ω _ y hy
    let z : Sp Ω ⟶ Y := pullback.lift y (y ≫ A.A.hom) (by rw [hy, Category.assoc])
    let w : Sp Ω ⟶ Sp Γ(Y, ⊤) := z ≫ Y.isoSpec.hom
    refine ⟨(Spec.preimage w).hom, ?_⟩
    change y = Spec.map (Spec.preimage w) ≫ _
    rw [Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst]

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

section Push
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

/- English proof (translation)
Establish `e` using `congrArg (fun z => z.left) (map_pow (pushHom h G') (𝟙 G') n)`. Establish `e2 : (pushHom h G' (𝟙 G')) ^ n = pushHom h G' (𝟙 G') ≫ mulA G n`. Rewrite using `[MonObj.comp_pow, Category.comp_id]`. Rewrite `e` using `[e2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem mulA_push (h : IsGrpPullback G' G f φ) (n : ℕ) : (mulA G' n).left ≫ φ = φ ≫ (mulA G n).left := by
  have e := congrArg (fun z => z.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e2 : (pushHom h G' (𝟙 G')) ^ n = pushHom h G' (𝟙 G') ≫ mulA G n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [e2] at e
  calc (mulA G' n).left ≫ φ = (pushHom h G' (𝟙 G' ^ n)).left := rfl
    _ = (pushHom h G' (𝟙 G') ≫ mulA G n).left := e
    _ = (𝟙 G'.left ≫ φ) ≫ (mulA G n).left := rfl
    _ = _ := by rw [Category.id_comp]

/- English proof (translation)
Establish `e` using `congrArg (fun z => z.left) (map_one (pushHom h (Over.mk (𝟙 S'))))`. Establish `e' : (𝟙 S' ≫ (η[G']).left) ≫ φ = (𝟙 S' ≫ f) ≫ (η[G]).left` using `e`. Rewrite `e'` using `[Category.id_comp, Category.id_comp]`. Then use the resulting hypothesis.
-/
theorem eta_push (h : IsGrpPullback G' G f φ) : (η[G']).left ≫ φ = f ≫ (η[G]).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (Over.mk (𝟙 S'))))
  have e' : (𝟙 S' ≫ (η[G']).left) ≫ φ = (𝟙 S' ≫ f) ≫ (η[G]).left := e
  rwa [Category.id_comp, Category.id_comp] at e'

end Push

end GlobalTheory.Mum.RatTors

namespace GlobalTheory.Mum.RatTors

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem spMap_inj {P Q : Type} [CommRing P] [CommRing Q] {u v : P →+* Q} (h : spMap u = spMap v) : u = v :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

/- English proof (translation)
Introduce `R₁ _ _ _ _ A n hn`. Take `⟨C, _, φ, p, hφ, hp, hpt⟩` from `exists_finite_tors _ A n hn`. Take `⟨E, hE, hEs⟩` from `exists_split_ext (FractionRing R₁) C φ hφ`. Use `⟨E, hE, ?_⟩` and prove the remaining obligations. Introduce and unpack `R₂ _ _ _ i₁₂ e _ he A₂ a ⟨ga, hga, hpb, -⟩ x hx`.

Set `j` to `algebraMap (FractionRing R₂) (Kb R₂)`. Establish `hge : ga = e.comp (algebraMap (FractionRing R₁) E)` using `IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => by`. Rewrite using `[RingHom.comp_apply, RingHom.comp_apply, hga, RingHom.comp_apply, he])`. Set `y` to `x.left ≫ a`. Establish `hxh : x.left ≫ A₂.A.hom = spMap j` using `Over.w x`.

Establish `hyh : y ≫ A.A.hom = spMap j ≫ spMap ga`. Express the relevant statement in the definitionally equal form `(x.left ≫ a) ≫ A.A.hom = _`. Rewrite using `[Category.assoc, hpb.1.w, ← Category.assoc, hxh]`. Establish `h1 : x.left ≫ (mulA A₂.A n).left = spMap j ≫ (η[A₂.A]).left`. Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx]`.

Both sides reduce to the same expression. Establish `htors : y ≫ (mulA A.A n).left = y ≫ A.A.hom ≫ (η[A.A]).left`. Express the relevant statement in the definitionally equal form `(x.left ≫ a) ≫ _ = (x.left ≫ a) ≫ _`. Rewrite using `[Category.assoc, ← mulA_push hpb, ← Category.assoc, h1, Category.assoc, eta_push hpb, ← Category.assoc (x.left ≫ a), hyh, Category.assoc]`. Take `⟨ψ, hψ⟩` from `hpt (Kb R₂) y htors`.

Establish `hψφ : ψ.comp φ = j.comp ga`. Use `spMap_inj ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.Ex.spMap_comp', GlobalTheory.Ex.spMap_comp', ← hp, ← Category.assoc, ← hψ, hyh]`. Take `⟨ψ₀, hψ₀⟩` from `hEs (FractionRing R₂) (Kb R₂) e j ψ (by rw [hψφ, hge])`. Establish `hψ₀φ : ψ₀.comp φ = ga`.

Use `RingHom.ext fun r => j.injective ?_` and prove the remaining obligations. Use `RingHom.congr_fun hψφ r` as an intermediate fact. Rewrite `this` using `[← hψ₀]`. Conclude with `this`. Set `y₀ : Sp (FractionRing R₂) ⟶ A.A.left` to `spMap ψ₀ ≫ p`.

Establish `hy₀ : y₀ ≫ A.A.hom = 𝟙 _ ≫ spMap ga`. Express the relevant statement in the definitionally equal form `(spMap ψ₀ ≫ p) ≫ _ = _`. Rewrite using `[Category.assoc, hp, ← GlobalTheory.Ex.spMap_comp', hψ₀φ, Category.id_comp]`. Use `⟨hpb.1.lift y₀ (𝟙 _) hy₀, hpb.1.hom_ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hpb.1.lift_fst]`.

Express the relevant statement in the definitionally equal form `y = _`. Rewrite using `[hψ, ← hψ₀, GlobalTheory.Ex.spMap_comp', Category.assoc]`. Rewrite using `[Category.assoc, hpb.1.lift_snd, Category.comp_id, hxh]`.
-/
theorem torsion_rational : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (A : PolAV (Sp (FractionRing R₁))) (n : ℕ), 1 ≤ n → ∃ E : IntermediateField (FractionRing R₁) (Kb R₁), FiniteDimensional (FractionRing R₁) E ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂) (e : E →+* FractionRing R₂), Function.Injective i₁₂ → (∀ r : R₁, e (algebraMap (FractionRing R₁) E (algebraMap R₁ (FractionRing R₁) r)) = algebraMap R₂ (FractionRing R₂) (i₁₂ r)) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → ∃ x₀ : Sp (FractionRing R₂) ⟶ A₂.A.left, x.left = spMap (algebraMap (FractionRing R₂) (Kb R₂)) ≫ x₀ := by
  intro R₁ _ _ _ _ A n hn
  obtain ⟨C, _, φ, p, hφ, hp, hpt⟩ := exists_finite_tors _ A n hn
  obtain ⟨E, hE, hEs⟩ := exists_split_ext (FractionRing R₁) C φ hφ
  refine ⟨E, hE, ?_⟩
  rintro R₂ _ _ _ i₁₂ e _ he A₂ a ⟨ga, hga, hpb, -⟩ x hx
  let j := algebraMap (FractionRing R₂) (Kb R₂)
  have hge : ga = e.comp (algebraMap (FractionRing R₁) E) :=
    IsLocalization.ringHom_ext (nonZeroDivisors R₁) (RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hga, RingHom.comp_apply, he])
  let y := x.left ≫ a
  have hxh : x.left ≫ A₂.A.hom = spMap j := Over.w x
  have hyh : y ≫ A.A.hom = spMap j ≫ spMap ga := by
    change (x.left ≫ a) ≫ A.A.hom = _
    rw [Category.assoc, hpb.1.w, ← Category.assoc, hxh]
  have h1 : x.left ≫ (mulA A₂.A n).left = spMap j ≫ (η[A₂.A]).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx]
    rfl
  have htors : y ≫ (mulA A.A n).left = y ≫ A.A.hom ≫ (η[A.A]).left := by
    change (x.left ≫ a) ≫ _ = (x.left ≫ a) ≫ _
    rw [Category.assoc, ← mulA_push hpb, ← Category.assoc, h1, Category.assoc, eta_push hpb,
      ← Category.assoc (x.left ≫ a), hyh, Category.assoc]
  obtain ⟨ψ, hψ⟩ := hpt (Kb R₂) y htors
  have hψφ : ψ.comp φ = j.comp ga := by
    refine spMap_inj ?_
    rw [GlobalTheory.Ex.spMap_comp', GlobalTheory.Ex.spMap_comp', ← hp, ← Category.assoc, ← hψ, hyh]
  obtain ⟨ψ₀, hψ₀⟩ := hEs (FractionRing R₂) (Kb R₂) e j ψ (by rw [hψφ, hge])
  have hψ₀φ : ψ₀.comp φ = ga := by
    refine RingHom.ext fun r => j.injective ?_
    have := RingHom.congr_fun hψφ r
    rw [← hψ₀] at this
    exact this
  let y₀ : Sp (FractionRing R₂) ⟶ A.A.left := spMap ψ₀ ≫ p
  have hy₀ : y₀ ≫ A.A.hom = 𝟙 _ ≫ spMap ga := by
    change (spMap ψ₀ ≫ p) ≫ _ = _
    rw [Category.assoc, hp, ← GlobalTheory.Ex.spMap_comp', hψ₀φ, Category.id_comp]
  refine ⟨hpb.1.lift y₀ (𝟙 _) hy₀, hpb.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hpb.1.lift_fst]
    change y = _
    rw [hψ, ← hψ₀, GlobalTheory.Ex.spMap_comp', Category.assoc]
  · rw [Category.assoc, hpb.1.lift_snd, Category.comp_id, hxh]

end GlobalTheory.Mum.RatTors
