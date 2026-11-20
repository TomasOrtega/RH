import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareActionSectionsGenerated
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfFieldExtension

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointDesc

/- English proof (translation)
Take `⟨t, ht⟩` from `H`. Substitute `hm` using the available equality. Conclude with `⟨LB.pullGen L (fun _ : PUnit => f) (fun _ => 1) t h, DVR.pullGen_isGen L (fun _ : PUnit => f) (fun _ => 1) t ht h⟩`.
-/
theorem hasGen_of_comp {X Y Z : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (h : Z ⟶ Y) (m : Z ⟶ X)
    (hm : h ≫ f = m) (H : HasGen (L.pull f)) : HasGen (L.pull m) := by
  obtain ⟨t, ht⟩ := H
  subst hm
  exact ⟨LB.pullGen L (fun _ : PUnit => f) (fun _ => 1) t h,
    DVR.pullGen_isGen L (fun _ : PUnit => f) (fun _ => 1) t ht h⟩

/- English proof (translation)
Take `⟨t, ht⟩` from `H`. Conclude with `GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hL _) (pull_isLB (pull_isLB hL f) h) (GlobalTheory.FamRep.lbIso_pull_pull hL f h).symm t ht`.
-/
theorem hasGen_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (h : Z ⟶ Y)
    (H : HasGen (L.pull (h ≫ f))) : HasGen ((L.pull f).pull h) := by
  obtain ⟨t, ht⟩ := H
  exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hL _) (pull_isLB (pull_isLB hL f) h)
    (GlobalTheory.FamRep.lbIso_pull_pull hL f h).symm t ht

/- English proof (translation)
Introduce `A _ hA M hM T x U y t ht hU H`. Establish `hL : (abelian₂ A M).IsLB` using `LB.isLB_linComb hM _ _`. Set `x0 : U.toScheme` to `⟨t, ht⟩`. Set `K : Type` to `U.toScheme.residueField x0`. Use `letI : Field K := inferInstanceAs (Field (U.toScheme.residueField x0))`.

Set `q : Sp K ⟶ U.toScheme` to `U.toScheme.fromSpecResidueField x0`. Set `p : Sp K ⟶ T.left` to `q ≫ U.ι`. Set `φ` to `Spec.preimage (p ≫ T.hom)`. Set `β : ℂ →+* K` to `φ.hom`. Establish `hβ : spMap β = p ≫ T.hom` using `Spec.map_preimage _`.

Set `Tk : Over (Sp ℂ)` to `Over.mk (spMap β)`. Set `pk : Tk ⟶ T` to `Over.homMk p hβ.symm`. Establish `hxy : pk ≫ x = toUnit Tk ≫ y` using `by ext1`. Simplify using `only [Over.comp_left, Over.homMk_left, pk, Over.toUnit_left]`. Use `show (q ≫ U.ι) ≫ x.left = Tk.hom ≫ y.left`.

Simplify using `only [Tk, Over.mk_hom, hβ, p, Category.assoc, hU]`. Set `e : A ⟶ A ⊗ 𝟙_ (Over (Sp ℂ))` to `lift (𝟙 A) (toUnit A)`. Set `g` to `lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)`. Establish `sq : (A ◁ pk) ≫ lift (fst A T) (snd A T ≫ x) = fst A Tk ≫ e ≫ g`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises.

Simplify using `[e, g]`. Simplify using `only [Category.assoc, lift_snd, e, g, lift_fst_assoc, lift_snd_assoc]`. Rewrite using `[whiskerLeft_snd_assoc, hxy, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Conclude with `toUnit_unique _ _`.

Establish `H₁ : HasGen ((abelian₂ A M).pull ((fst A Tk).left ≫ (e ≫ g).left))` using `hasGen_of_comp _ (A ◁ pk).left _ (by rw [← Over.comp_left, sq, Over.comp_left]) H`. Establish `H₂` using `hasGen_pull_pull hL (e ≫ g).left (fst A Tk).left H₁`. Establish `hpb : IsPullback (fst A Tk).left (snd A Tk).left A.hom (spMap β)` using `IsPullback.of_hasPullback _ _`. Take `⟨u, hu⟩` from `GlobalTheory.FieldTriv.exists_gen_of_field_extension ℂ K β A hA _ (fst A Tk).left (snd A Tk).left hpb ((abelian₂ A M).pull (e ≫ g).left) (pull_isLB hL _) H₂`. Use `hasGen_of_comp (e ≫ g).left (fst A (𝟙_ (Over (Sp ℂ)))).left _ ?_ ⟨u, hu⟩` and prove the remaining obligations.

Rewrite using `[← Over.comp_left]`. Use `congr 1`. Rewrite using `[← Category.assoc]`. Establish `: fst A (𝟙_ (Over (Sp ℂ))) ≫ e = 𝟙 _`. Apply `CartesianMonoidalCategory.hom_ext` to reduce the goal to its premises.

Simplify using `[e]`. Simplify using `only [e, Category.assoc, lift_snd, Category.id_comp]`. Conclude with `toUnit_unique _ _`. Rewrite using `[this, Category.id_comp]`.
-/
theorem hasGen_lam_pull_of_eq_on_open : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A) (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (t : T.left), t ∈ U →
      U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) := by
  intro A _ hA M hM T x U y t ht hU H
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _

  let x0 : U.toScheme := ⟨t, ht⟩
  let K : Type := U.toScheme.residueField x0
  letI : Field K := inferInstanceAs (Field (U.toScheme.residueField x0))
  let q : Sp K ⟶ U.toScheme := U.toScheme.fromSpecResidueField x0
  let p : Sp K ⟶ T.left := q ≫ U.ι
  let φ := Spec.preimage (p ≫ T.hom)
  let β : ℂ →+* K := φ.hom
  have hβ : spMap β = p ≫ T.hom := Spec.map_preimage _
  let Tk : Over (Sp ℂ) := Over.mk (spMap β)
  let pk : Tk ⟶ T := Over.homMk p hβ.symm
  have hxy : pk ≫ x = toUnit Tk ≫ y := by
    ext1
    simp only [Over.comp_left, Over.homMk_left, pk, Over.toUnit_left]
    show (q ≫ U.ι) ≫ x.left = Tk.hom ≫ y.left
    simp only [Tk, Over.mk_hom, hβ, p, Category.assoc, hU]
  let e : A ⟶ A ⊗ 𝟙_ (Over (Sp ℂ)) := lift (𝟙 A) (toUnit A)
  let g := lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)
  have sq : (A ◁ pk) ≫ lift (fst A T) (snd A T ≫ x) = fst A Tk ≫ e ≫ g := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [e, g]
    · simp only [Category.assoc, lift_snd, e, g, lift_fst_assoc, lift_snd_assoc]
      rw [whiskerLeft_snd_assoc, hxy, ← Category.assoc, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
  have H₁ : HasGen ((abelian₂ A M).pull ((fst A Tk).left ≫ (e ≫ g).left)) :=
    hasGen_of_comp _ (A ◁ pk).left _ (by rw [← Over.comp_left, sq, Over.comp_left]) H
  have H₂ := hasGen_pull_pull hL (e ≫ g).left (fst A Tk).left H₁
  have hpb : IsPullback (fst A Tk).left (snd A Tk).left A.hom (spMap β) := IsPullback.of_hasPullback _ _
  obtain ⟨u, hu⟩ := GlobalTheory.FieldTriv.exists_gen_of_field_extension ℂ K β A hA _ (fst A Tk).left (snd A Tk).left hpb
    ((abelian₂ A M).pull (e ≫ g).left) (pull_isLB hL _) H₂
  refine hasGen_of_comp (e ≫ g).left (fst A (𝟙_ (Over (Sp ℂ)))).left _ ?_ ⟨u, hu⟩
  rw [← Over.comp_left]
  congr 1
  rw [← Category.assoc]
  have : fst A (𝟙_ (Over (Sp ℂ))) ≫ e = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [e]
    · simp only [e, Category.assoc, lift_snd, Category.id_comp]
      exact toUnit_unique _ _
  rw [this, Category.id_comp]

end GlobalTheory.PointDesc
