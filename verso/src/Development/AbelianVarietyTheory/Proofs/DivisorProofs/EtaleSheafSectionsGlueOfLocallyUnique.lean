import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.SecGlueLoc

/- English proof (translation)
The claim follows from `(isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)`.
-/
theorem isSheaf_forget {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)

/- English proof (translation)
Simplify using `only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]`.
-/
theorem res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res h (Sec.res g x) = Sec.res (h ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/- English proof (translation)
The claim follows from `((isSheaf_forget F) S hS).isSeparatedFor.ext (fun V g hg => h V g hg)`.
-/
theorem ext_of_sieve {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (S : Sieve U)
    (hS : S ∈ Scheme.etaleTopology U) (s t : Sec F U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g s = Sec.res g t) : s = t :=
  ((isSheaf_forget F) S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

/- English proof (translation)
Take `⟨S, hS, hP⟩` from `h3`. Set `t : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) S.arrows` to `fun V g hg => (hP V g hg).choose`. Establish `ht : ∀ (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g), A V (g ≫ x) (t g hg)` using `fun V g hg => (hP V g hg).choose_spec`. Establish `hc : t.Compatible`. Introduce `Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ w`.

Express the relevant statement in the definitionally equal form `Sec.res g₁ (t f₁ hf₁) = Sec.res g₂ (t f₂ hf₂)`. Establish `a1` using `h1 _ _ g₁ _ _ (ht _ f₁ hf₁)`. Establish `a2` using `h1 _ _ g₂ _ _ (ht _ f₂ hf₂)`. Rewrite `a1` using `[← Category.assoc, w]`. Rewrite `a2` using `[← Category.assoc]`.

Conclude with `h2 _ _ _ _ a1 a2`. Take `⟨s, hs, -⟩` from `(isSheaf_forget F) S hS t hc`. Use `⟨s, S, hS, fun V g hg => ?_⟩` and prove the remaining obligations. Establish `e : Sec.res g s = t g hg` using `hs g hg`. Use `show A V (g ≫ x) (Sec.res g s)`.

Rewrite using `[e]`. Conclude with `ht V g hg`.
-/
theorem exists_loc {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0})
    (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), A U x s → A V (g ≫ x) (Sec.res g s))
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t)
    (U : Scheme.{0}) (x : U ⟶ X) (h3 : Loc U fun V g => ∃ s, A V (g ≫ x) s) :
    ∃ s : Sec F U, Loc U fun V g => A V (g ≫ x) (Sec.res g s) := by
  obtain ⟨S, hS, hP⟩ := h3
  let t : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) S.arrows :=
    fun V g hg => (hP V g hg).choose
  have ht : ∀ (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g), A V (g ≫ x) (t g hg) :=
    fun V g hg => (hP V g hg).choose_spec
  have hc : t.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ w
    change Sec.res g₁ (t f₁ hf₁) = Sec.res g₂ (t f₂ hf₂)
    have a1 := h1 _ _ g₁ _ _ (ht _ f₁ hf₁)
    have a2 := h1 _ _ g₂ _ _ (ht _ f₂ hf₂)
    rw [← Category.assoc, w] at a1
    rw [← Category.assoc] at a2
    exact h2 _ _ _ _ a1 a2
  obtain ⟨s, hs, -⟩ := (isSheaf_forget F) S hS t hc
  refine ⟨s, S, hS, fun V g hg => ?_⟩
  have e : Sec.res g s = t g hg := hs g hg
  show A V (g ≫ x) (Sec.res g s)
  rw [e]
  exact ht V g hg

/- English proof (translation)
Take `⟨S, hS, hPs⟩` from `hs`. Take `⟨T, hT, hPt⟩` from `ht`. Use `ext_of_sieve F (S ⊓ T) (Scheme.etaleTopology.intersection_covering hS hT) s t (fun V g hg => ?_)` and prove the remaining obligations. Conclude with `h2 V (g ≫ x) _ _ (hPs V g hg.1) (hPt V g hg.2)`.
-/
theorem loc_unique {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0})
    (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop)
    (h2 : ∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t)
    (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U)
    (hs : Loc U fun V g => A V (g ≫ x) (Sec.res g s)) (ht : Loc U fun V g => A V (g ≫ x) (Sec.res g t)) :
    s = t := by
  obtain ⟨S, hS, hPs⟩ := hs
  obtain ⟨T, hT, hPt⟩ := ht
  refine ext_of_sieve F (S ⊓ T) (Scheme.etaleTopology.intersection_covering hS hT) s t (fun V g hg => ?_)
  exact h2 V (g ≫ x) _ _ (hPs V g hg.1) (hPt V g hg.2)

end GlobalTheory.EtC.SecGlueLoc

open GlobalTheory.EtC.SecGlueLoc in

/- English proof (translation)
Introduce `R _ F X A h1 h2 h3`. Set `e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U` to `fun U x => (exists_loc F X A h1 h2 U x (h3 U x)).choose`. Establish `he : ∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => A V (g ≫ x) (Sec.res g (e U x))` using `fun U x => (exists_loc F X A h1 h2 U x (h3 U x)).choose_spec`. Use `⟨e, fun V U g x => ?_, fun U x s hs => ?_⟩` and prove the remaining obligations. Use `loc_unique F X A h2 V (g ≫ x) _ _ ?_ (he V (g ≫ x))` and prove the remaining obligations.

Take `⟨S, hS, hP⟩` from `he U x`. Use `⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W h hh => ?_⟩` and prove the remaining obligations. Use `show A W (h ≫ g ≫ x) (Sec.res h (Sec.res g (e U x)))`. Rewrite using `[res_comp, ← Category.assoc]`. Conclude with `hP W (h ≫ g) hh`.

Use `loc_unique F X A h2 U x _ _ (he U x) ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h1 V U g x s hs⟩` and prove the remaining obligations.
-/
theorem GlobalTheory.EtC.secGlue_of_loc : ∀ {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop),
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), A U x s → A V (g ≫ x) (Sec.res g s)) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => ∃ s, A V (g ≫ x) s) →
    ∃ e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (e U x) = e V (g ≫ x)) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (s : Sec F U), A U x s → e U x = s := by
  intro R _ F X A h1 h2 h3
  let e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U := fun U x => (exists_loc F X A h1 h2 U x (h3 U x)).choose
  have he : ∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => A V (g ≫ x) (Sec.res g (e U x)) :=
    fun U x => (exists_loc F X A h1 h2 U x (h3 U x)).choose_spec
  refine ⟨e, fun V U g x => ?_, fun U x s hs => ?_⟩
  · refine loc_unique F X A h2 V (g ≫ x) _ _ ?_ (he V (g ≫ x))
    obtain ⟨S, hS, hP⟩ := he U x
    refine ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W h hh => ?_⟩
    show A W (h ≫ g ≫ x) (Sec.res h (Sec.res g (e U x)))
    rw [res_comp, ← Category.assoc]
    exact hP W (h ≫ g) hh
  · refine loc_unique F X A h2 U x _ _ (he U x) ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h1 V U g x s hs⟩

end
