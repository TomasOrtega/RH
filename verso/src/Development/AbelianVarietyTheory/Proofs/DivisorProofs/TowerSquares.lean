import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.TowerSq

/- English proof (translation)
Use `IsPullback.of_isLimit (c := PullbackCone.mk h (𝟙 X) (by simp)) (PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => ?_) (fun s m _ h2 => ?_))` and prove the remaining obligations. Rewrite using `[← cancel_mono f, Category.assoc]`. Conclude with `s.condition.symm`. Conclude with `Category.comp_id _`. Simplify using `using h2`.
-/
theorem isPullback_id_of_mono {C : Type*} [Category C] {X Y Z : C} (h : X ⟶ Y) (f : Y ⟶ Z) [Mono f] :
    IsPullback h (𝟙 X) f (h ≫ f) := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk h (𝟙 X) (by simp)) (PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => ?_)
    (fun s m _ h2 => ?_))
  · rw [← cancel_mono f, Category.assoc]
    exact s.condition.symm
  · exact Category.comp_id _
  · simpa using h2

/- English proof (translation)
Establish `: IsClosedImmersion (thick R I e)` using `IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective`. Use `infer_instance`.
-/
theorem mono_thick' (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/- English proof (translation)
Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression.
-/
theorem thickTrans_thick' (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) :
    thickTrans R I e ≫ thick R I (e + 1) = thick R I e := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end GlobalTheory.FormalAlg.TowerSq

open GlobalTheory.FormalAlg.TowerSq in

/- English proof (translation)
Introduce `R _ I Y β hβ`. Use `⟨fun e => ?_, fun γ h0 hγ e => ?_⟩` and prove the remaining obligations. Use `mono_thick' R I (e + 1)` as an intermediate fact. Establish `h` using `(hβ e).paste_vert (isPullback_id_of_mono (thickTrans R I e) (thick R I (e + 1)))`. Rewrite `h` using `[thickTrans_thick', Category.comp_id]`.

Conclude with `h`. Establish `hc : ∀ e, ∃ u : Spec (CommRingCat.of (R ⧸ I ^ (0 + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), u ≫ thick R I e = thick R I 0 ∧ IsPullback (γ e) (Y 0).hom (Y e).hom u`. Introduce `e`. Proceed by induction on `e with`. Consider the case `zero`.

Rewrite using `[h0]`. Conclude with `⟨𝟙 _, Category.id_comp _, IsPullback.of_horiz_isIso ⟨by simp⟩⟩`. Consider the case `succ e ih`. Take `⟨u, hu, hp⟩` from `ih`. Use `⟨u ≫ thickTrans R I e, by rw [Category.assoc, thickTrans_thick', hu], ?_⟩` and prove the remaining obligations.

Rewrite using `[← hγ e]`. Conclude with `hp.paste_horiz (hβ e)`. Take `⟨u, hu, hp⟩` from `hc e`. Use `mono_thick' R I e` as an intermediate fact. Establish `h` using `hp.paste_vert (isPullback_id_of_mono u (thick R I e))`.

Rewrite `h` using `[hu, Category.comp_id]`. Conclude with `h`.
-/
theorem GlobalTheory.FormalAlg.towerSquares : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsPullback (β e) (Y e).hom ((Y (e + 1)).hom ≫ thick R I (e + 1)) (thick R I e)) ∧ ∀ γ : ∀ e, (Y 0).left ⟶ (Y e).left, γ 0 = 𝟙 _ → (∀ e, γ e ≫ β e = γ (e + 1)) → ∀ e, IsPullback (γ e) (Y 0).hom ((Y e).hom ≫ thick R I e) (thick R I 0) := by
  intro R _ I Y β hβ
  refine ⟨fun e => ?_, fun γ h0 hγ e => ?_⟩
  · have := mono_thick' R I (e + 1)
    have h := (hβ e).paste_vert (isPullback_id_of_mono (thickTrans R I e) (thick R I (e + 1)))
    rw [thickTrans_thick', Category.comp_id] at h
    exact h
  · have hc : ∀ e, ∃ u : Spec (CommRingCat.of (R ⧸ I ^ (0 + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))),
        u ≫ thick R I e = thick R I 0 ∧ IsPullback (γ e) (Y 0).hom (Y e).hom u := by
      intro e
      induction e with
      | zero =>
        rw [h0]
        exact ⟨𝟙 _, Category.id_comp _, IsPullback.of_horiz_isIso ⟨by simp⟩⟩
      | succ e ih =>
        obtain ⟨u, hu, hp⟩ := ih
        refine ⟨u ≫ thickTrans R I e, by rw [Category.assoc, thickTrans_thick', hu], ?_⟩
        rw [← hγ e]
        exact hp.paste_horiz (hβ e)
    obtain ⟨u, hu, hp⟩ := hc e
    have := mono_thick' R I e
    have h := hp.paste_vert (isPullback_id_of_mono u (thick R I e))
    rw [hu, Category.comp_id] at h
    exact h
