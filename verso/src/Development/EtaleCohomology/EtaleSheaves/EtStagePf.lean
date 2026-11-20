import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.SpreadOf
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.RingHom.Etale

noncomputable section
open CategoryTheory Limits TensorProduct

namespace LateralTheory.E.EtStagePf

/- English proof (translation)
Set `_` to `f.hom.toAlgebra`. Establish `h : Algebra.Etale A T` using `hf`. Take `⟨A₀, B₀, _, _, hfg, het, ⟨e⟩⟩` from `Algebra.Etale.exists_subalgebra_fg ℤ A T`. Establish `hft : Algebra.FiniteType ℤ A₀` using `(Subalgebra.fg_iff_finiteType A₀).mp hfg`. Establish `hfp : Algebra.FinitePresentation ℤ A₀` using `Algebra.FinitePresentation.of_finiteType.mp hft`.

Use `⟨CommRingCat.of A₀, CommRingCat.of B₀, CommRingCat.ofHom (algebraMap A₀ A), CommRingCat.ofHom (algebraMap A₀ B₀), CommRingCat.ofHom (e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `RingHom.finitePresentation_algebraMap.mpr hfp` as an intermediate fact. Rewrite `this` using `[RingHom.ext_int (algebraMap ℤ A₀) (Int.castRingHom A₀)]`. Then use the resulting hypothesis. Conclude with `RingHom.etale_algebraMap.mpr het`. Use `(CommRingCat.isPushout_tensorProduct A₀ A B₀).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm.toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_` and prove the remaining obligations.

Use extensionality with `x`. Conclude with `e.symm.commutes x`. Use extensionality with `x`. Both sides reduce to the same expression.
-/
theorem exists_model {A T : CommRingCat.{0}} (f : A ⟶ T) (hf : f.hom.Etale) :
    ∃ (A₀ B₀ : CommRingCat.{0}) (a : A₀ ⟶ A) (f₀ : A₀ ⟶ B₀) (b : B₀ ⟶ T),
      (Int.castRingHom A₀).FinitePresentation ∧ f₀.hom.Etale ∧ IsPushout a f₀ f b := by
  let _ := f.hom.toAlgebra
  have h : Algebra.Etale A T := hf
  obtain ⟨A₀, B₀, _, _, hfg, het, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ A T
  have hft : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have hfp : Algebra.FinitePresentation ℤ A₀ := Algebra.FinitePresentation.of_finiteType.mp hft
  refine ⟨CommRingCat.of A₀, CommRingCat.of B₀, CommRingCat.ofHom (algebraMap A₀ A),
    CommRingCat.ofHom (algebraMap A₀ B₀),
    CommRingCat.ofHom (e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_, ?_⟩
  · have := RingHom.finitePresentation_algebraMap.mpr hfp
    rwa [RingHom.ext_int (algebraMap ℤ A₀) (Int.castRingHom A₀)] at this
  · exact RingHom.etale_algebraMap.mpr het
  · refine (CommRingCat.isPushout_tensorProduct A₀ A B₀).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.symm.toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_
    · ext x
      exact e.symm.commutes x
    · ext x
      rfl

/- English proof (translation)
Introduce `J _ _ D c hc _ _ T _ f _ _ _ hf`. Take `⟨A₀, B₀, a, f₀, b, hfp, het, hP⟩` from `exists_model f hf`. Set `α : (Functor.const J).obj (CommRingCat.of ℤ) ⟶ D` to `{ app := fun i => CommRingCat.ofHom (Int.castRingHom _) naturality := fun _ _ _ => CommRingCat.hom_ext (RingHom.ext_int _ _) }`. Take `⟨k, a', -, ha⟩` from `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (CommRingCat.of ℤ) D α (CommRingCat.ofHom (Int.castRingHom A₀)) c hc hfp a (fun _ => CommRingCat.hom_ext (RingHom.ext_int _ _))`. Substitute `ha` using the available equality.

Establish `hQ` using `IsPushout.of_hasPushout a' f₀`. Establish `hw : a' ≫ c.ι.app k ≫ f = f₀ ≫ b` using `by rw [← hP.w, Category.assoc]`. Use `⟨k, pushout a' f₀, pushout.inl a' f₀, pushout.desc (c.ι.app k ≫ f) b hw, ?_, ?_⟩` and prove the remaining obligations. Use `IsPushout.of_left ?_ (pushout.inl_desc _ _ _).symm hQ` and prove the remaining obligations. Rewrite using `[pushout.inr_desc]`.

Conclude with `hP`. Use `(RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := @RingHom.Etale)).mpr RingHom.Etale.isStableUnderBaseChange` as an intermediate fact. Conclude with `this.of_isPushout hQ het`.
-/
theorem EtStage_of : LateralTheory.E.SpreadPf.Cut.EtStage := by
  intro J _ _ D c hc _ _ T _ f _ _ _ hf
  obtain ⟨A₀, B₀, a, f₀, b, hfp, het, hP⟩ := exists_model f hf
  let α : (Functor.const J).obj (CommRingCat.of ℤ) ⟶ D :=
    { app := fun i => CommRingCat.ofHom (Int.castRingHom _)
      naturality := fun _ _ _ => CommRingCat.hom_ext (RingHom.ext_int _ _) }
  obtain ⟨k, a', -, ha⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (CommRingCat.of ℤ) D α
    (CommRingCat.ofHom (Int.castRingHom A₀)) c hc hfp a
    (fun _ => CommRingCat.hom_ext (RingHom.ext_int _ _))
  subst ha
  have hQ := IsPushout.of_hasPushout a' f₀
  have hw : a' ≫ c.ι.app k ≫ f = f₀ ≫ b := by rw [← hP.w, Category.assoc]
  refine ⟨k, pushout a' f₀, pushout.inl a' f₀, pushout.desc (c.ι.app k ≫ f) b hw, ?_, ?_⟩
  · refine IsPushout.of_left ?_ (pushout.inl_desc _ _ _).symm hQ
    rw [pushout.inr_desc]
    exact hP
  · have := (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := @RingHom.Etale)).mpr
      RingHom.Etale.isStableUnderBaseChange
    exact this.of_isPushout hQ het

end LateralTheory.E.EtStagePf
