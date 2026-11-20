import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R O R' Q _ _ _ _ _ _ _ I a b hP`. Use `set t : TensorProduct R O (R' ⧸ I) →ₐ[R] Q := Algebra.TensorProduct.lift a b fun _ _ => Commute.all _ _ with ht`. Establish `H0` using `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R O (R' ⧸ I))`. Establish `e1 : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) ≫ Spec.map (CommRingCat.ofHom (S` using `TensorProduct R O (R' ⧸ I)) Algebra.TensorProduct.includeLeftRingHom) = spMap (a : O →+* Q) := by`. Rewrite using `[← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `[ht]`. Establish `e2 : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) ≫ Spec.map (CommRingCat.ofHom (S` using `TensorProduct R O (R' ⧸ I)) Algebra.TensorProduct.includeRight.toRingHom) = spMap (b : R' ⧸ I →+* Q) := by`. Rewrite using `[← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `[ht]`. Establish `hiso : IsIso (Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)))`. Establish `: Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) = (hP.isoIsPullback _ _ H0).hom`.

Apply `H0.hom_ext` to reduce the goal to its premises. Rewrite using `[e1, IsPullback.isoIsPullback_hom_fst]`. Rewrite using `[e2, IsPullback.isoIsPullback_hom_snd]`. Rewrite using `[this]`. Use `infer_instance`.

Rewrite `hiso` using `[isIso_SpecMap_iff]`. Establish `hbij : Function.Bijective t` using `hiso`. Establish `hcomp : (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) = t.comp (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I))`. Apply `Algebra.TensorProduct.ext'` to reduce the goal to its premises. Introduce `x y`.

Simplify using `[ht]`. Establish `hmk : Function.Surjective (Ideal.Quotient.mkₐ R I)` using `Ideal.Quotient.mkₐ_surjective R I`. Rewrite using `[hcomp]`. Use `⟨hbij.2.comp (LinearMap.lTensor_surjective O hmk), ?_⟩` and prove the remaining obligations. Establish `: RingHom.ker (t.comp (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I))) = RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I))`.

Use extensionality with `x`. Simplify using `only [RingHom.mem_ker, AlgHom.comp_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h; exact hbij.1 (by rw [h, map_zero])`. Introduce `h`.

Rewrite using `[h, map_zero]`. Rewrite using `[this, Algebra.TensorProduct.lTensor_ker _ hmk]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem tensor_of_pullback_surj_ker : ∀ {R O R' Q : Type} [CommRing R] [CommRing O] [CommRing R'] [CommRing Q] [Algebra R O] [Algebra R R'] [Algebra R Q] (I : Ideal R') (a : O →ₐ[R] Q) (b : R' ⧸ I →ₐ[R] Q), IsPullback (spMap (a : O →+* Q)) (spMap (b : R' ⧸ I →+* Q)) (spMap (algebraMap R O)) (spMap (algebraMap R (R' ⧸ I))) → Function.Surjective (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) = I.map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R') := by
  intro R O R' Q _ _ _ _ _ _ _ I a b hP
  set t : TensorProduct R O (R' ⧸ I) →ₐ[R] Q := Algebra.TensorProduct.lift a b fun _ _ => Commute.all _ _ with ht
  have H0 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R O (R' ⧸ I))
  have e1 : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) ≫
      Spec.map (CommRingCat.ofHom (S := TensorProduct R O (R' ⧸ I)) Algebra.TensorProduct.includeLeftRingHom) =
      spMap (a : O →+* Q) := by
    rw [← Spec.map_comp]; congr 1; ext x; simp [ht]
  have e2 : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) ≫
      Spec.map (CommRingCat.ofHom (S := TensorProduct R O (R' ⧸ I)) Algebra.TensorProduct.includeRight.toRingHom) =
      spMap (b : R' ⧸ I →+* Q) := by
    rw [← Spec.map_comp]; congr 1; ext x; simp [ht]
  have hiso : IsIso (Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q))) := by
    have : Spec.map (CommRingCat.ofHom (t : TensorProduct R O (R' ⧸ I) →+* Q)) = (hP.isoIsPullback _ _ H0).hom := by
      apply H0.hom_ext
      · rw [e1, IsPullback.isoIsPullback_hom_fst]
      · rw [e2, IsPullback.isoIsPullback_hom_snd]
    rw [this]; infer_instance
  rw [isIso_SpecMap_iff] at hiso
  have hbij : Function.Bijective t := hiso
  have hcomp : (Algebra.TensorProduct.lift a (b.comp (Ideal.Quotient.mkₐ R I)) fun _ _ => Commute.all _ _) =
      t.comp (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I)) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    simp [ht]
  have hmk : Function.Surjective (Ideal.Quotient.mkₐ R I) := Ideal.Quotient.mkₐ_surjective R I
  rw [hcomp]
  refine ⟨hbij.2.comp (LinearMap.lTensor_surjective O hmk), ?_⟩
  have : RingHom.ker (t.comp (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I))) =
      RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R O) (Ideal.Quotient.mkₐ R I)) := by
    ext x
    simp only [RingHom.mem_ker, AlgHom.comp_apply]
    constructor
    · intro h; exact hbij.1 (by rw [h, map_zero])
    · intro h; rw [h, map_zero]
  rw [this, Algebra.TensorProduct.lTensor_ker _ hmk]
  congr 1
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.Mum
