import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbEnd

/- English proof (translation)
Introduce `S A _ hA φ hgeo`. Use `haveI : IsProper A.hom := hA.proper`. Use `haveI : IsProper (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance`. Use `haveI : IsProper φ.left := IsProper.of_comp φ.left A.hom`. Use `haveI : LocallyQuasiFinite φ.left := by`.

Use `LocallyQuasiFinite.of_finite_preimage_singleton φ.left fun y => ?_` and prove the remaining obligations. Set `K` to `AlgebraicClosure (A.left.residueField y)`. Set `u : Spec (CommRingCat.of K) ⟶ A.left` to `Spec.map (CommRingCat.ofHom (algebraMap (A.left.residueField y) K)) ≫ A.left.fromSpecResidueField y`. Set `t` to `u ≫ A.hom`. Use `haveI := hgeo K t`.

Set `φ'` to `((Over.pullback t).map φ).left`. Set `p : Spec (CommRingCat.of K)` to `(⊥ : PrimeSpectrum K)`. Establish `hup : u p = y` using `Scheme.fromSpecResidueField_apply y _`. Set `v : Spec (CommRingCat.of K) ⟶ pullback A.hom t` to `pullback.lift u (𝟙 _) (by simp [t])`. Use `((φ'.finite_preimage_singleton (v p)).image (pullback.fst A.hom t)).subset fun x hx => ?_` and prove the remaining obligations.

Establish `hx' : φ.left x = u p` using `by rw [hup]; exact hx`. Take `⟨w, hw1, hw2⟩` from `Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := u) x p hx'`. Set `m : pullback φ.left u ⟶ pullback A.hom t` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by`. Rewrite using `[← Over.w φ, ← Category.assoc, pullback.condition, Category.assoc])`. Establish `hm1 : m ≫ pullback.fst A.hom t = pullback.fst _ _` using `pullback.lift_fst _ _ _`.

Establish `hφ1 : φ' ≫ pullback.fst A.hom t = pullback.fst A.hom t ≫ φ.left` using `(GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ).w.symm`. Establish `hφ2 : φ' ≫ pullback.snd A.hom t = pullback.snd A.hom t` using `pullback.lift_snd _ _ _`. Establish `hmv : m ≫ φ' = pullback.snd φ.left u ≫ v`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hφ1, ← Category.assoc, hm1, Category.assoc, pullback.lift_fst, pullback.condition]`.

Rewrite using `[Category.assoc, hφ2, pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]`. Use `⟨m w, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ' (m w) = v p`. Rewrite using `[← Scheme.Hom.comp_apply, hmv, Scheme.Hom.comp_apply, hw2]`. Rewrite using `[← Scheme.Hom.comp_apply, hm1, hw1]`.

Conclude with `IsFinite.of_isProper_of_locallyQuasiFinite φ.left`.
-/
theorem isFinite_of_isFinite_geomFibres :
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (φ : A ⟶ A),
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), IsFinite ((Over.pullback t).map φ).left) →
    IsFinite φ.left := by
  intro S A _ hA φ hgeo
  haveI : IsProper A.hom := hA.proper
  haveI : IsProper (φ.left ≫ A.hom) := by rw [Over.w φ]; infer_instance
  haveI : IsProper φ.left := IsProper.of_comp φ.left A.hom
  haveI : LocallyQuasiFinite φ.left := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton φ.left fun y => ?_
    let K := AlgebraicClosure (A.left.residueField y)
    let u : Spec (CommRingCat.of K) ⟶ A.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (A.left.residueField y) K)) ≫
        A.left.fromSpecResidueField y
    let t := u ≫ A.hom
    haveI := hgeo K t
    let φ' := ((Over.pullback t).map φ).left
    let p : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
    have hup : u p = y := Scheme.fromSpecResidueField_apply y _
    let v : Spec (CommRingCat.of K) ⟶ pullback A.hom t := pullback.lift u (𝟙 _) (by simp [t])
    refine ((φ'.finite_preimage_singleton (v p)).image (pullback.fst A.hom t)).subset fun x hx => ?_
    have hx' : φ.left x = u p := by rw [hup]; exact hx
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := u) x p hx'
    let m : pullback φ.left u ⟶ pullback A.hom t :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
        rw [← Over.w φ, ← Category.assoc, pullback.condition, Category.assoc])
    have hm1 : m ≫ pullback.fst A.hom t = pullback.fst _ _ := pullback.lift_fst _ _ _
    have hφ1 : φ' ≫ pullback.fst A.hom t = pullback.fst A.hom t ≫ φ.left :=
      (GlobalTheory.AbLaw.MulN.isPullback_baseChange t φ).w.symm
    have hφ2 : φ' ≫ pullback.snd A.hom t = pullback.snd A.hom t := pullback.lift_snd _ _ _
    have hmv : m ≫ φ' = pullback.snd φ.left u ≫ v := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφ1, ← Category.assoc, hm1, Category.assoc, pullback.lift_fst, pullback.condition]
      · rw [Category.assoc, hφ2, pullback.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id]
    refine ⟨m w, ?_, ?_⟩
    · change φ' (m w) = v p
      rw [← Scheme.Hom.comp_apply, hmv, Scheme.Hom.comp_apply, hw2]
    · rw [← Scheme.Hom.comp_apply, hm1, hw1]
  exact IsFinite.of_isProper_of_locallyQuasiFinite φ.left

end GlobalTheory.AbEnd
