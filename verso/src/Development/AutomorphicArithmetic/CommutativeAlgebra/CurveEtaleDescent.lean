import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.CommutativeAlgebra.CechDescentTwistOfProperSurjectiveStrictlyHensel
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EquivOfStalkwiseBaseChange
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TateTwistFinitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

/- English proof (translation)
Introduce `k`. Use `⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `Category.id_comp _`.
-/
private theorem qcqs_id (X : Scheme.{0}) : QcqsOver (𝟙 (sch.obj X)) := by
  intro k
  refine ⟨X, 𝟙 X, Iso.refl _, inferInstance, inferInstance, ?_⟩
  simp
  exact Category.id_comp _

/- English proof (translation)
Introduce `k`. Take `⟨Z, π, e, hπ, he⟩` from `GlobalTheory.T.exists_representable_cech_level_of_stable @IsProper Y X f inferInstance k`. Use `haveI := hπ`. Use `⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations. Simplify using `using he`.
-/
private theorem qcqs_cech {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] :
    QcqsOver (cechAug f ≫ 𝟙 (sch.obj X)) := by
  intro k
  obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsProper Y X f inferInstance k
  haveI := hπ
  refine ⟨Z, π ≫ f, e, inferInstance, inferInstance, ?_⟩
  simpa using he

/- English proof (translation)
Take `⟨hiso, hcomp, -, -⟩` from `GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F`. Take `⟨m, hpb, -⟩` from `GlobalTheory.T.etaleCechNerve_baseChange_isPullback Y X (pullback f s) T (pullback.fst f s) (pullback.snd f s) f s (IsPullback.of_hasPullback f s)`. Establish `hpb' : IsPullback m (cechAug (pullback.snd f s)) (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s)`. Rewrite using `[Category.comp_id]`. Conclude with `hpb`.

Set `g : pullback (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s) ⟶ pullback (𝟙 (sch.obj X)) (sch.map s)` to `(bcMap (cechAug f) (𝟙 (sch.obj X))).app (Over.mk s)`. Establish `hsnd : g ≫ pullback.snd (𝟙 (sch.obj X)) (sch.map s) = pullback.snd (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s)` using `by dsimp only [g, bcMap] erw [pullback.lift_snd]`. Conclude with `Category.comp_id _`. Establish `hQ : Eqv R (pullback.snd (𝟙 (sch.obj X)) (sch.map s)) F` using `hiso _ _ _ inferInstance`. Establish `hι : Eqv R hpb'.isoPullback.hom F` using `hiso _ _ _ inferInstance`.

Establish `key : (hpb'.isoPullback.hom ≫ g) ≫ pullback.snd (𝟙 (sch.obj X)) (sch.map s) = cechAug (pullback.snd f s)`. Rewrite using `[Category.assoc, hsnd, hpb'.isoPullback_hom_snd]`. Establish `h1 : Eqv R (hpb'.isoPullback.hom ≫ g) F`. Use `(hcomp _ _ _ _ _).2.2 hQ ?_` and prove the remaining obligations. Rewrite using `[key]`.

Conclude with `h`. Conclude with `((hcomp _ _ _ _ _).2.1 hι h1 : Eqv R g F)`.
-/
private theorem stalk_eqv (R : Type) [CommRing R] (F : Shv R) {Y X T : Scheme.{0}} (f : Y ⟶ X) (s : T ⟶ X)
    (h : Eqv R (cechAug (pullback.snd f s)) F) :
    Eqv R ((bcMap (cechAug f) (𝟙 (sch.obj X))).app (Over.mk s)) F := by
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F
  obtain ⟨m, hpb, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback Y X (pullback f s) T (pullback.fst f s) (pullback.snd f s) f s
    (IsPullback.of_hasPullback f s)
  have hpb' : IsPullback m (cechAug (pullback.snd f s)) (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s) := by
    rw [Category.comp_id]
    exact hpb
  let g : pullback (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s) ⟶ pullback (𝟙 (sch.obj X)) (sch.map s) :=
    (bcMap (cechAug f) (𝟙 (sch.obj X))).app (Over.mk s)
  have hsnd : g ≫ pullback.snd (𝟙 (sch.obj X)) (sch.map s)
      = pullback.snd (cechAug f ≫ 𝟙 (sch.obj X)) (sch.map s) := by
    dsimp only [g, bcMap]
    erw [pullback.lift_snd]
    exact Category.comp_id _
  have hQ : Eqv R (pullback.snd (𝟙 (sch.obj X)) (sch.map s)) F := hiso _ _ _ inferInstance
  have hι : Eqv R hpb'.isoPullback.hom F := hiso _ _ _ inferInstance
  have key : (hpb'.isoPullback.hom ≫ g) ≫ pullback.snd (𝟙 (sch.obj X)) (sch.map s)
      = cechAug (pullback.snd f s) := by
    rw [Category.assoc, hsnd, hpb'.isoPullback_hom_snd]
  have h1 : Eqv R (hpb'.isoPullback.hom ≫ g) F := by
    refine (hcomp _ _ _ _ _).2.2 hQ ?_
    rw [key]
    exact h
  exact ((hcomp _ _ _ _ _).2.1 hι h1 : Eqv R g F)

/- English proof (translation)
Introduce `hH q _ k _ hq Y X p _ f _ _ i`. Use `UpperTheory.Cb.equiv_of_stalkwise_base_change (ZMod q) (tw q i) X _ _ (cechAug f) (𝟙 (sch.obj X)) (UpperTheory.Cb.tateTwist_finitary q i) (qcqs_cech f) (qcqs_id X) ?_` and prove the remaining obligations. Introduce `O _ s hs`. Apply `stalk_eqv` to reduce the goal to its premises. Establish `hqO : IsUnit ((q : ℕ) : O)`.

Establish `φ` using `Spec.preimage (s ≫ p)`. Simplify using `using hq.map φ.hom`. Conclude with `UpperTheory.cech_descent_twist_of_proper_surjective_strictly_henselian hH q O hs.1 hqO (pullback.snd f s) i`.
-/
theorem UpperTheory.curve_etale_descent :
    LateralTheory.E.E4.LeafDesc := by
  intro hH q _ k _ hq Y X p _ f _ _ i
  refine UpperTheory.Cb.equiv_of_stalkwise_base_change (ZMod q) (tw q i) X _ _ (cechAug f) (𝟙 (sch.obj X)) (UpperTheory.Cb.tateTwist_finitary q i)
    (qcqs_cech f) (qcqs_id X) ?_
  intro O _ s hs
  apply stalk_eqv
  have hqO : IsUnit ((q : ℕ) : O) := by
    have φ := Spec.preimage (s ≫ p)
    simpa using hq.map φ.hom
  exact UpperTheory.cech_descent_twist_of_proper_surjective_strictly_henselian hH q O hs.1 hqO (pullback.snd f s) i
