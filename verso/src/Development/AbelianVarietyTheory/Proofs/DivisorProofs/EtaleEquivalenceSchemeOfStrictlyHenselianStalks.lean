import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSchBc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfStalkwiseBaseChangeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

attribute [-instance] CategoryTheory.Limits.hasPullbackHorizPaste

/- English proof (translation)
Introduce `_` and use `⟨X, r, Iso.refl _, inferInstance, inferInstance, by simp [sch]⟩`.
-/
theorem qcqsOver_sch {X S : Scheme.{0}} (r : X ⟶ S) [QuasiCompact r] [QuasiSeparated r] : QcqsOver (sch.map r) :=
  fun _ => ⟨X, r, Iso.refl _, inferInstance, inferInstance, by simp [sch]⟩

/- English proof (translation)
Establish `h` using `(IsPullback.of_hasPullback (f ≫ p) s).map sch`. Rewrite `h` using `[Functor.map_comp]`. Conclude with `h`.
-/
theorem isPullback_sch_comp {Y X S T : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (s : T ⟶ S) :
    IsPullback (sch.map (pullback.fst (f ≫ p) s)) (sch.map (pullback.snd (f ≫ p) s)) (sch.map f ≫ sch.map p) (sch.map s) := by
  have h := (IsPullback.of_hasPullback (f ≫ p) s).map sch
  rw [Functor.map_comp] at h
  exact h

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem bcMap_app_fst {E E' : Spc} {S : Scheme.{0}} (α : E ⟶ E') (p : E' ⟶ sch.obj S) (U : Over S) :
    (bcMap α p).app U ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E') = pullback.fst (α ≫ p) (sch.map U.hom) ≫ α :=
  pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `(pullback.lift_snd _ _ _).trans (Category.comp_id _)`.
-/
theorem bcMap_app_snd {E E' : Spc} {S : Scheme.{0}} (α : E ⟶ E') (p : E' ⟶ sch.obj S) (U : Over S) :
    (bcMap α p).app U ≫ (pullback.snd p (sch.map U.hom) : (bc p).obj U ⟶ _) = pullback.snd (α ≫ p) (sch.map U.hom) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/- English proof (translation)
Set `P1` to `isPullback_sch_comp f p s`. Set `P2` to `(IsPullback.of_hasPullback p s).map sch`. Apply `pullback.hom_ext` to reduce the goal to its premises. Establish `l : (P1.isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s)) ≫ pullback.fst (sch.map p) (sch.map s) = sch.map (pullback.fst (f ≫ p) s) ≫ sch.map f`. Use `(Category.assoc _ _ _).trans ?_` and prove the remaining obligations.

Use `erw [bcMap_app_fst]`. Rewrite using `[← Category.assoc]`. Conclude with `congrArg (· ≫ sch.map f) P1.isoPullback_hom_fst`. Establish `r : (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ P2.isoPullback.hom) ≫ pullback.fst (sch.map p) (sch.map s) = sch.map (pullback.fst (f ≫ p) s) ≫ sch.map f`. Rewrite using `[Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]`.

Conclude with `l.trans r.symm`. Establish `l : (P1.isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s)) ≫ pullback.snd (sch.map p) (sch.map s) = sch.map (pullback.snd (f ≫ p) s)`. Use `(Category.assoc _ _ _).trans ?_` and prove the remaining obligations. Use `erw [bcMap_app_snd]`. Conclude with `P1.isoPullback_hom_snd`.

Establish `r : (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ P2.isoPullback.hom) ≫ pullback.snd (sch.map p) (sch.map s) = sch.map (pullback.snd (f ≫ p) s)`. Rewrite using `[Category.assoc, IsPullback.isoPullback_hom_snd, ← Functor.map_comp]`. Conclude with `congrArg sch.map ((pullback.lift_snd _ _ _).trans (Category.comp_id _))`. Conclude with `l.trans r.symm`.
-/
theorem bcMap_sch_square {Y X S T : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (s : T ⟶ S) :
    (isPullback_sch_comp f p s).isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s) =
      sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫
        ((IsPullback.of_hasPullback p s).map sch).isoPullback.hom := by
  let P1 := isPullback_sch_comp f p s
  let P2 := (IsPullback.of_hasPullback p s).map sch
  apply pullback.hom_ext
  · have l : (P1.isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s)) ≫ pullback.fst (sch.map p) (sch.map s) =
        sch.map (pullback.fst (f ≫ p) s) ≫ sch.map f := by
      refine (Category.assoc _ _ _).trans ?_
      erw [bcMap_app_fst]
      rw [← Category.assoc]
      exact congrArg (· ≫ sch.map f) P1.isoPullback_hom_fst
    have r : (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ P2.isoPullback.hom) ≫
        pullback.fst (sch.map p) (sch.map s) = sch.map (pullback.fst (f ≫ p) s) ≫ sch.map f := by
      rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
    exact l.trans r.symm
  · have l : (P1.isoPullback.hom ≫ (bcMap (sch.map f) (sch.map p)).app (Over.mk s)) ≫ pullback.snd (sch.map p) (sch.map s) =
        sch.map (pullback.snd (f ≫ p) s) := by
      refine (Category.assoc _ _ _).trans ?_
      erw [bcMap_app_snd]
      exact P1.isoPullback_hom_snd
    have r : (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫ P2.isoPullback.hom) ≫
        pullback.snd (sch.map p) (sch.map s) = sch.map (pullback.snd (f ≫ p) s) := by
      rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Functor.map_comp]
      exact congrArg sch.map ((pullback.lift_snd _ _ _).trans (Category.comp_id _))
    exact l.trans r.symm

/- English proof (translation)
Introduce `R _ F hF Y X S f p _ _ _ _ hst`. Use `GlobalTheory.T.equiv_of_stalkwise_base_change R F S (sch.obj Y) (sch.obj X) (sch.map f) (sch.map p) hF ?_ (qcqsOver_sch p) ?_` and prove the remaining obligations. Rewrite using `[← Functor.map_comp]`. Conclude with `qcqsOver_sch (f ≫ p)`. Introduce `O _ s hs`.

Establish `hb` using `eqv_basic R F`. Establish `hsq` using `bcMap_sch_square f p s`. Establish `h1` using `hb.1 _ _ (isPullback_sch_comp f p s).isoPullback.hom inferInstance`. Establish `h2` using `(hb.2.1 _ _ _ _ _).1 (hst O s hs) (hb.1 _ _ ((IsPullback.of_hasPullback p s).map sch).isoPullback.hom inferInstance)`. Rewrite `h2` using `[← hsq]`.

Conclude with `(hb.2.1 _ _ _ _ _).2.1 h1 h2`.
-/
theorem eqv_sch_of_stalks : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (Y X S : Scheme.{0}) (f : Y ⟶ X) (p : X ⟶ S) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f], (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R (sch.map (pullback.map (f ≫ p) s p s f (𝟙 _) (𝟙 _) (by simp) (by simp))) F) → Eqv R (sch.map f) F := by
  intro R _ F hF Y X S f p _ _ _ _ hst
  refine GlobalTheory.T.equiv_of_stalkwise_base_change R F S (sch.obj Y) (sch.obj X) (sch.map f) (sch.map p) hF ?_ (qcqsOver_sch p) ?_
  · rw [← Functor.map_comp]; exact qcqsOver_sch (f ≫ p)
  · intro O _ s hs
    have hb := eqv_basic R F
    have hsq := bcMap_sch_square f p s
    have h1 := hb.1 _ _ (isPullback_sch_comp f p s).isoPullback.hom inferInstance
    have h2 := (hb.2.1 _ _ _ _ _).1 (hst O s hs) (hb.1 _ _ ((IsPullback.of_hasPullback p s).map sch).isoPullback.hom inferInstance)
    rw [← hsq] at h2
    exact (hb.2.1 _ _ _ _ _).2.1 h1 h2

end GlobalTheory.EtC
