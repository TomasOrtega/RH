import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullbackStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Establish `: PreservesLimit (cospan f g) sch`. Unfold `sch`. Use `infer_instance`. Conclude with `h.map sch`.
-/
theorem sch_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPullback (sch.map fst) (sch.map snd) (sch.map f) (sch.map g) := by
  have : PreservesLimit (cospan f g) sch := by
    unfold sch; infer_instance
  exact h.map sch

/- English proof (translation)
Introduce `S W V r f U`. Take `⟨m, hm, -⟩` from `GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ (pullback.fst f (pullback.fst r U.hom)) (pullback.snd f (pullback.fst r U.hom)) f (pullback.fst r U.hom) (IsPullback.of_hasPullback _ _)`. Establish `hQ` using `sch_isPullback (IsPullback.of_hasPullback r U.hom)`. Establish `hP` using `hm.paste_vert hQ`. Use `⟨hP.isoPullback, hQ.isoPullback, ?_⟩` and prove the remaining obligations.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [bc, bcMap, Category.assoc, pullback.lift_fst, pullback.map]`. Rewrite using `[IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_fst]`. Conclude with `hm.w`. Simplify using `only [bc, bcMap, Category.assoc, pullback.lift_snd, pullback.map, Category.comp_id]`.

Rewrite using `[IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]`.
-/
theorem bc_cechAug_iso : ∀ (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W) (U : Over S),
    ∃ (e₁ : cech (pullback.snd f (pullback.fst r U.hom)) ≅ (bc (cechAug f ≫ sch.map r)).obj U)
      (e₂ : sch.obj (pullback r U.hom) ≅ (bc (sch.map r)).obj U),
      e₁.hom ≫ (bcMap (cechAug f) (sch.map r)).app U = cechAug _ ≫ e₂.hom := by
  intro S W V r f U
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ (pullback.fst f (pullback.fst r U.hom))
    (pullback.snd f (pullback.fst r U.hom)) f (pullback.fst r U.hom) (IsPullback.of_hasPullback _ _)
  have hQ := sch_isPullback (IsPullback.of_hasPullback r U.hom)
  have hP := hm.paste_vert hQ
  refine ⟨hP.isoPullback, hQ.isoPullback, ?_⟩
  apply pullback.hom_ext
  · simp only [bc, bcMap, Category.assoc, pullback.lift_fst, pullback.map]
    rw [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_fst]
    exact hm.w
  · simp only [bc, bcMap, Category.assoc, pullback.lift_snd, pullback.map, Category.comp_id]
    rw [IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]

end GlobalTheory.EtC
