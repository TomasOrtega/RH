import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

instance : PreservesLimitsOfShape WalkingCospan sch := by unfold sch; infer_instance

/- English proof (translation)
The claim follows from `(IsPullback.of_hasPullback U.hom r).flip.map sch`.
-/
theorem isPullback_sch_bc {S W : Scheme.{0}} (r : W ⟶ S) (U : Over S) :
    IsPullback (sch.map (pullback.snd U.hom r)) (sch.map (pullback.fst U.hom r)) (sch.map r) (sch.map U.hom) :=
  (IsPullback.of_hasPullback U.hom r).flip.map sch

/- English proof (translation)
Introduce `S W r`. Use `⟨NatIso.ofComponents (fun U => (isPullback_sch_bc r U).isoPullback) ?_, fun U => ?_⟩` and prove the remaining obligations. Introduce `U V g`. Establish `fV` using `(isPullback_sch_bc r V).isoPullback_hom_fst`. Establish `sV` using `(isPullback_sch_bc r V).isoPullback_hom_snd`.

Establish `fU` using `(isPullback_sch_bc r U).isoPullback_hom_fst`. Establish `sU` using `(isPullback_sch_bc r U).isoPullback_hom_snd`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [bc, pullback.map, Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc, pullback.lift_fst, Category.comp_id] erw [fV, fU, ← Functor.map_comp, pullback.lift_snd]`. Both sides reduce to the same expression.

Simplify using `only [bc, pullback.map, Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc, pullback.lift_snd] erw [sV, reassoc_of% sU, ← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]`. Both sides reduce to the same expression. Conclude with `⟨IsPullback.isoPullback_hom_fst _, IsPullback.isoPullback_hom_snd _⟩`.
-/
theorem bc_sch_iso : ∀ (S W : Scheme.{0}) (r : W ⟶ S), ∃ e : (Over.pullback r ⋙ Over.forget W ⋙ sch) ≅ bc (sch.map r), ∀ U : Over S, e.hom.app U ≫ pullback.fst (sch.map r) (sch.map U.hom) = sch.map (pullback.snd U.hom r) ∧ e.hom.app U ≫ pullback.snd (sch.map r) (sch.map U.hom) = sch.map (pullback.fst U.hom r) := by
  intro S W r
  refine ⟨NatIso.ofComponents (fun U => (isPullback_sch_bc r U).isoPullback) ?_, fun U => ?_⟩
  · intro U V g
    have fV := (isPullback_sch_bc r V).isoPullback_hom_fst
    have sV := (isPullback_sch_bc r V).isoPullback_hom_snd
    have fU := (isPullback_sch_bc r U).isoPullback_hom_fst
    have sU := (isPullback_sch_bc r U).isoPullback_hom_snd
    apply pullback.hom_ext
    · simp only [bc, pullback.map, Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc,
        pullback.lift_fst, Category.comp_id]
      erw [fV, fU, ← Functor.map_comp, pullback.lift_snd]
      rfl
    · simp only [bc, pullback.map, Functor.comp_map, Over.forget_map, Over.pullback_map_left, Category.assoc,
        pullback.lift_snd]
      erw [sV, reassoc_of% sU, ← Functor.map_comp, ← Functor.map_comp, pullback.lift_fst]
      rfl
  · exact ⟨IsPullback.isoPullback_hom_fst _, IsPullback.isoPullback_hom_snd _⟩

end GlobalTheory.EtC
