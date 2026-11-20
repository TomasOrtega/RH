import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ColumnStabiliser
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.TrivialColumnStabiliser

noncomputable section

namespace GlobalTheory.Proof.StabilizerGroupMap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice
open scoped TensorProduct

/- English proof (translation)
Use `haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by`. Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 D.host.F)`. Establish `hne : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)`. Conclude with `(evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial`. Use `haveI : Nontrivial (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) := inferInstance`.

Introduce `a b hab`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply `(inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).injective` to reduce the goal to its premises. Establish `h2` using `congrArg (fun g : GL (Fin D.R.k) _ => g.val i j) hab`. Simplify `h2` using `[bc]`.
-/
theorem bc_inclE_injective (D : D7) :
    Function.Injective
      (bc (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
        GL (Fin D.R.k) D.host.E →*
          GL (Fin D.R.k) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  haveI : Nontrivial (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
    exact (evalV D.host.F ⟨P, hP.isPrime, hne⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) := inferInstance
  intro a b hab
  refine Units.ext (Matrix.ext fun i j => ?_)
  apply (inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)).injective
  have h2 := congrArg (fun g : GL (Fin D.R.k) _ => g.val i j) hab
  simpa [bc] using h2

/- English proof (translation)
The claim follows from `(GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.map_colStab D Lv u y).symm`.
-/
theorem stabGroup_eq_map (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y =
      (GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y).map
        (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) :=
  (GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.map_colStab D Lv u y).symm

def stabEquiv (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y ≃* GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y :=
  ((GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y).equivMapOfInjective _ (bc_inclE_injective D)).trans
    (MulEquiv.subgroupCongr (stabGroup_eq_map D Lv u y).symm)

/- English proof (translation)
Rewrite using `[stabGroup_eq_map, Subgroup.map_eq_bot_iff_of_injective _ (bc_inclE_injective D)]`.
-/
theorem stabGroup_eq_bot_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word)
    (y : GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y = ⊥ ↔ GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.colStab D Lv u y = ⊥ := by
  rw [stabGroup_eq_map, Subgroup.map_eq_bot_iff_of_injective _ (bc_inclE_injective D)]

/- English proof (translation)
Use `imp_congr_right fun _ => imp_congr_right fun _ => ?_` and prove the remaining obligations. Conclude with `⟨fun h y => (stabGroup_eq_bot_iff D Lv u y).1 (h y.1 y.2), fun h y hy => (stabGroup_eq_bot_iff D Lv u ⟨y, hy⟩).2 (h ⟨y, hy⟩)⟩`.
-/
theorem at_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    (GBig D → (∀ i : Fin 2, SplitsF D (D.host.g i)) →
      ∀ y ∈ GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.GAf D, GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.stabGroup D Lv u y = ⊥) ↔
      GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.ColStabTrivialAt D Lv u := by
  refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
  exact ⟨fun h y => (stabGroup_eq_bot_iff D Lv u y).1 (h y.1 y.2),
    fun h y hy => (stabGroup_eq_bot_iff D Lv u ⟨y, hy⟩).2 (h ⟨y, hy⟩)⟩

/- English proof (translation)
The claim follows from `forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => at_iff D Lv u`.
-/
theorem columnStabilisersTrivial_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.TrivialColumnStabiliser.ColumnStabilisersTrivial ↔ GlobalTheory.IndefiniteRowSideFullHecke.ColumnStabiliser.ColStabTrivial :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => at_iff D Lv u

end GlobalTheory.Proof.StabilizerGroupMap

end
