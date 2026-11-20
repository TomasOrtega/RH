import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/- English proof (translation)
The claim follows from `ModuleCat.isZero_iff_subsingleton.mp (Sheaf.isTerminalOfBotCover G U (Scheme.bot_mem_propQCTopology (P := @WeaklyEtale) U)).isZero`.
-/
theorem subsingleton_obj_of_isEmpty (G : Shv R) (U : Scheme.{0}) [IsEmpty U] :
    Subsingleton (G.val.obj (op U)) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (Sheaf.isTerminalOfBotCover G U (Scheme.bot_mem_propQCTopology (P := @WeaklyEtale) U)).isZero

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Apply `((sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv (uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R)) ((freeOn R).obj X)).injective` to reduce the goal to its premises. Apply `NatTrans.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `U`. Apply `ModuleCat.hom_ext` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Break down `isEmpty_or_nonempty U.unop with hU | hU` into its components or cases. Conclude with `(subsingleton_obj_of_isEmpty R ((freeOn R).obj X) U.unop).elim _ _`. Establish `: IsEmpty (ULift.{1} (U.unop ⟶ X))` using `⟨fun f => IsEmpty.false (f.down.base (Classical.arbitrary U.unop))⟩`.

Establish `hs : Subsingleton (ULift.{1} (U.unop ⟶ X) →₀ ULift.{1} R)` using `inferInstance`. Establish `hx : x = 0` using `hs.elim x 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules.
-/
theorem isZero_freeOn_of_isEmpty (X : Scheme.{0}) [IsEmpty X] : IsZero ((freeOn R).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    (uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R)) ((freeOn R).obj X)).injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · exact (subsingleton_obj_of_isEmpty R ((freeOn R).obj X) U.unop).elim _ _
  · have : IsEmpty (ULift.{1} (U.unop ⟶ X)) :=
      ⟨fun f => IsEmpty.false (f.down.base (Classical.arbitrary U.unop))⟩
    have hs : Subsingleton (ULift.{1} (U.unop ⟶ X) →₀ ULift.{1} R) := inferInstance
    have hx : x = 0 := hs.elim x 0
    subst hx
    simp

end GlobalTheory.Et

end
