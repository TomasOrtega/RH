import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem spec_pi_cofan_isColimit : ∀ (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B] (e : B ≃+* (∀ i, T i)), Nonempty (IsColimit (Cofan.mk (Spec (CommRingCat.of B)) (fun i => Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))))) := by
  intro ι _ T _ B _ e
  let R : ι → CommRingCat := fun i => CommRingCat.of (T i)
  let eB : CommRingCat.of B ≅ CommRingCat.of (∀ i, T i) := e.toCommRingCatIso
  let φ : (∐ fun i => Spec (R i)) ≅ Spec (CommRingCat.of B) :=
    asIso (sigmaSpec R) ≪≫ Scheme.Spec.mapIso eB.op
  refine ⟨IsColimit.ofIsoColimit (coproductIsCoproduct _) (Cofan.ext φ ?_)⟩
  intro i
  simp only [φ, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.op_hom, Cofan.inj, Cofan.mk_ι_app]
  erw [ι_sigmaSpec_assoc]
  simp only [Scheme.Spec_map, Quiver.Hom.unop_op, ← Spec.map_comp]
  rfl

end GlobalTheory.EtC
