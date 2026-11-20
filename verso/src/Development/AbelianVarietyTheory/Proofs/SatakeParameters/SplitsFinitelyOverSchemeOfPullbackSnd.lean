import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

/- English proof (translation)
Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem splits_of_splits_pullback_snd {Z X S V : Scheme.{0}} (f : Z ⟶ X) (x : S ⟶ X) (v : V ⟶ S) :
    GlobalTheory.EtC.Tr.Splits (pullback.snd f x) v → GlobalTheory.EtC.Tr.Splits f (v ≫ x) := by
  rintro ⟨m, s, hs, hiso⟩
  refine ⟨m, fun j => s j ≫ pullback.fst f x, fun j => ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs j]
  · have heq : (Sigma.desc (fun j => pullback.lift (s j ≫ pullback.fst f x) (𝟙 V)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, hs j, Category.id_comp])) :
          ∐ (fun _ : Fin m => V) ⟶ pullback f (v ≫ x)) =
        (Sigma.desc (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp])) :
          ∐ (fun _ : Fin m => V) ⟶ pullback (pullback.snd f x) v) ≫
          (pullbackLeftPullbackSndIso f x v).hom := by
      apply Sigma.hom_ext
      intro j
      rw [Sigma.ι_desc, Sigma.ι_desc_assoc]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullbackLeftPullbackSndIso_hom_fst, pullback.lift_fst_assoc]
      · rw [pullback.lift_snd, Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullback.lift_snd]
    rw [heq]
    infer_instance

end GlobalTheory.EtC.Tr
