import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open scoped TensorProduct

namespace GlobalTheory

open PDiv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities.
-/
theorem omega_eq_zero_of_p_smul_eq_zero :
    ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R),
      (∀ n, Function.Injective (GlobalTheory.PDiv.cotMap (G.mulP n))) →
        ∀ w : G.omega, (p : R) • w = 0 → w = 0 := by
  intro p R _ G hinj w hw
  refine Subtype.ext (funext fun n => ?_)
  have hp : (p : R) • w.1 (n + 1) = 0 := congrArg (fun v : G.omega => v.1 (n + 1)) hw
  apply hinj n
  change cotMap (G.mulP n) (w.1 n) = cotMap (G.mulP n) 0
  rw [map_zero, ← w.2 n, ← LinearMap.comp_apply, ← cotMap_comp, G.mulP_comp_res,
    cotMap_mulBy, hp]

end GlobalTheory
