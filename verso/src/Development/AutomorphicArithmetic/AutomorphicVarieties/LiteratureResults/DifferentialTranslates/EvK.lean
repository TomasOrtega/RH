import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `E _ _ _ a Ξ k m g`. Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul φ v`. Establish `h : ev (smK Ξ k (φ ⊗ₜ[ℂ] v)) g = φ.1 (g * infGL E a (Unitary.toUnits k)) • (Ξ.mat (Unitary.toUnits k) *ᵥ v)` using `rfl`.

Rewrite using `[h, ev_tmul, Matrix.mulVec_smul]`. Consider the case `add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, Matrix.mulVec_add]`.
-/
theorem evK : EvK := by
  intro E _ _ _ a Ξ k m g
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    have h : ev (smK Ξ k (φ ⊗ₜ[ℂ] v)) g =
        φ.1 (g * infGL E a (Unitary.toUnits k)) • (Ξ.mat (Unitary.toUnits k) *ᵥ v) := rfl
    rw [h, ev_tmul, Matrix.mulVec_smul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, Matrix.mulVec_add]

end UpperTheory.V.Lit.Dr
