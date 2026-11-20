import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem finM_eq_one_iff_mem_GinfC :
    ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V), finM V hn g = 1 ↔ g ∈ GinfC V := by
  intro D V n hn g
  subst hn
  have e0 : finM V rfl g = (Formalism.L2.Theta.mt V g).map (toEAf D) := by simp [finM]
  have e : (Formalism.L2.Theta.mt V g).map (toEAf D) = (finHom V g).val.map
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := rfl
  rw [e0, e]
  constructor
  · intro h
    show finHom V g = 1
    apply Units.ext
    have hinj := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
    apply Matrix.map_injective hinj
    show (finHom V g).val.map _ = (1 : Matrix _ _ _).map _
    rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
  · intro hk
    have h : finHom V g = 1 := hk
    have h2 : (finHom V g).val = 1 := by rw [h]; rfl
    rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.AdForm
