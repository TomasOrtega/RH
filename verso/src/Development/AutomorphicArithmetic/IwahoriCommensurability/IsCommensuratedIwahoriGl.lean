import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import GroundTheory.AutomorphicForms.AffineBruhat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriSubgroupDefinitionsAgree
open Formalism.UG GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.isCommensurated_iwahori_gl :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), IsCommensurated (iwahori k n) := by
  intro k _ _ _ _ n g
  have hO : IsOpen (iwahori k n : Set (GL (Fin n) k)) := isOpen_iwahori k n
  have hC : IsCompact (iwahori k n : Set (GL (Fin n) k)) := isCompact_iwahori k n
  have hset : (((iwahori k n).map (MulAut.conj g).toMonoidHom : Subgroup (GL (Fin n) k)) :
      Set (GL (Fin n) k)) = (fun x => g⁻¹ * x * g) ⁻¹' (iwahori k n : Set (GL (Fin n) k)) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  have hOc : IsOpen (((iwahori k n).map (MulAut.conj g).toMonoidHom : Subgroup (GL (Fin n) k)) :
      Set (GL (Fin n) k)) := by
    rw [hset]
    exact hO.preimage (by fun_prop)
  haveI : CompactSpace (iwahori k n) := isCompact_iff_compactSpace.mp hC
  have hU : IsOpen ((((iwahori k n).map (MulAut.conj g).toMonoidHom).subgroupOf (iwahori k n) :
      Subgroup (iwahori k n)) : Set (iwahori k n)) :=
    hOc.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hU
  exact Subgroup.index_ne_zero_of_finite
