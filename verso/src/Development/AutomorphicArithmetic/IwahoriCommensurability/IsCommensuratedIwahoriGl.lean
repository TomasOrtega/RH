import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import GroundTheory.AutomorphicForms.AffineBruhat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IwahoriSubgroupDefinitionsAgree
open Formalism.UG GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal Matrix

/- English proof (translation)
Introduce `k _ _ _ _ n g`. Establish `hO : IsOpen (iwahori k n : Set (GL (Fin n) k))` using `isOpen_iwahori k n`. Establish `hC : IsCompact (iwahori k n : Set (GL (Fin n) k))` using `isCompact_iwahori k n`. Establish `hset : (((iwahori k n).map (MulAut.conj g).toMonoidHom : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) = (fun x => g⁻¹ * x * g) ⁻¹' (iwahori k n : Set (GL (Fin n) k))`. Use extensionality with `x`.

Simplify using `only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Simplify `hy` using `[mul_assoc]`. Introduce `hx`.

Conclude with `⟨_, hx, by simp [mul_assoc]⟩`. Establish `hOc : IsOpen (((iwahori k n).map (MulAut.conj g).toMonoidHom : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k))`. Rewrite using `[hset]`. Conclude with `hO.preimage (by fun_prop)`. Use `haveI : CompactSpace (iwahori k n) := isCompact_iff_compactSpace.mp hC`.

Establish `hU : IsOpen ((((iwahori k n).map (MulAut.conj g).toMonoidHom).subgroupOf (iwahori k n) : Subgroup (iwahori k n)) : Set (iwahori k n))` using `hOc.preimage continuous_subtype_val`. Use `haveI := Subgroup.quotient_finite_of_isOpen _ hU`. Conclude with `Subgroup.index_ne_zero_of_finite`.
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
