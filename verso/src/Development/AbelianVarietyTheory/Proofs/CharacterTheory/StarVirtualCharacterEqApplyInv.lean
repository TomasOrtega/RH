import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.CuspGL

open Polynomial in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Treat this case separately.

Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.CuspGL.star_virt_eq_inv : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ),
    χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G → ∀ g, star (χ g) = χ g⁻¹ := by
  intro G _ _ χ hχ
  have := Fintype.ofFinite G
  unfold _root_.GlobalTheory.BI.Virt at hχ
  induction hχ using AddSubgroup.closure_induction with
  | mem ψ hψ =>
    obtain ⟨n, ρ, h⟩ := hψ
    intro g
    have key := _root_.GlobalTheory.BadShare.ZCalc.character_inv (FDRep.of ρ) g
    simp only [h, Algebra.algebraMap_self, RingHom.id_apply]
    exact key.symm
  | zero => intro g; simp
  | add ψ φ _ _ h₁ h₂ => intro g; simp [h₁ g, h₂ g]
  | neg ψ _ h₁ => intro g; simp [h₁ g]

end GlobalTheory.CuspGL
