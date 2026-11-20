import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ScalW

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Take a linear combination of the given relations to obtain the conclusion. Rewrite the hypotheses and the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem znear_term : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) - hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := by
  intro D X u
  obtain ⟨c, hc, hm⟩ := X.xu_z u
  obtain ⟨-, hz0, -⟩ := X.vectorsInLattice
  set z' := X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u with hz'
  have hm' : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) ∈ mL X.B.I X.B.g := hm
  refine ⟨c * c, Nat.Coprime.mul hc hc, ?_⟩
  intro y hy
  have hcz : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' ∈ X.B.I.Lf := by
    have e : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' =
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) := by
      rw [smul_sub]; abel
    rw [e]
    exact add_mem (GlobalTheory.St.G.FrameClose.nat_smul_mem c hz0) (GlobalTheory.St.G.FrameClose.mL_le _ hm')
  obtain ⟨t1, ht1, e1⟩ := GlobalTheory.St.G.FrameClose.zmod_of_mL hm' hy
  rw [GlobalTheory.St.G.FrameClose.hA_nat_left, GlobalTheory.St.G.FrameClose.hA_sub_left] at e1
  have hs : hA X.B.I X.z0 y ∈ IntAf X.B.I.F X.B.I.E := GlobalTheory.St.G.FrameClose.hA_int hz0 hy
  have hs' : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y ∈ IntAf X.B.I.F X.B.I.E :=
    mul_mem (natCast_mem _ c) hs
  have e : ((c * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (hA X.B.I z' y • z' - hA X.B.I X.z0 y • X.z0) =
      t1 • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z')) +
      ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y) •
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0)) := by
    simp only [smul_smul, smul_sub, Nat.cast_mul]
    have e2 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I z' y =
        (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t1 + (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y := by
      linear_combination e1
    have e3 : (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I z' y =
        t1 * ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) +
        (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      linear_combination (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * e2
    rw [e3, add_smul, show (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 y * (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) by ring]
    abel
  rw [e]
  refine add_mem ?_ ?_
  · exact (mL X.B.I X.B.g).smul_mem (⟨_, ht1⟩ : IntAf X.B.I.F X.B.I.E) (Submodule.subset_span ⟨_, hcz, rfl⟩)
  · exact (mL X.B.I X.B.g).smul_mem (⟨_, hs'⟩ : IntAf X.B.I.F X.B.I.E) hm'

end GlobalTheory.ScalW
