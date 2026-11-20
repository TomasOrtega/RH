import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto

open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMirFun

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_mirProj (n : ℕ) : Continuous (mirabolicProjection k n) := by
  have hval : Continuous fun g : Mir k n =>
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val.comp continuous_subtype_val
  have hblock : Continuous fun g : Mir k n =>
      ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply (Fin.castSucc j)).comp ((continuous_apply (Fin.castSucc i)).comp hval)
  have hinv : Continuous fun g : Mir k n => g⁻¹ := by
    exact continuous_inv
  refine Units.continuous_iff.2 ⟨hblock, ?_⟩
  have : (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      fun g => ((mirabolicProjection k n g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    funext g
    rw [map_inv]
  show Continuous (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
  rw [this]
  exact hblock.comp hinv

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem smPsiPlus : SmPsiPlus k := by
  intro n W _ _ σ hσ w
  exact (hσ w).preimage (continuous_mirProj k n)

end GlobalTheory.CompanionTheory.BZMirFun
