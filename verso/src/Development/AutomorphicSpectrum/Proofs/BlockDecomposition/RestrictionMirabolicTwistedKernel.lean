import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.BZMirDer

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Both sides reduce to the same expression.
-/
theorem twKer_resM_derUnipM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (m n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (m + 1)) k) V),
    twKer (resM k π).ρ (derUnipM k m n) (derCharM k ψ m n) = twKer π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n) := by
  intro k _ _ _ _ ψ m n V _ _ π
  unfold twKer
  congr 1
  ext w
  constructor
  · rintro ⟨u, v, rfl⟩
    exact ⟨Subgroup.subgroupOfEquivOfLe (derUnip_le_Mir k m n) u, v, rfl⟩
  · rintro ⟨u, v, rfl⟩
    refine ⟨(Subgroup.subgroupOfEquivOfLe (derUnip_le_Mir k m n)).symm u, v, ?_⟩
    simp [derCharM, resM]
    rfl

end GlobalTheory.CompanionTheory.BZMirDer
