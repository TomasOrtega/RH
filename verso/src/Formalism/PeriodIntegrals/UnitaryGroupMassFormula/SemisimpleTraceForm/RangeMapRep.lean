import Mathlib
import Formalism.PeriodIntegrals.SSAscent
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemisimpleTraceForm.TraceNilStep

namespace PI.SSAscent.UnitaryGroupMassFormula

open PI.SSAscent

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Supply the required witnesses or components.
-/
theorem range_mapRep {Γ : Type} [Group Γ] {K L : Type} [Field K] [Field L] [Algebra K L] {a : ℕ}
    (ρ : Γ →* GL (Fin a) K) :
    (Set.range fun g => ((mapRep (algebraMap K L) ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) =
      (algebraMap K L).mapMatrix '' Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) K) := by
  ext M
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(ρ g : Matrix (Fin a) (Fin a) K), ⟨g, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ssAscent_of (hD : DownStep) (hA : AscendStep) (hU : UpStep) : PI.SSAscent := by
  intro K L _ _ _ _ Γ _ a ρ hρ
  apply hU L Γ a
  have h1 : TrNondeg (imAlg ρ) := hD K Γ a ρ hρ
  have h2 := hA K L a (Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) K)) h1
  have h3 : imAlg (mapRep (algebraMap K L) ρ) =
      Algebra.adjoin L ((algebraMap K L).mapMatrix '' Set.range fun g => (ρ g : Matrix (Fin a) (Fin a) K)) :=
    congrArg (Algebra.adjoin L) (range_mapRep (L := L) ρ)
  rw [h3]
  exact h2

end PI.SSAscent.UnitaryGroupMassFormula
