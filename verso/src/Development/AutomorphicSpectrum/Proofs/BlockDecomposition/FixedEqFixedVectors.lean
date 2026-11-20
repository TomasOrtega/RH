import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Whit

namespace GlobalTheory.CompanionTheory.AdmDict

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) :
    GlobalTheory.PRep.fixed ρ K = GroundTheory.Automorphic.fixedVectors ρ K := by
  ext v
  constructor
  · intro hv h hh
    simpa using hv ⟨h, hh⟩
  · intro hv h
    simpa using hv h h.2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isAdmissible_iff : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ := by
  intro G V _ _ _ _ _ ρ
  have hs : GlobalTheory.PRep.IsSmooth ρ ↔ GroundTheory.Automorphic.IsSmooth ρ := Iff.rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hs.1 h1, fun K hc ho => ?_⟩
    have := h2 K ho hc
    rwa [fixed_eq_fixedVectors] at this
  · rintro ⟨h1, h2⟩
    refine ⟨hs.2 h1, fun K ho hc => ?_⟩
    rw [fixed_eq_fixedVectors]
    exact h2 K hc ho

end GlobalTheory.CompanionTheory.AdmDict
