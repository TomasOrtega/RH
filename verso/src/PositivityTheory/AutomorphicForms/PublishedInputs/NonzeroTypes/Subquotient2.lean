import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.Subquotient₂

variable {F H V : Type} [Field F] [Group H] [AddCommGroup V] [Module F V]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem wellFoundedGT_of_finiteLength {ρ : Representation F H V} (h : HasFiniteLength ρ) :
    WellFoundedGT (Subrepresentation ρ) := by
  have hN := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).1
  have := isNoetherian_iff'.mp hN
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).strictMono.wellFoundedGT

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem wellFoundedLT_of_finiteLength {ρ : Representation F H V} (h : HasFiniteLength ρ) :
    WellFoundedLT (Subrepresentation ρ) := by
  have hA := (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2
  have : WellFoundedLT (Submodule (MonoidAlgebra F H) ρ.asModule) := hA
  exact (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).strictMono.wellFoundedLT

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem exists_covBy {ρ : Representation F H V} (h : HasFiniteLength ρ) {y : V} (hy : y ≠ 0) :
    ∃ S T : Subrepresentation ρ, T ⋖ S ∧ y ∈ S.toSubmodule ∧ y ∉ T.toSubmodule := by
  have := wellFoundedGT_of_finiteLength h
  have := wellFoundedLT_of_finiteLength h
  obtain ⟨T, hT, hmax⟩ := wellFounded_gt.has_min {T : Subrepresentation ρ | y ∉ T.toSubmodule}
    ⟨⊥, fun h' => hy ((Submodule.mem_bot F).1 h')⟩
  have hTtop : T ≠ ⊤ := by
    rintro rfl
    exact hT trivial
  obtain ⟨S, hS, hmin⟩ := wellFounded_lt.has_min {S : Subrepresentation ρ | T < S}
    ⟨⊤, lt_top_iff_ne_top.2 hTtop⟩
  refine ⟨S, T, ⟨hS, fun U hTU hUS => hmin U hTU hUS⟩, ?_, hT⟩
  by_contra hyS
  exact hmax S hyS hS

end UpperTheory.TNZ.Grp.Subquotient₂

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem step_subq {n : ℕ} (G : Grp k n) : G.SubquotientProp := by
  intro W _ _ ρ hs hfl hη
  obtain ⟨y, hy, hyη⟩ := hη
  obtain ⟨S, T, hcov, hyS, hyT⟩ := Subquotient₂.exists_covBy hfl hy
  let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hsq : IsSubquotient (subQuot S T) ρ := ⟨S, p, Submodule.mkQ_surjective _⟩
  refine ⟨_, inferInstance, inferInstance, subQuot S T, hsq.isSmooth hs, isIrreducible_subQuot hcov, hsq,
    Submodule.Quotient.mk ⟨y, hyS⟩, ?_, fun m hm => ?_⟩
  · rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hyT
  · show Submodule.Quotient.mk (S.toRepresentation m ⟨y, hyS⟩) = _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hyη m hm)

end UpperTheory.TNZ.Grp
