import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDefiniteUnitaryInfinitePointOfUnitaryFamilStatement
import Formalism.LocalToGlobal.Columns.CoefColLemmas

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Wt.isIrreducible_rep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n),
    W.rep.IsIrreducible := by
  intro E _ _ _ n W
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨Formalism.L2.Col.VV_nontrivial ℂ W, fun U hU => ?_⟩
  refine GlobalTheory.CoefIrred.vv_irreducible_unitary (InfinitePlace E) n W U fun g hg x hx => ?_
  obtain ⟨y, hy, hyg⟩ := GlobalTheory.T.exists_definiteUnitaryInfinitePoint_of_unitary_family E n g hg
  have h := hU ⟨y, hy⟩ x hx
  rw [← hyg]
  exact h

end GlobalTheory.DefU
