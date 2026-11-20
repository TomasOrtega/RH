import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.EtaPassage

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
theorem main : ∀ D : D7, KillingConditions.CommutingEndomorphismCondition D → TwistedPlaces.adm1 D := by
  intro D h i hi hl
  obtain ⟨α, hc, h1, h0⟩ := h i hi hl
  have hA : ((D.what₂.restRowsFiniteGroupCard : ℕ) : ℤ) ≠ 0 := by exact_mod_cast D.what₂.restRowsFiniteGroupCard_pos.ne'
  have hP := Formalism.MainNotions.TruncatedSeriesCountingIdentities.second_statement D i (D.nd.Zgood i) (Formalism.L2.zgoodSub D i) α _ hA hc h1 h0
  rw [← Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.etaLoc_eq] at hP
  simp only [padicValInt.of_nat] at hP
  have hR := (Rat.cast_le (K := ℝ)).2 hP
  push_cast at hR
  exact hR

end GlobalTheory.EtaPassage
