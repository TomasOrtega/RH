import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem EtC.isIso_chains_map_of_isIso_free (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E')
    (h : ∀ n, IsIso ((free R).map (f.app n))) : IsIso ((chains R).map f) := by
  have hw : IsIso (((SimplicialObject.whiskering _ _).obj (free R)).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact h n
  have : IsIso ((chainsN R).map f) := by
    unfold chainsN
    rw [Functor.comp_map]
    infer_instance
  unfold chains
  rw [Functor.comp_map]
  infer_instance

end GlobalTheory
