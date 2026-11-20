import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitTorsion

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem principal_unit_idele_torsion : ∀ (E : Type) [Field E] [NumberField E] (t : Eˣ), Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E →
    (∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1) → ∃ n : ℕ, 0 < n ∧ t ^ n = 1 := by
  intro E _ _ t ht hnorm
  have hv : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (t : E) ≤ 1 := by
    intro v
    have h1 := ht v
    have h2 : ((Neutral.B1.diagUnits E t : AdeleRing (𝓞 E) E)).2 v = ((t : E) : v.adicCompletion E) := rfl
    rw [h2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1.le
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (t : E) hv
  have hint : IsIntegral ℤ (t : E) := by
    rw [← hy]; exact y.isIntegral_coe
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hint hnorm
  exact ⟨n, hn, Units.ext (by simpa using hpow)⟩

end GlobalTheory.UnitTorsion
