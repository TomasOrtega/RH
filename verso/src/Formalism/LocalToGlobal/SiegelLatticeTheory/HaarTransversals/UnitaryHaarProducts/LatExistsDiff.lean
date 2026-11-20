import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LatExistsDefs

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.SG.Pf.LatEx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem splitDiff_holds : SplitDiff := by
  intro F E _ _ _ _ _ p P hp hPm hpP hpP2 h
  haveI : P.IsPrime := hPm.isPrime
  have hDE : differentIdeal ℤ (𝓞 E) ≤ P := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)]
    exact le_trans Ideal.mul_le_right h
  have hdvd : P ∣ differentIdeal ℤ (𝓞 E) := Ideal.dvd_iff_le.mpr hDE
  rw [dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain] at hdvd
  apply hdvd
  have hpu : ((p : ℤ)) ∈ P.under ℤ := by
    show (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) P
    rw [Ideal.mem_comap]
    simpa using hpP
  have hne : P.under ℤ ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpu
    exact hp.ne_zero (by exact_mod_cast hpu)
  haveI : P.LiesOver (P.under ℤ) := ⟨rfl⟩
  rw [← Ideal.ramificationIdx_eq_ramificationIdx' (P.under ℤ) P hne]
  apply Ideal.ramificationIdx'_spec
  · rw [pow_one]
    exact Ideal.map_comap_le
  · intro hle
    have h2 := hle (Ideal.mem_map_of_mem (algebraMap ℤ (𝓞 E)) hpu)
    apply hpP2
    simpa using h2

end Formalism.L2.SG.Pf.LatEx
