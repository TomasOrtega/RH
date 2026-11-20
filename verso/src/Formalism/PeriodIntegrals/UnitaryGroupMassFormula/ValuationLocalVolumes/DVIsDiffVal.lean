import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiffGenLoc

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dV_isDiffVal : IsDiffVal v (dV v) := by
  have h : ∃ d, IsDiffVal v d := diffExists v
  unfold dV
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Proceed by induction.

Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem val_pow_le (k : ℕ) (x : 𝓞 F) (hx : x ∈ differentIdeal ℤ (𝓞 F) ^ k) :
    Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v (dV v) ^ k := by
  have hint : ∀ y : 𝓞 F, Valued.v (algebraMap F (Fv F v) (y : F)) ≤ 1 := by
    intro y
    have e := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v y
    have hle := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := F) v y
    exact e.le.trans hle
  induction k generalizing x with
  | zero =>
    rw [pow_zero]
    exact hint x
  | succ k ih =>
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have h1 := (dV_isDiffVal v).2.1 a ha
      have h2 := ih b hb
      rw [show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul, map_mul, pow_succ']
      exact mul_le_mul' h1 h2
    · rw [show ((a + b : 𝓞 F) : F) = (a : F) + (b : F) from rfl, map_add]
      exact Valuation.map_add_le _ ha hb

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
