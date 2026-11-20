import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiffGenLoc

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `h : ∃ d, IsDiffVal v d` using `diffExists v`. Unfold `dV`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem dV_isDiffVal : IsDiffVal v (dV v) := by
  have h : ∃ d, IsDiffVal v d := diffExists v
  unfold dV
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Establish `hint : ∀ y : 𝓞 F, Valued.v (algebraMap F (Fv F v) (y : F)) ≤ 1`. Introduce `y`. Establish `e` using `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v y`. Establish `hle` using `IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := F) v y`. Conclude with `e.le.trans hle`.

Proceed by induction on `k generalizing x with`. Consider the case `zero`. Rewrite using `[pow_zero]`. Conclude with `hint x`. Consider the case `succ k ih`.

Rewrite `hx` using `[pow_succ']`. Use `Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Establish `h1` using `(dV_isDiffVal v).2.1 a ha`. Establish `h2` using `ih b hb`. Rewrite using `[show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul, map_mul, pow_succ']`.

Conclude with `mul_le_mul' h1 h2`. Rewrite using `[show ((a + b : 𝓞 F) : F) = (a : F) + (b : F) from rfl, map_add]`. Conclude with `Valuation.map_add_le _ ha hb`.
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
