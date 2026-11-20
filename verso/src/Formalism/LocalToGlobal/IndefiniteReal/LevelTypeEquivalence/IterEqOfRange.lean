import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterSymmR
import Formalism.FlagUnipotentLattices.KappaAssemblyOf

namespace Formalism.IndefR.Eqv

open scoped ContDiff
open MeasureTheory

section Pt

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ev {k : ℕ} (j : Fin k) : Fin k → ℝ := Pi.single j 1

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem norm_ev {k : ℕ} (j : Fin k) : ‖ev j‖ = 1 := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    by_cases h : i = j
    · subst h; simp [ev]
    · simp [ev, h]
  · have := norm_le_pi_norm (ev j) j
    simpa [ev] using this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem natCast_lt_inf (m : ℕ) : (m : WithTop ℕ∞) < ∞ := by
  exact_mod_cast ENat.natCast_lt_top m

noncomputable def dS {k : ℕ} (g : (Fin k → ℝ) → ℂ) (S : Finset (Fin k)) (t : Fin k → ℝ) : ℂ :=
  iteratedFDeriv ℝ S.card g t (fun a => ev (S.orderEmbOfFin rfl a))

end Pt

end Formalism.IndefR.Eqv
