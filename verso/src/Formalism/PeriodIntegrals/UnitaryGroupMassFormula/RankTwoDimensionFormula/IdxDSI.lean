import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.FlagLevelCharacterEqPsiDivN

noncomputable section

open scoped Classical TensorProduct
open Matrix NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

namespace PI.UnitaryDimensionFormula

/- English proof (translation)
Introduce `I`. Use `⟨unitaryCongruence.sigA_sigA (I := I), ?_⟩` and prove the remaining obligations. Unfold `Formalism.UG.IsHerm Formalism.UG.cT`. Use extensionality with `i j`. Simplify using `[JA, sigA, Formalism.UG.inclE, Formalism.UG.sigR]`.

Use `congr 1`. Rewrite using `[← unitaryCongruence.J_conj (I := I) j i]`. Use `first`. Consider the case `rfl`. Consider the case `simp`.
-/
theorem idxDSig : IdxDSig := by
  intro I
  refine ⟨unitaryCongruence.sigA_sigA (I := I), ?_⟩
  unfold Formalism.UG.IsHerm Formalism.UG.cT
  ext i j
  simp [JA, sigA, Formalism.UG.inclE, Formalism.UG.sigR]
  congr 1
  rw [← unitaryCongruence.J_conj (I := I) j i]
  first
  | rfl
  | simp

/- English proof (translation)
Introduce `I` and use `⟨fun _ hx _ hy => unitaryCongruence.hA_int I hx hy, fun _ hc => unitaryCongruence.sigA_mem I hc⟩`.
-/
theorem idxDInt : IdxDInt := fun I =>
  ⟨fun _ hx _ hy => unitaryCongruence.hA_int I hx hy, fun _ hc => unitaryCongruence.sigA_mem I hc⟩

end PI.UnitaryDimensionFormula
