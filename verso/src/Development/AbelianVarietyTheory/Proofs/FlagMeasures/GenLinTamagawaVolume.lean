import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidueStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPowStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

/- English proof (translation)
Introduce `E _ _ hE j hj`. Proceed by induction on `j, hj using Nat.le_induction with`. Consider the case `base => simpa using GlobalTheory.T.glNormOneAdelicQuotientVolume_one_eq_residue E hE`. Consider the case `succ j hj ih`. Establish `hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv E`.

Unfold `Formalism.HermitianLatticesTheory.vInv`. Check the signs of the components of the expression. Establish `hz : 0 ≤ zetaE E (j + 1)` using `zero_le_one.trans (GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow E (j + 1) (by omega)).1`. Establish `h` using `GlobalTheory.T.glNormOneAdelicQuotientVolume_siegel_step E hE (j + 1) (by omega) (by rw [Nat.add_sub_cancel, ih]; exact ENNReal.ofReal_lt_top)`. Rewrite using `[h, Nat.add_sub_cancel, ih, ← ENNReal.ofReal_mul' (mul_nonneg (pow_nonneg hv _) hz), Finset.prod_Icc_succ_top (by omega)]`.

Use `congr 1`. Establish `e : Formalism.HermitianLatticesTheory.fDeg E * (j + 1) ^ 2 = Formalism.HermitianLatticesTheory.fDeg E * j ^ 2 + Formalism.HermitianLatticesTheory.fDeg E * (2 * (j + 1) - 1)`. Establish `: 2 * (j + 1) - 1 = 2 * j + 1` using `by omega`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem genLinVolume : GenLinVolume := by
  intro E _ _ hE j hj
  induction j, hj using Nat.le_induction with
  | base => simpa using GlobalTheory.T.glNormOneAdelicQuotientVolume_one_eq_residue E hE
  | succ j hj ih =>
    have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv E := by
      unfold Formalism.HermitianLatticesTheory.vInv
      positivity
    have hz : 0 ≤ zetaE E (j + 1) := zero_le_one.trans (GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow E (j + 1) (by omega)).1
    have h := GlobalTheory.T.glNormOneAdelicQuotientVolume_siegel_step E hE (j + 1) (by omega)
      (by rw [Nat.add_sub_cancel, ih]; exact ENNReal.ofReal_lt_top)
    rw [h, Nat.add_sub_cancel, ih, ← ENNReal.ofReal_mul' (mul_nonneg (pow_nonneg hv _) hz),
      Finset.prod_Icc_succ_top (by omega)]
    congr 1
    have e : Formalism.HermitianLatticesTheory.fDeg E * (j + 1) ^ 2 =
        Formalism.HermitianLatticesTheory.fDeg E * j ^ 2 + Formalism.HermitianLatticesTheory.fDeg E * (2 * (j + 1) - 1) := by
      have : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [this]; ring
    rw [e, pow_add]
    ring

end GlobalTheory.FlagMeas
