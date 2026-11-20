import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

/- English proof (translation)
Use `set r : ℝ := (NNReal.sqrt (qF F : NNReal) : ℝ) with hr`. Establish `hq0 : (0 : ℝ) < residueCard F`. Conclude with `zero_lt_one.trans one_lt_residueCard` after adjusting the coercions. Establish `hrq : r ^ 2 = (residueCard F : ℝ)`. Rewrite using `[hr, ← NNReal.coe_pow, NNReal.sq_sqrt]`.

Simplify using `[qF, residueCard]`. Establish `hr0 : 0 < r`. Break down `(NNReal.coe_nonneg (NNReal.sqrt (qF F : NNReal))).lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Establish `: r = 0` using `h.symm`. Rewrite `hrq` using `[this]`. Simplify using `at hrq`. Conclude with `hq0.ne' (by exact_mod_cast hrq.symm)`. Establish `hord : ord (((uniformizerUnit F ^ m : Fˣ)) : F) = m`.

Rewrite using `[ord_units_zpow, coe_uniformizerUnit, ord_uniformizer (irreducible_uniformizer F), mul_one]`. Establish `hmod : ((modulus (((uniformizerUnit F ^ m : Fˣ)) : F) : NNReal) : ℝ) = r ^ (-(2 * m))`. Rewrite using `[modulus_of_ne_zero (Units.ne_zero _), hord, NNReal.coe_zpow, NNReal.coe_natCast, ← hrq, ← zpow_natCast, ← _root_.zpow_mul]`. Evaluate the numerical expressions. Establish `hpow : (r ^ (-(2 * m))) ^ ((t : ℝ) / 2) = r ^ (-(t * m))`.

Rewrite using `[← Real.rpow_intCast, ← Real.rpow_mul hr0.le, ← Real.rpow_intCast]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hcast : ((t : ℂ) / 2) = (((t : ℝ) / 2 : ℝ) : ℂ)` using `by push_cast; rfl`.

Establish `hnn : 0 ≤ r ^ (-(2 * m))` using `(zpow_pos hr0 _).le`. Unfold `Ad3.mp`. Rewrite using `[hmod, hcast, ← Complex.ofReal_cpow hnn, hpow, Complex.ofReal_zpow]`. Both sides reduce to the same expression.
-/
theorem mp_uniformizerUnit_zpow_half (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (m t : ℤ) :
    Ad3.mp (uniformizerUnit F ^ m) ((t : ℂ) / 2) = sqrtQ F ^ (-(t * m)) := by
  set r : ℝ := (NNReal.sqrt (qF F : NNReal) : ℝ) with hr
  have hq0 : (0 : ℝ) < residueCard F := by
    exact_mod_cast zero_lt_one.trans one_lt_residueCard
  have hrq : r ^ 2 = (residueCard F : ℝ) := by
    rw [hr, ← NNReal.coe_pow, NNReal.sq_sqrt]
    simp [qF, residueCard]
  have hr0 : 0 < r := by
    rcases (NNReal.coe_nonneg (NNReal.sqrt (qF F : NNReal))).lt_or_eq with h | h
    · exact h
    · exfalso
      have : r = 0 := h.symm
      rw [this] at hrq
      simp at hrq
      exact hq0.ne' (by exact_mod_cast hrq.symm)
  have hord : ord (((uniformizerUnit F ^ m : Fˣ)) : F) = m := by
    rw [ord_units_zpow, coe_uniformizerUnit, ord_uniformizer (irreducible_uniformizer F), mul_one]
  have hmod : ((modulus (((uniformizerUnit F ^ m : Fˣ)) : F) : NNReal) : ℝ) = r ^ (-(2 * m)) := by
    rw [modulus_of_ne_zero (Units.ne_zero _), hord, NNReal.coe_zpow, NNReal.coe_natCast, ← hrq,
      ← zpow_natCast, ← _root_.zpow_mul]
    norm_num
  have hpow : (r ^ (-(2 * m))) ^ ((t : ℝ) / 2) = r ^ (-(t * m)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hr0.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hcast : ((t : ℂ) / 2) = (((t : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  have hnn : 0 ≤ r ^ (-(2 * m)) := (zpow_pos hr0 _).le
  unfold Ad3.mp
  rw [hmod, hcast, ← Complex.ofReal_cpow hnn, hpow, Complex.ofReal_zpow]
  rfl

end GlobalTheory.CompanionTheory.LFUDom
