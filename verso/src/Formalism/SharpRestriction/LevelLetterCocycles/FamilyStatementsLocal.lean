import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller

noncomputable section

namespace Formalism.MainNotions.FamilyNumericLemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Filter Topology

def kF (c : ℝ) : ℝ := (1 + Real.exp (-(c * Real.log 6))) / (1 - Real.exp (-(c * Real.log 6)))

/- English proof (translation)
Establish `h6 : 0 < Real.log 6` using `Real.log_pos (by norm_num)`. Conclude with `Real.exp_lt_one_iff.mpr (by nlinarith)`.
-/
theorem exp_neg_log_six_lt_one {c : ℝ} (hc : 0 < c) : Real.exp (-(c * Real.log 6)) < 1 := by
  have h6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  exact Real.exp_lt_one_iff.mpr (by nlinarith)

/- English proof (translation)
Establish `h` using `exp_neg_log_six_lt_one hc`. Establish `h0` using `Real.exp_pos (-(c * Real.log 6))`. Unfold `kF`. Conclude with `div_nonneg (by linarith) (by linarith)`.
-/
theorem kF_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ kF c := by
  have h := exp_neg_log_six_lt_one hc
  have h0 := Real.exp_pos (-(c * Real.log 6))
  unfold kF
  exact div_nonneg (by linarith) (by linarith)

/- English proof (translation)
Establish `h` using `exp_neg_log_six_lt_one hc`. Unfold `kF`. Clear denominators, using `[show (1 - Real.exp (-(c * Real.log 6))) ≠ 0 by linarith]` for the nonvanishing conditions.
-/
theorem kF_mul {c : ℝ} (hc : 0 < c) : kF c * (1 - Real.exp (-(c * Real.log 6))) = 1 + Real.exp (-(c * Real.log 6)) := by
  have h := exp_neg_log_six_lt_one hc
  unfold kF
  field_simp [show (1 - Real.exp (-(c * Real.log 6))) ≠ 0 by linarith]

/- English proof (translation)
Use extensionality with `t`. Simplify using `[cyl]`.
-/
theorem cyl_univ (D : D7) (k : Fin 2) : cyl D k Set.univ = Set.univ := by
  ext t; simp [cyl]

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun t _ => Finset.prod_nonneg fun v _ => (hL k v).1 (t v)`.
-/
theorem locShare_nonneg (D : D7) (eV : VecAt D) (CL : ℝ) (hL : lawL D eV CL) (k : Fin 2) (S : Finset (Tup D k)) :
    0 ≤ locShare D eV k S :=
  Finset.sum_nonneg fun t _ => Finset.prod_nonneg fun v _ => (hL k v).1 (t v)

end Formalism.MainNotions.FamilyNumericLemmas
