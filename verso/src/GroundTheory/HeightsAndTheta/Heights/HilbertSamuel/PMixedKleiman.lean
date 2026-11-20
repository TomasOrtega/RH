import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleiman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleimanLow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleimanTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero => exact MixedKleiman.atDim_zero`. Consider the case `succ n ih`. Establish `ih' : MixedKleiman.AtDim (n + 1 - 1)` using `by simpa using ih`.

Establish `hLow : MixedKleiman.LowAt (n + 1)` using `hL (n + 1) ih'`. Introduce `K _ ι _ P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj`. Break down `lt_or_eq_of_le hj with hj | rfl` into its components or cases. Conclude with `hLow K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj`. Establish `hlist : (fun i : Fin (n + 1) => if (i : ℕ) < n + 1 then M else A) = fun _ => M`.

Use function extensionality and compare the values at `fun i => if_pos i.isLt`. Rewrite using `[hlist]`. Break down `Nat.lt_or_ge n 1 with hn | hn` into its components or cases. Take `rfl : n = 0` from `by omega`. Establish `hW` using `hhM P hP le_rfl`.

Establish `e : (fun _ : Fin 1 => M) = ![M]`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Both sides reduce to the same expression. Simplify `hW` using `[e]`.

Conclude with `hT (n + 1) (by omega) ih' hLow K ι P P0 M II hII h1 hP h0 hsM hnM hcM hhM`.
-/
theorem MixedKleiman.atDim_of_steps (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    ∀ d, MixedKleiman.AtDim d := by
  intro d
  induction d with
  | zero => exact MixedKleiman.atDim_zero
  | succ n ih =>
    have ih' : MixedKleiman.AtDim (n + 1 - 1) := by simpa using ih
    have hLow : MixedKleiman.LowAt (n + 1) := hL (n + 1) ih'
    intro K _ ι _ P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact hLow K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
    · have hlist : (fun i : Fin (n + 1) => if (i : ℕ) < n + 1 then M else A) = fun _ => M :=
        funext fun i => if_pos i.isLt
      rw [hlist]
      rcases Nat.lt_or_ge n 1 with hn | hn
      · obtain rfl : n = 0 := by omega
        have hW := hhM P hP le_rfl
        have e : (fun _ : Fin 1 => M) = ![M] := by
          funext i
          fin_cases i
          rfl
        simpa [e] using hW
      · exact hT (n + 1) (by omega) ih' hLow K ι P P0 M II hII h1 hP h0 hsM hnM hcM hhM

/- English proof (translation)
Introduce `K _ ι _ P P0 d M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj`. Conclude with `MixedKleiman.atDim_of_steps hL hT d K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj`.
-/
theorem MixedKleiman.proof (hL : MixedKleimanLow.Statement) (hT : MixedKleimanTop.Statement) :
    MixedKleiman.Statement := by
  intro K _ ι _ P P0 d M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj
  exact MixedKleiman.atDim_of_steps hL hT d K ι P P0 M A a II hII h1 hP h0 hsM hnM hcM hhM haA hsA hmA hcA j hj

end GroundTheory.Heights₂.Heights.HilbertSamuel
