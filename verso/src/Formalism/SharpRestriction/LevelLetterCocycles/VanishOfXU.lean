import Formalism.SharpRestriction.LevelLetterCocycles.LevelOneUniformizerCoeffVanish
import Formalism.SharpRestriction.LevelLetterCocycles.CoeffAlgMul

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrC

open Formalism.MainNotions.N.Pv.LocalLengthBound.Ser PowerSeries

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules.
-/
theorem smulS_delta (g : PowerSeries LL) (w : V) (j : ℕ) :
    smulS g (fun k : ℤ => if k = 0 then w else 0) (j : ℤ) = coeff j g • w := by
  have hLB : LB 0 (fun k : ℤ => if k = 0 then w else 0) := by
    intro k hk
    simp [ne_of_lt hk]
  rw [smulS_eq_sum hLB g (j : ℤ) (j + 1) (by omega)]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg (by omega)]
    simp
  · intro hj
    simp at hj

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem LB_delta (w : V) : LB 0 (fun k : ℤ => if k = 0 then w else 0) := by
  intro k hk
  simp [ne_of_lt hk]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem LB_fsum {ι : Type} (s : Finset ι) {m : ℤ} (F : ι → ℤ → V) (hF : ∀ i, LB m (F i)) :
    LB m (∑ i ∈ s, F i) := by
  refine Finset.induction_on s (fun k _ => by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha]
  exact LB_add (hF a) ih

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem smulS_fsum {ι : Type} (s : Finset ι) (g : PowerSeries LL) {m : ℤ} (F : ι → ℤ → V)
    (hF : ∀ i, LB m (F i)) : smulS g (∑ i ∈ s, F i) = ∑ i ∈ s, smulS g (F i) := by
  refine Finset.induction_on s ?_ ?_
  · funext k
    simp [smulS]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, smulS_add (hF a) (LB_fsum s F hF), ih]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem smulS_shift (g : PowerSeries LL) {m : ℤ} {F : ℤ → V} (hF : LB m F) (H : ℕ) :
    smulS (X ^ H * g) F = fun r => smulS g F (r - H) := by
  rw [smulS_mul hF, smulS_X_pow (LB_smulS hF g)]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem LB_of_unit {U : PowerSeries LL} (hU : constantCoeff U ≠ 0) {m N : ℤ} {F : ℤ → V} (hF : LB m F)
    (h : LB N (smulS U F)) : LB N F := by
  have h2 := LB_smulS h U⁻¹
  rwa [smulS_inv hF U hU] at h2

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem vanish_of_XU {U : PowerSeries LL} (hU : constantCoeff U ≠ 0) {m : ℤ} {F : ℤ → V} (hF : LB m F)
    (H : ℕ) (N : ℤ) (h : ∀ r < N + H, smulS (X ^ H * U) F r = 0) : LB N F := by
  apply LB_of_unit hU hF
  intro r hr
  have := h (r + H) (by omega)
  rw [smulS_shift U hF H] at this
  simpa using this

end Formalism.MainNotions.UnusedSlot80.CrC
