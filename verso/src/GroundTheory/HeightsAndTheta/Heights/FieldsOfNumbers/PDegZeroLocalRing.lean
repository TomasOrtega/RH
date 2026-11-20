import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocQuot
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocal
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocNoetherian
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Split into cases according to the possible forms of the given data. Treat this case separately.

Rewrite the indicated hypotheses using the stated equalities. Treat this case separately. Proceed by induction. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem ringKrullDim_eq_of_relDim {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {F : Type u} [Field F] {Q : Ideal (MRing ι F)} {m : ℕ} (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  have hm : ((m : ℕ) : WithBot (WithTop ℤ)) = (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  unfold relDim at h
  rw [hm] at h
  cases hd : ringKrullDim (MRing ι F ⧸ Q) with
  | bot =>
    rw [hd] at h
    exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [hd] at h
      simp only [WithBot.map_coe, WithBot.coe_inj] at h
      exact absurd h (WithTop.top_ne_coe)
    | coe D =>
      rw [hd] at h
      simp only [WithBot.map_coe, WithBot.coe_inj] at h
      change (((D : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) = ((m : ℤ) : WithTop ℤ) at h
      have h := WithTop.coe_inj.mp h
      have : D = m + Fintype.card K := by omega
      rw [this]
      rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Replace the chosen expression with an arbitrary variable. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities.

Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Proceed by induction. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities.

Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
theorem DegZeroLocalRing.proof (h1 : DegZeroLocLocal.Statement.{u})
    (h2 : DegZeroLocNoetherian.Statement.{u}) (h3 : DegZeroLocDim.Statement.{u}) :
    DegZeroLocalRing.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  refine ⟨⟨h2 F K ι P hP W hW hPW, h1 F K ι P hP W hW hPW⟩, fun n hn1 hn => ?_⟩
  have e := h3 F K ι P hP W hW hPW
  rw [ringKrullDim_eq_of_relDim hn1, ringKrullDim_eq_of_relDim hn] at e
  revert e
  generalize ringKrullDim (degZeroLoc P {W}) = d
  intro e
  cases d with
  | bot =>
    rw [WithBot.bot_add] at e
    exact absurd e WithBot.bot_ne_coe
  | coe d =>
    rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj] at e
    induction d using ENat.recTopCoe with
    | top =>
      rw [top_add] at e
      exact absurd e.symm (ENat.natCast_ne_top _)
    | coe d =>
      rw [← Nat.cast_add, Nat.cast_inj] at e
      have : d = 1 := by omega
      rw [this]
      rfl

end

end GroundTheory.Heights₂.Heights.FieldNumbers
