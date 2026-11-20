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
Establish `hm : ((m : ℕ) : WithBot (WithTop ℤ)) = (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))` using `rfl`. Unfold `relDim at h`. Rewrite `h` using `[hm]`. Consider the cases of `hd : ringKrullDim (MRing ι F ⧸ Q) with`. Consider the case `bot`.

Rewrite `h` using `[hd]`. Conclude with `absurd h (by simp)`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`.

Rewrite `h` using `[hd]`. Simplify using `only [WithBot.map_coe, WithBot.coe_inj] at h`. Conclude with `absurd h (WithTop.top_ne_coe)`. Consider the case `coe D`. Rewrite `h` using `[hd]`.

Simplify using `only [WithBot.map_coe, WithBot.coe_inj] at h`. Express the relevant statement in the definitionally equal form `(((D : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) = ((m : ℤ) : WithTop ℤ) at h`. Establish `h` using `WithTop.coe_inj.mp h`. Establish `: D = m + Fintype.card K` using `by omega`. Rewrite using `[this]`.

Both sides reduce to the same expression.
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
Introduce `F _ K _ _ ι _ P hP W hW hPW`. Use `hP.isPrime` as an intermediate fact. Use `⟨⟨h2 F K ι P hP W hW hPW, h1 F K ι P hP W hW hPW⟩, fun n hn1 hn => ?_⟩` and prove the remaining obligations. Establish `e` using `h3 F K ι P hP W hW hPW`. Rewrite `e` using `[ringKrullDim_eq_of_relDim hn1, ringKrullDim_eq_of_relDim hn]`.

Use `revert e`. Generalize the expression as in `ringKrullDim (degZeroLoc P {W}) = d`. Introduce `e`. Consider the cases of `d with`. Consider the case `bot`.

Rewrite `e` using `[WithBot.bot_add]`. Conclude with `absurd e WithBot.bot_ne_coe`. Consider the case `coe d`. Rewrite `e` using `[← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj]`. Proceed by induction on `d using ENat.recTopCoe with`.

Consider the case `top`. Rewrite `e` using `[top_add]`. Conclude with `absurd e.symm (ENat.natCast_ne_top _)`. Consider the case `coe d`. Rewrite `e` using `[← Nat.cast_add, Nat.cast_inj]`.

Establish `: d = 1` using `by omega`. Rewrite using `[this]`. Both sides reduce to the same expression.
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
