import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank

namespace Formalism.BasicNotions

def Ranks.NF (R : Ranks) : ℕ := R.k + R.m * (R.t + (R.r + 6) + 1)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Use linear arithmetic over natural numbers and integers.
-/
theorem Ranks.NF_le (R : Ranks) : R.NF ≤ 2 * R.N R.m := by
  have h := R.rank_add_five_le
  have h1 : R.t + (R.r + 6) + 1 ≤ 2 * (R.t + 1) := by unfold Ranks.r; omega
  have h2 : R.m * (R.t + (R.r + 6) + 1) ≤ R.m * (2 * (R.t + 1)) := Nat.mul_le_mul_left _ h1
  have h3 : R.m * (2 * (R.t + 1)) = 2 * (R.m * (R.t + 1)) := by ring
  unfold Ranks.NF Ranks.N
  omega

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem Ranks.N_le_t_sq (R : Ranks) : R.N R.m ≤ R.t ^ 2 := by
  have h1 := R.rank_add_five_le
  have h2 := R.three_m_lt_t
  have h3 := R.two_le_m
  have hk : R.k ≤ R.t := by omega
  unfold Ranks.N
  nlinarith

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Ranks.NF_le_two_mul_t_sq (R : Ranks) : R.NF ≤ 2 * R.t ^ 2 :=
  le_trans R.NF_le (Nat.mul_le_mul_left _ R.N_le_t_sq)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Use linear arithmetic over natural numbers and integers.
-/
theorem ParamsT.nV_eq {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    D.R.nV = T.TO * T.nWn + (8 * D.R.f * D.R.r + 4) := by
  have h1 := T.split
  have h2 := T.nP_eq
  unfold Ranks.nV
  omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ParamsT.nV_ge {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) :
    8 * D.R.f * D.R.r + 4 ≤ D.R.nV := by
  rw [T.nV_eq]; exact Nat.le_add_left _ _

end Formalism.BasicNotions
