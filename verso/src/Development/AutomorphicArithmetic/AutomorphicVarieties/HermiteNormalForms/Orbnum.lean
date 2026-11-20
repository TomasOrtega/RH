import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Establish `hd1 : 1 ≤ d` using `le_trans hN hd`. Use `set B := 2 * D * d with hBdef`. Establish `hB2 : 2 ≤ B`. Establish `: 1 ≤ D * d` using `Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))`. Rewrite using `[hBdef, mul_assoc]`.

Use linear arithmetic over natural numbers and integers. Establish `hDB : D ≤ B`. Rewrite using `[hBdef]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hdB : d ≤ B`.

Rewrite using `[hBdef]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hNB : N ≤ B` using `le_trans hd hdB`. Establish `hX : D ^ N * d ^ d ≤ B ^ (2 * d)`. Establish `a : D ^ N ≤ B ^ d` using `le_trans (Nat.pow_le_pow_left hDB N) (Nat.pow_le_pow_right (by omega) hd)`.

Establish `b : d ^ d ≤ B ^ d` using `Nat.pow_le_pow_left hdB d`. Combine the equalities or inequalities in the displayed calculation. Establish `hX1 : 1 ≤ D ^ N * d ^ d` using `Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)))`. Establish `hNN : N ^ N ≤ B ^ d` using `le_trans (Nat.pow_le_pow_left hNB N) (Nat.pow_le_pow_right (by omega) hd)`. Establish `hNN1 : 1 ≤ N ^ N` using `Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))`.

Establish `f1 : (D ^ N * d ^ d) ^ (1 + d * N) ≤ B ^ (2 * d * (1 + d * N))`. Rewrite using `[pow_mul B]`. Conclude with `Nat.pow_le_pow_left hX _`. Establish `hin : 2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1 ≤ B ^ (5 * d + 2)`. Establish `hY1 : 1 ≤ N ^ N * (D ^ N * d ^ d) ^ 2` using `Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))`.

Establish `hY : N ^ N * (D ^ N * d ^ d) ^ 2 ≤ B ^ d * (B ^ (2 * d)) ^ 2` using `Nat.mul_le_mul hNN (Nat.pow_le_pow_left hX 2)`. Establish `h4 : 4 ≤ B ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hin2 : (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1 ≤ B ^ ((5 * d + 2) * d + 1)`. Establish `a : (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d ≤ B ^ ((5 * d + 2) * d)`.

Rewrite using `[pow_mul B]`. Conclude with `Nat.pow_le_pow_left hin d`. Establish `b : 1 ≤ B ^ ((5 * d + 2) * d)` using `Nat.one_le_pow _ _ (by omega)`. Combine the equalities or inequalities in the displayed calculation. Establish `f2 : ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1)) ≤ B ^ (((5 * d + 2) * d + 1) * (d * N * (p + 1)))`.

Rewrite using `[pow_mul B]`. Conclude with `Nat.pow_le_pow_left hin2 _`. Establish `hexp : 2 * d * (1 + d * N) + ((5 * d + 2) * d + 1) * (d * N * (p + 1)) ≤ 12 * (p + 1) * d ^ 3 * N`. Establish `e1 : d ≤ d ^ 3 * N * (p + 1)`. Establish `: 1 ≤ d ^ 2 * N * (p + 1)` using `Nat.one_le_iff_ne_zero.mpr (by positivity)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : d ^ 2 * N ≤ d ^ 3 * N * (p + 1)`. Establish `: 1 ≤ d * (p + 1)` using `Nat.one_le_iff_ne_zero.mpr (by positivity)`. Use the polynomial consequences of the given equalities and inequalities. Establish `e3 : d * N * (p + 1) ≤ d ^ 3 * N * (p + 1)`.

Establish `: 1 ≤ d ^ 2` using `Nat.one_le_pow _ _ (by omega)`. Use the polynomial consequences of the given equalities and inequalities. Establish `e4 : d ^ 2 * N * (p + 1) ≤ d ^ 3 * N * (p + 1)`. Establish `: d ^ 2 * N * (p + 1) * 1 ≤ d ^ 2 * N * (p + 1) * d` using `Nat.mul_le_mul_left _ hd1`. Use the polynomial consequences of the given equalities and inequalities.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem UpperTheory.V.KT.orbit_number_power_bound (D d N p : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hd : N ≤ d) :
    (D ^ N * d ^ d) ^ (1 + d * N) *
      ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1)) ≤
    (2 * D * d) ^ (12 * (p + 1) * d ^ 3 * N) := by
  have hd1 : 1 ≤ d := le_trans hN hd
  set B := 2 * D * d with hBdef
  have hB2 : 2 ≤ B := by
    have : 1 ≤ D * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [hBdef, mul_assoc]
    omega
  have hDB : D ≤ B := by
    rw [hBdef]
    nlinarith
  have hdB : d ≤ B := by
    rw [hBdef]
    nlinarith
  have hNB : N ≤ B := le_trans hd hdB
  have hX : D ^ N * d ^ d ≤ B ^ (2 * d) := by
    have a : D ^ N ≤ B ^ d :=
      le_trans (Nat.pow_le_pow_left hDB N) (Nat.pow_le_pow_right (by omega) hd)
    have b : d ^ d ≤ B ^ d := Nat.pow_le_pow_left hdB d
    calc D ^ N * d ^ d ≤ B ^ d * B ^ d := Nat.mul_le_mul a b
      _ = B ^ (2 * d) := by ring
  have hX1 : 1 ≤ D ^ N * d ^ d :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)))
  have hNN : N ^ N ≤ B ^ d :=
    le_trans (Nat.pow_le_pow_left hNB N) (Nat.pow_le_pow_right (by omega) hd)
  have hNN1 : 1 ≤ N ^ N := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have f1 : (D ^ N * d ^ d) ^ (1 + d * N) ≤ B ^ (2 * d * (1 + d * N)) := by
    rw [pow_mul B]
    exact Nat.pow_le_pow_left hX _
  have hin : 2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1 ≤ B ^ (5 * d + 2) := by
    have hY1 : 1 ≤ N ^ N * (D ^ N * d ^ d) ^ 2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
    have hY : N ^ N * (D ^ N * d ^ d) ^ 2 ≤ B ^ d * (B ^ (2 * d)) ^ 2 :=
      Nat.mul_le_mul hNN (Nat.pow_le_pow_left hX 2)
    have h4 : 4 ≤ B ^ 2 := by nlinarith
    calc 2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1 ≤ 4 * (N ^ N * (D ^ N * d ^ d) ^ 2) := by omega
      _ ≤ B ^ 2 * (B ^ d * (B ^ (2 * d)) ^ 2) := Nat.mul_le_mul h4 hY
      _ = B ^ (5 * d + 2) := by ring
  have hin2 : (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1 ≤ B ^ ((5 * d + 2) * d + 1) := by
    have a : (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d ≤ B ^ ((5 * d + 2) * d) := by
      rw [pow_mul B]
      exact Nat.pow_le_pow_left hin d
    have b : 1 ≤ B ^ ((5 * d + 2) * d) := Nat.one_le_pow _ _ (by omega)
    calc (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1 ≤ 2 * B ^ ((5 * d + 2) * d) := by omega
      _ ≤ B * B ^ ((5 * d + 2) * d) := Nat.mul_le_mul_right _ hB2
      _ = B ^ ((5 * d + 2) * d + 1) := by ring
  have f2 : ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1)) ≤
      B ^ (((5 * d + 2) * d + 1) * (d * N * (p + 1))) := by
    rw [pow_mul B]
    exact Nat.pow_le_pow_left hin2 _
  have hexp : 2 * d * (1 + d * N) + ((5 * d + 2) * d + 1) * (d * N * (p + 1)) ≤
      12 * (p + 1) * d ^ 3 * N := by
    have e1 : d ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d ^ 2 * N * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have e2 : d ^ 2 * N ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have e3 : d * N * (p + 1) ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have e4 : d ^ 2 * N * (p + 1) ≤ d ^ 3 * N * (p + 1) := by
      have : d ^ 2 * N * (p + 1) * 1 ≤ d ^ 2 * N * (p + 1) * d := Nat.mul_le_mul_left _ hd1
      nlinarith
    nlinarith
  calc (D ^ N * d ^ d) ^ (1 + d * N) *
        ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1))
      ≤ B ^ (2 * d * (1 + d * N)) * B ^ (((5 * d + 2) * d + 1) * (d * N * (p + 1))) :=
        Nat.mul_le_mul f1 f2
    _ = B ^ (2 * d * (1 + d * N) + ((5 * d + 2) * d + 1) * (d * N * (p + 1))) := by ring
    _ ≤ B ^ (12 * (p + 1) * d ^ 3 * N) := Nat.pow_le_pow_right (by omega) hexp

/- English proof (translation)
Introduce `L _ _ N p hN`. Establish `hD : 1 ≤ absD L` using `Nat.one_le_iff_ne_zero.mpr (by`. Simplify using `only [absD, ne_eq, Int.natAbs_eq_zero]`. Conclude with `NumberField.discr_ne_zero L)`. Establish `hd : N ≤ dd L N`.

Simplify using `only [dd]`. Establish `: 1 ≤ Module.finrank ℚ L` using `Module.finrank_pos`. Use the polynomial consequences of the given equalities and inequalities. Use `orbit_number_power_bound (absD L) (dd L N) N p hD hN hd` as an intermediate fact. Simplify `this` using `only [orbBound, I0, RR]`.
-/
theorem UpperTheory.V.KT.orbnum :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (p : ℕ), 1 ≤ N →
    orbBound L N p ≤ (2 * absD L * dd L N) ^ (12 * (p + 1) * dd L N ^ 3 * N) := by
  intro L _ _ N p hN
  have hD : 1 ≤ absD L := Nat.one_le_iff_ne_zero.mpr (by
    simp only [absD, ne_eq, Int.natAbs_eq_zero]
    exact NumberField.discr_ne_zero L)
  have hd : N ≤ dd L N := by
    simp only [dd]
    have : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
    nlinarith
  have := orbit_number_power_bound (absD L) (dd L N) N p hD hN hd
  simpa only [orbBound, I0, RR] using this
