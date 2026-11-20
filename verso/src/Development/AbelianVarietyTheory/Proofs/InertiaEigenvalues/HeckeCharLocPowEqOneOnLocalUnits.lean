import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.LocUnitPow

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Break down `eq_or_ne γ 0 with rfl | h0` into its components or cases. Conclude with `zero_le`. Rewrite `h`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Rewrite using `[WithZero.exp_le_exp]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `e : z ^ (m + 1) - 1 = z ^ m * (z - 1) + (z ^ m - 1)` using `by ring`. Rewrite using `[e]`.

Use `Valuation.map_add_le _ ?_ ih` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hz, one_pow, one_mul]`.
-/
theorem val_pow_sub_one_le {v : HeightOneSpectrum (𝓞 L)} {z : v.adicCompletion L} (hz : Valued.v z = 1) (i : ℕ) :
    Valued.v (z ^ i - 1) ≤ Valued.v (z - 1) := by
  induction i with
  | zero => simp
  | succ m ih =>
    have e : z ^ (m + 1) - 1 = z ^ m * (z - 1) + (z ^ m - 1) := by ring
    rw [e]
    refine Valuation.map_add_le _ ?_ ih
    rw [map_mul, map_pow, hz, one_pow, one_mul]

/- English proof (translation)
Establish `e : z ^ N - 1 = (z - 1) * ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L))`. Rewrite using `[← geom_sum_mul, Finset.sum_sub_distrib]`. Simplify using `[mul_comm]`. Establish `hS : Valued.v ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ)`. Use `Valuation.map_add_le _ ?_ hN` and prove the remaining obligations.

Use `Valuation.map_sum_le _ fun i _ => ?_` and prove the remaining obligations. Conclude with `(val_pow_sub_one_le hz i).trans (hj.trans (WithZero.exp_le_exp.mpr (by omega)))`. Rewrite using `[e, map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_pow_sub_one_step {v : HeightOneSpectrum (𝓞 L)} {N : ℕ}
    (hN : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ))
    {z : v.adicCompletion L} (hz : Valued.v z = 1) {j : ℤ} (hj : Valued.v (z - 1) ≤ WithZero.exp (-j)) (hj1 : 1 ≤ j) :
    Valued.v (z ^ N - 1) ≤ WithZero.exp (-(j + 1)) := by
  have e : z ^ N - 1 = (z - 1) * ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) := by
    rw [← geom_sum_mul, Finset.sum_sub_distrib]
    simp [mul_comm]
  have hS : Valued.v ((∑ i ∈ Finset.range N, (z ^ i - 1)) + (N : v.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
    refine Valuation.map_add_le _ ?_ hN
    refine Valuation.map_sum_le _ fun i _ => ?_
    exact (val_pow_sub_one_le hz i).trans (hj.trans (WithZero.exp_le_exp.mpr (by omega)))
  rw [e, map_mul]
  calc _ ≤ WithZero.exp (-j) * WithZero.exp (-1 : ℤ) := mul_le_mul' hj hS
    _ = _ := by rw [← WithZero.exp_add]; congr 1; ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using hz1`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_mul]`. Establish `hzk : Valued.v (z ^ N ^ k) = 1` using `by rw [map_pow, hz, one_pow]`.

Use `val_pow_sub_one_step hN hzk ih (by omega)` as an intermediate fact. Use `this using 3` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_pow_pow_sub_one_le {v : HeightOneSpectrum (𝓞 L)} {N : ℕ}
    (hN : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ))
    {z : v.adicCompletion L} (hz : Valued.v z = 1) (hz1 : Valued.v (z - 1) ≤ WithZero.exp (-1 : ℤ)) (k : ℕ) :
    Valued.v (z ^ (N ^ k) - 1) ≤ WithZero.exp (-((k : ℤ) + 1)) := by
  induction k with
  | zero => simpa using hz1
  | succ k ih =>
    rw [pow_succ, pow_mul]
    have hzk : Valued.v (z ^ N ^ k) = 1 := by rw [map_pow, hz, one_pow]
    have := val_pow_sub_one_step hN hzk ih (by omega)
    convert this using 3
    push_cast
    ring

/- English proof (translation)
Introduce `L _ _ χ v x hx`. Take `⟨n, hn⟩` from `GlobalTheory.Mem.UnrAe.exists_levelLe χ v`. Use `Formalism.UG.P.glint_finite_residueField (F := L) v` as an intermediate fact. Set `_` to `Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))`. Use `set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hNdef`.

Establish `hN2 : 1 < N` using `Fintype.one_lt_card`. Establish `hNv : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ)`. Establish `hr : IsLocalRing.residue (v.adicCompletionIntegers L) (N : v.adicCompletionIntegers L) = 0`. Rewrite using `[map_natCast]`. Conclude with `FiniteField.cast_card_eq_zero _`.

Rewrite `hr` using `[IsLocalRing.residue_eq_zero_iff]`. Establish `hlt : Valued.v (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1` using `(Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hr`. Establish `e : (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) = (N : v.adicCompletion L)` using `by push_cast; rfl`. Rewrite `hlt` using `[e]`. Conclude with `le_exp_neg_one' hlt`.

Establish `hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `hx.le`. Use `set y : v.adicCompletionIntegers L := ⟨x, hxO⟩`. Establish `hyu : IsUnit y` using `HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx`.

Establish `hr : IsLocalRing.residue _ y ≠ 0`. Rewrite using `[ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]`. Conclude with `hyu`. Establish `hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0`. Rewrite using `[map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]`.

Rewrite `hp` using `[IsLocalRing.residue_eq_zero_iff]`. Establish `hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1` using `(Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp`. Establish `e : (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) = (x : v.adicCompletion L) ^ (N - 1) - 1` using `by push_cast; rfl`. Rewrite `hlt` using `[e]`. Establish `hx1` using `le_exp_neg_one' hlt`.

Establish `hz : Valued.v ((x : v.adicCompletion L) ^ (N - 1)) = 1`. Rewrite using `[map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]`. Establish `key` using `val_pow_pow_sub_one_le hNv hz hx1 n`. Use `⟨(N - 1) * N ^ n, Nat.mul_pos (by omega) (pow_pos (by omega) _), ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`.

Use `hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx _) ?_` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val, pow_mul]`. Conclude with `key.trans (WithZero.exp_le_exp.mpr (by omega))`.
-/
theorem loc_pow_eq_one : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ), Formalism.L2.Host.IsUnitAt v x → ∃ m : ℕ, 0 < m ∧ χ.loc v x ^ m = 1 := by
  intro L _ _ χ v x hx
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ v
  have := Formalism.UG.P.glint_finite_residueField (F := L) v
  let _ := Fintype.ofFinite (IsLocalRing.ResidueField (v.adicCompletionIntegers L))
  set N := Fintype.card (IsLocalRing.ResidueField (v.adicCompletionIntegers L)) with hNdef
  have hN2 : 1 < N := Fintype.one_lt_card
  have hNv : Valued.v (N : v.adicCompletion L) ≤ WithZero.exp (-1 : ℤ) := by
    have hr : IsLocalRing.residue (v.adicCompletionIntegers L) (N : v.adicCompletionIntegers L) = 0 := by
      rw [map_natCast]; exact FiniteField.cast_card_eq_zero _
    rw [IsLocalRing.residue_eq_zero_iff] at hr
    have hlt : Valued.v (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
      (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hr
    have e : (((N : v.adicCompletionIntegers L)) : v.adicCompletion L) = (N : v.adicCompletion L) := by
      push_cast; rfl
    rw [e] at hlt
    exact le_exp_neg_one' hlt
  have hxO : (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
  set y : v.adicCompletionIntegers L := ⟨x, hxO⟩
  have hyu : IsUnit y := HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 hx
  have hr : IsLocalRing.residue _ y ≠ 0 := by
    rw [ne_eq, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hyu
  have hp : IsLocalRing.residue _ (y ^ (N - 1) - 1) = 0 := by
    rw [map_sub, map_pow, map_one, FiniteField.pow_card_sub_one_eq_one _ hr, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff] at hp
  have hlt : Valued.v (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion L) (WithZero (Multiplicative ℤ))))).1 hp
  have e : (((y ^ (N - 1) - 1 : v.adicCompletionIntegers L)) : v.adicCompletion L) =
      (x : v.adicCompletion L) ^ (N - 1) - 1 := by
    push_cast; rfl
  rw [e] at hlt
  have hx1 := le_exp_neg_one' hlt
  have hz : Valued.v ((x : v.adicCompletion L) ^ (N - 1)) = 1 := by
    rw [map_pow, show Valued.v (x : v.adicCompletion L) = 1 from hx, one_pow]
  have key := val_pow_pow_sub_one_le hNv hz hx1 n
  refine ⟨(N - 1) * N ^ n, Nat.mul_pos (by omega) (pow_pos (by omega) _), ?_⟩
  rw [← map_pow]
  refine hn _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx _) ?_
  rw [Units.val_pow_eq_pow_val, pow_mul]
  exact key.trans (WithZero.exp_le_exp.mpr (by omega))

end GlobalTheory.LocUnitPow
