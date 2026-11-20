import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomSchurG
import Formalism.SharpRestriction.CuspSpanNormBounds.NearParameterGap
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge

/- English proof (translation)
Take `⟨hk, h2, h3, h4⟩` from `h1`. Establish `hmono : Formalism.FourierDecayAlt.ThreeDimData.aOf r h0 ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h`. Unfold `Formalism.FourierDecayAlt.ThreeDimData.aOf`. Apply `div_le_div_of_nonneg_right hle` to reduce the goal to its premises. Check the signs of the components of the expression.

Conclude with `⟨hk, h2.trans hle, h3.trans hmono, h4.trans hmono⟩`.
-/
theorem gapOK_mono {k r : ℕ} {h0 h : ℝ} (h1 : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h0) (hle : h0 ≤ h) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h := by
  obtain ⟨hk, h2, h3, h4⟩ := h1
  have hmono : Formalism.FourierDecayAlt.ThreeDimData.aOf r h0 ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    apply div_le_div_of_nonneg_right hle
    positivity
  exact ⟨hk, h2.trans hle, h3.trans hmono, h4.trans hmono⟩

/- English proof (translation)
Unfold `kaS gg`. Establish `hka` using `Formalism.MainNotions.BridgeLemma.sza_ka_pos D`. Establish `h0 : (0 : ℝ) < D.host.g 0` using `by exact_mod_cast (D.host.g_prime 0).pos`. Establish `h1 : (0 : ℝ) < D.host.g 1` using `by exact_mod_cast (D.host.g_prime 1).pos`. Check the signs of the components of the expression.
-/
theorem kaS_pos_of_hyp {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) :
    0 < kaS D := by
  unfold kaS gg
  have hka := Formalism.MainNotions.BridgeLemma.sza_ka_pos D
  have h0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have h1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  positivity

def H0 (k r : ℕ) : ℝ :=
  1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 4

/- English proof (translation)
Unfold `H0`. Establish `hN1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)`. Establish `haN : ((2 * r + 2 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 2 * r + 2 ≤ 2 * r + k + 1)`. Establish `ha0 : (0 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ)` using `by positivity`. Establish `h3 : ((3 * (r + 1) : ℕ) : ℝ) ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ)`.

Conclude with `(by omega : 3 * (r + 1) ≤ 2 * (2 * r + k + 1))` after adjusting the coercions. Establish `hpow : ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 5`. Combine the equalities or inequalities in the displayed calculation. Establish `hN0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by positivity`. Establish `hq : (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 4 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3`.

Establish `: ((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `mul_le_mul_of_nonneg_right h3 (by positivity)`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem explicit_gap_le_polynomial (k r : ℕ) (hk : 1 ≤ k) : H0 k r ≤ 1000 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 8 := by
  unfold H0
  have hN1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have haN : ((2 * r + 2 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 * r + 2 ≤ 2 * r + k + 1)
  have ha0 : (0 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := by positivity
  have h3 : ((3 * (r + 1) : ℕ) : ℝ) ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 3 * (r + 1) ≤ 2 * (2 * r + k + 1))
  have hpow : ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 := by
    calc ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) :=
          Real.rpow_le_rpow ha0 haN (by norm_num)
      _ ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ ((5 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 := Real.rpow_natCast _ _
  have hN0 : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by positivity
  have hq : (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 4 ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by
    have : ((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    nlinarith
  calc 1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 4
        = 1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
          ((((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 4) := by ring
    _ ≤ 1000 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hq (by positivity) (by positivity)
    _ = 1000 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 8 := by ring

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Establish `hc : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1)` using `by push_cast; ring`. Establish `hcpos : (0 : ℝ) < 2 * ((r : ℝ) + 1)` using `by positivity`. Establish `hsq : 0 < Real.sqrt (2 * ((r : ℝ) + 1))` using `Real.sqrt_pos.mpr hcpos`. Establish `hsq1 : 1 ≤ Real.sqrt (2 * ((r : ℝ) + 1))`.

Rewrite using `[Real.one_le_sqrt]`. Use `Nat.cast_nonneg (α := ℝ) r` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrp : ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) = (2 * ((r : ℝ) + 1)) ^ 4 * Real.sqrt (2 * ((r : ℝ) + 1))`. Rewrite using `[hc, show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add hcpos, Real.rpow_natCast, Real.sqrt_eq_rpow]`.

Establish `hH : H0 (j + 1) r = 250 * ((2 * ((r : ℝ) + 1)) ^ 4 * Real.sqrt (2 * ((r : ℝ) + 1))) * (3 * ((r : ℝ) + 1) * (2 * (r : ℝ) + (j : ℝ) + 2) ^ 2 + (2 * (r : ℝ) + (j : ℝ) + 2) ^ 3)`. Unfold `H0`. Rewrite using `[hrp]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hA : Formalism.FourierDecayAlt.ThreeDimData.aOf r (H0 (j + 1) r) = 125 / 4 * (2 * ((r : ℝ) + 1)) ^ 4 * (3 * ((r : ℝ) + 1) * (2 * (r : ℝ) + (j : ℝ) + 2) ^ 2 + (2 * (r : ℝ) + (j : ℝ) + 2) ^ 3)`. Rewrite using `[hH]`. Unfold `Formalism.FourierDecayAlt.ThreeDimData.aOf`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `⟨by omega, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hH]`. Establish `hX : 0 ≤ (2 * ((r : ℝ) + 1)) ^ 4 * (3 * ((r : ℝ) + 1) * (2 * (r : ℝ) + (j : ℝ) + 2) ^ 2 + (2 * (r : ℝ) + (j : ℝ) + 2) ^ 3)` using `by positivity`. Establish `h1` using `mul_le_mul_of_nonneg_left hsq1 hX`. Establish `h2 : 120 * ((2 * r + (j + 1) + 1 : ℕ) : ℝ) ^ 3 ≤ 250 * ((2 * ((r : ℝ) + 1)) ^ 4 * (3 * ((r : ℝ) + 1) * (2 * (r : ℝ) + (j : ℝ) + 2) ^ 2 + (2 * (r : ℝ) + (j : ℝ) + 2) ^ 3))`.

Rewrite using `[← sub_nonneg]`. Use `push_cast`. Put the polynomial expressions in normal form. Check the signs of the components of the expression. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[hA]`. Unfold `Formalism.FourierDecayAlt.ThreeDimData.Mexp Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.AG Formalism.FourierDecayAlt.ThreeDimData.dN`. Rewrite using `[← sub_nonneg]`. Use `push_cast`. Put the polynomial expressions in normal form.

Check the signs of the components of the expression. Rewrite using `[hA]`. Unfold `Formalism.FourierDecayAlt.ThreeDimData.AG`. Rewrite using `[← sub_nonneg]`. Use `push_cast`.

Put the polynomial expressions in normal form. Check the signs of the components of the expression.
-/
theorem gap_ok_explicit (k r : ℕ) (hk : 1 ≤ k) : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (H0 k r) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hc : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have hcpos : (0 : ℝ) < 2 * ((r : ℝ) + 1) := by positivity
  have hsq : 0 < Real.sqrt (2 * ((r : ℝ) + 1)) := Real.sqrt_pos.mpr hcpos
  have hsq1 : 1 ≤ Real.sqrt (2 * ((r : ℝ) + 1)) := by
    rw [Real.one_le_sqrt]
    have := Nat.cast_nonneg (α := ℝ) r
    linarith
  have hrp : ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) =
      (2 * ((r : ℝ) + 1)) ^ 4 * Real.sqrt (2 * ((r : ℝ) + 1)) := by
    rw [hc, show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add hcpos, Real.rpow_natCast,
      Real.sqrt_eq_rpow]
  have hH : H0 (j + 1) r = 250 * ((2 * ((r : ℝ) + 1)) ^ 4 * Real.sqrt (2 * ((r : ℝ) + 1))) *
      (3 * ((r : ℝ) + 1) * (2 * (r : ℝ) + (j : ℝ) + 2) ^ 2 + (2 * (r : ℝ) + (j : ℝ) + 2) ^ 3) := by
    unfold H0
    rw [hrp]
    push_cast
    ring
  have hA : Formalism.FourierDecayAlt.ThreeDimData.aOf r (H0 (j + 1) r) = 125 / 4 * (2 * ((r : ℝ) + 1)) ^ 4 *
      (3 * ((r : ℝ) + 1) * (2 * (r : ℝ) + (j : ℝ) + 2) ^ 2 + (2 * (r : ℝ) + (j : ℝ) + 2) ^ 3) := by
    rw [hH]
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    field_simp
    ring
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [hH]
    have hX : 0 ≤ (2 * ((r : ℝ) + 1)) ^ 4 *
        (3 * ((r : ℝ) + 1) * (2 * (r : ℝ) + (j : ℝ) + 2) ^ 2 + (2 * (r : ℝ) + (j : ℝ) + 2) ^ 3) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsq1 hX
    have h2 : 120 * ((2 * r + (j + 1) + 1 : ℕ) : ℝ) ^ 3 ≤ 250 * ((2 * ((r : ℝ) + 1)) ^ 4 *
        (3 * ((r : ℝ) + 1) * (2 * (r : ℝ) + (j : ℝ) + 2) ^ 2 + (2 * (r : ℝ) + (j : ℝ) + 2) ^ 3)) := by
      rw [← sub_nonneg]
      push_cast
      ring_nf
      positivity
    nlinarith
  · rw [hA]
    unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp Formalism.FourierDecayAlt.ThreeDimData.AS Formalism.FourierDecayAlt.ThreeDimData.AG Formalism.FourierDecayAlt.ThreeDimData.dN
    rw [← sub_nonneg]
    push_cast
    ring_nf
    positivity
  · rw [hA]
    unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    rw [← sub_nonneg]
    push_cast
    ring_nf
    positivity

/- English proof (translation)
Establish `hmf : D.R.m ^ 4 ≤ D.R.f` using `hH.2.2.1`. Establish `hfk : D.R.f ≤ D.R.k` using `hH.2.2.2.1`. Establish `hCl : 0 < Cl` using `hH.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2`. Establish `hk3 : 3 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hm2 : 2 ≤ D.R.m` using `D.R.two_le_m`.

Establish `hrk : D.R.k + 1 ≤ D.R.r` using `by show D.R.k + 1 ≤ D.R.k + D.R.m - 1`. Use linear arithmetic over natural numbers and integers. Establish `hK : (3 : ℝ) ≤ (D.R.k : ℝ)` using `by exact_mod_cast hk3`. Establish `hM : (2 : ℝ) ≤ (D.R.m : ℝ)` using `by exact_mod_cast hm2`. Establish `hMF : (D.R.m : ℝ) ^ 4 ≤ (D.R.f : ℝ)` using `by exact_mod_cast hmf`.

Establish `hRK : (D.R.k : ℝ) + 1 ≤ (D.R.r : ℝ)` using `by exact_mod_cast hrk`. Establish `hR1 : 1 ≤ (D.R.r : ℝ)` using `by linarith`. Establish `hF1 : 1 ≤ (D.R.f : ℝ)`. Establish `: (1 : ℝ) ≤ (D.R.m : ℝ) ^ 4` using `one_le_pow₀ (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hX0 : 0 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5` using `by positivity`. Establish `hX8 : (D.R.r : ℝ) ^ 8 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5`. Combine the equalities or inequalities in the displayed calculation. Establish `hX2 : 2 * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5`. Establish `h1 : (D.R.r : ℝ) ^ 2 ≤ (D.R.r : ℝ) ^ 19` using `pow_le_pow_right₀ hR1 (by norm_num)`.

Establish `h2 : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 5`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : (D.R.m : ℝ) ^ 3 ≤ (D.R.m : ℝ) ^ 4` using `pow_le_pow_right₀ (by linarith) (by norm_num)`. Establish `h4 : 2 * (D.R.k : ℝ) ≤ (D.R.r : ℝ) ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨kaS_pos_of_hyp hH, fun τ lam' hd _ => ?_⟩` and prove the remaining obligations. Use `⟨Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L - 2 * (Cn * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3), ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Establish `h1 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ≤ |lamD D τ a - lamD D τ b|` using `Formalism.MainNotions.BridgeLemma.szh_gap hH τ a b hab`. Establish `ha : |lam' a - lamD D τ a| ≤ l1dist lam' (lamD D τ)` using `Finset.single_le_sum (f := fun i => |lam' i - lamD D τ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ a)`.

Establish `hb : |lam' b - lamD D τ b| ≤ l1dist lam' (lamD D τ)` using `Finset.single_le_sum (f := fun i => |lam' i - lamD D τ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ b)`. Establish `t1` using `abs_sub_le (lamD D τ a) (lam' a) (lamD D τ b)`. Establish `t2` using `abs_sub_le (lam' a) (lam' b) (lamD D τ b)`. Rewrite `t1` using `[abs_sub_comm (lamD D τ a) (lam' a)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `gapOK_mono (gap_ok_explicit D.R.k D.R.rS (by omega)) ?_` and prove the remaining obligations. Establish `hH0` using `explicit_gap_le_polynomial D.R.k D.R.rS (by omega)`. Rewrite `hH0` using `[Formalism.MainNotions.S.dimS_eq]`. Establish `hCX : (1000 + |Cn|) * ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5) ≤ Cl * large₂.sc.L * ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5)` using `mul_le_mul_of_nonneg_right hL hX0`. Establish `hCn : Cn * (2 * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3) ≤ |Cn| * ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5)` using `(mul_le_mul_of_nonneg_right (le_abs_self Cn) (by positivity)).trans (mul_le_mul_of_nonneg_left hX2 (abs_nonneg Cn))`.

Establish `hGX : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = Cl * large₂.sc.L * ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5)` using `by ring`. Use polynomial arithmetic with `[hH0, hX8, hCX, hCn, hGX]`.
-/
theorem paramTieG_of {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (Cn : ℝ) (hL : 1000 + |Cn| ≤ Cl * large₂.sc.L) : ParamTieG D Cn := by
  have hmf : D.R.m ^ 4 ≤ D.R.f := hH.2.2.1
  have hfk : D.R.f ≤ D.R.k := hH.2.2.2.1
  have hCl : 0 < Cl := hH.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hrk : D.R.k + 1 ≤ D.R.r := by
    show D.R.k + 1 ≤ D.R.k + D.R.m - 1
    omega
  have hK : (3 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk3
  have hM : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm2
  have hMF : (D.R.m : ℝ) ^ 4 ≤ (D.R.f : ℝ) := by exact_mod_cast hmf
  have hRK : (D.R.k : ℝ) + 1 ≤ (D.R.r : ℝ) := by exact_mod_cast hrk
  have hR1 : 1 ≤ (D.R.r : ℝ) := by linarith
  have hF1 : 1 ≤ (D.R.f : ℝ) := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 4 := one_le_pow₀ (by linarith)
    linarith
  have hX0 : 0 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 := by positivity
  have hX8 : (D.R.r : ℝ) ^ 8 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 := by
    calc (D.R.r : ℝ) ^ 8 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hR1 (by norm_num)
      _ = (D.R.r : ℝ) ^ 19 * 1 := (mul_one _).symm
      _ ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 := by gcongr; exact one_le_pow₀ hF1
  have hX2 : 2 * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 := by
    have h1 : (D.R.r : ℝ) ^ 2 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hR1 (by norm_num)
    have h2 : (D.R.f : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
      calc (D.R.f : ℝ) = (D.R.f : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_right₀ hF1 (by norm_num)
    have h3 : (D.R.m : ℝ) ^ 3 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have h4 : 2 * (D.R.k : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by nlinarith
    calc 2 * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 2 * (D.R.f : ℝ) :=
          mul_le_mul h4 (h3.trans hMF) (by positivity) (by positivity)
      _ ≤ (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 := mul_le_mul h1 h2 (by linarith) (by positivity)
  refine ⟨kaS_pos_of_hyp hH, fun τ lam' hd _ => ?_⟩
  refine ⟨Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L - 2 * (Cn * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3), ?_, ?_⟩
  · intro a b hab
    have h1 : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ≤ |lamD D τ a - lamD D τ b| :=
      Formalism.MainNotions.BridgeLemma.szh_gap hH τ a b hab
    have ha : |lam' a - lamD D τ a| ≤ l1dist lam' (lamD D τ) :=
      Finset.single_le_sum (f := fun i => |lam' i - lamD D τ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ a)
    have hb : |lam' b - lamD D τ b| ≤ l1dist lam' (lamD D τ) :=
      Finset.single_le_sum (f := fun i => |lam' i - lamD D τ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ b)
    have t1 := abs_sub_le (lamD D τ a) (lam' a) (lamD D τ b)
    have t2 := abs_sub_le (lam' a) (lam' b) (lamD D τ b)
    rw [abs_sub_comm (lamD D τ a) (lam' a)] at t1
    linarith
  · refine gapOK_mono (gap_ok_explicit D.R.k D.R.rS (by omega)) ?_
    have hH0 := explicit_gap_le_polynomial D.R.k D.R.rS (by omega)
    rw [Formalism.MainNotions.S.dimS_eq] at hH0
    have hCX : (1000 + |Cn|) * ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5) ≤ Cl * large₂.sc.L * ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5) := mul_le_mul_of_nonneg_right hL hX0
    have hCn : Cn * (2 * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3) ≤ |Cn| * ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5) :=
      (mul_le_mul_of_nonneg_right (le_abs_self Cn) (by positivity)).trans
        (mul_le_mul_of_nonneg_left hX2 (abs_nonneg Cn))
    have hGX : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = Cl * large₂.sc.L * ((D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5) := by ring
    nlinarith [hH0, hX8, hCX, hCn, hGX]

/- English proof (translation)
Introduce `Cn`. Take `⟨x0, -, hx0⟩` from `Formalism.MainNotions.BridgeLemma.ev_L (Fm := Fm) ((1000 + |Cn|) / Formalism.MainNotions.S.sCl Fm)`. Use `⟨x0, fun x hx i hH => ?_⟩` and prove the remaining obligations. Establish `hCl : 0 < Formalism.MainNotions.S.sCl Fm` using `hH.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2`. Use `paramTieG_of hH.1 Cn ?_` and prove the remaining obligations.

Establish `h` using `hx0 x hx i`. Rewrite `h` using `[div_le_iff₀ hCl]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem parameter_gap_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ) :
    ParamTieGF Fm Cg cb Cu cT CT C0 := by
  intro Cn
  obtain ⟨x0, -, hx0⟩ := Formalism.MainNotions.BridgeLemma.ev_L (Fm := Fm) ((1000 + |Cn|) / Formalism.MainNotions.S.sCl Fm)
  refine ⟨x0, fun x hx i hH => ?_⟩
  have hCl : 0 < Formalism.MainNotions.S.sCl Fm := hH.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine paramTieG_of hH.1 Cn ?_
  have h := hx0 x hx i
  rw [div_le_iff₀ hCl] at h
  linarith

end Formalism.L2.S.Pv.Mom
