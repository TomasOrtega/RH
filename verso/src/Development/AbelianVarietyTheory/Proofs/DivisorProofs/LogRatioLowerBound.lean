import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainVolumeLowerStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions

namespace GlobalTheory.CovTop.MeasLow

/- English proof (translation)
Use `set c : ℚ := ((p : ℚ) + 1)⁻¹ with hc`. Establish `hp1 : (0 : ℚ) < (p : ℚ) + 1` using `by positivity`. Establish `c0 : 0 ≤ c` using `by positivity`. Establish `c1 : c ≤ 1` using `inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg p : (0 : ℚ) ≤ p)])`. Unfold `Formalism.IndefR.Mult.weylDimU at h ⊢`.

Establish `key : ∀ i : Fin p, ∀ j ∈ Finset.univ.filter (fun j : Fin p => i < j), (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) ≠ 0 → c ≤ |(((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))|`. Introduce `i j hj hne`. Establish `hij : i < j` using `(Finset.mem_filter.1 hj).2`. Establish `hd : (0 : ℚ) < ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)`. Establish `: (i : ℕ) < (j : ℕ)` using `hij`.

Establish `: ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ)` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hdle : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≤ (p : ℚ) + 1`. Establish `: (j : ℕ) < p` using `j.2`. Establish `: ((j : ℕ) : ℚ) ≤ p` using `by exact_mod_cast this.le`.

Establish `: (0 : ℚ) ≤ ((i : ℕ) : ℚ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set n : ℤ := lam i - lam j + (j : ℕ) - (i : ℕ) with hn`. Establish `hnum : ((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) = (n : ℚ)`. Rewrite using `[hn]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hne`, the goal using `[hnum]`. Establish `hn0 : n ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Establish `hn1 : (1 : ℚ) ≤ |(n : ℚ)|`. Establish `: (1 : ℤ) ≤ |n|` using `Int.one_le_abs hn0`.

Conclude with `this` after adjusting the coercions. Rewrite using `[abs_div, abs_of_pos hd, hc]`. Rewrite using `[le_div_iff₀ hd]`. Combine the equalities or inequalities in the displayed calculation. Establish `inner : ∀ i : Fin p, c ^ p ≤ |∏ j ∈ Finset.univ.filter (fun j : Fin p => i < j), (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))| ∨ (∏ j ∈ Finset.univ.filter (fun j : Fin p => i < j), (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : …`.

Introduce `i`. Distinguish the cases in `h0 : (∏ j ∈ Finset.univ.filter (fun j : Fin p => i < j), (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) = 0`. Conclude with `Or.inr h0`. Use `left`. Rewrite using `[Finset.abs_prod]`.

Establish `hcard : (Finset.univ.filter (fun j : Fin p => i < j)).card ≤ p`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod (fun _ _ => c0)` to reduce the goal to its premises. Introduce `j hj`.

Conclude with `key i j hj (fun hz => h0 (Finset.prod_eq_zero hj hz))`. Establish `outer : c ^ (p * p) ≤ |∏ i : Fin p, ∏ j ∈ Finset.univ.filter (fun j : Fin p => i < j), (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))|`. Rewrite using `[Finset.abs_prod]`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.prod_le_prod (fun _ _ => pow_nonneg c0 _)` to reduce the goal to its premises.

Introduce `i _`. Break down `inner i with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd (Finset.prod_eq_zero (Finset.mem_univ i) h1) h`. Establish `hpow : c ^ (p * p) * ((p : ℚ) + 1) ^ (p * p) = 1`.

Rewrite using `[← mul_pow, hc, inv_mul_cancel₀ hp1.ne', one_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_le_abs_weylDimU_mul {p : ℕ} (lam : Fin p → ℤ) (h : Formalism.IndefR.Mult.weylDimU lam ≠ 0) :
    1 ≤ |Formalism.IndefR.Mult.weylDimU lam| * ((p : ℚ) + 1) ^ (p * p) := by
  set c : ℚ := ((p : ℚ) + 1)⁻¹ with hc
  have hp1 : (0 : ℚ) < (p : ℚ) + 1 := by positivity
  have c0 : 0 ≤ c := by positivity
  have c1 : c ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg p : (0 : ℚ) ≤ p)])
  unfold Formalism.IndefR.Mult.weylDimU at h ⊢
  have key : ∀ i : Fin p, ∀ j ∈ Finset.univ.filter (fun j : Fin p => i < j),
      (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) ≠ 0 →
      c ≤ |(((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))| := by
    intro i j hj hne
    have hij : i < j := (Finset.mem_filter.1 hj).2
    have hd : (0 : ℚ) < ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) := by
      have : (i : ℕ) < (j : ℕ) := hij
      have : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast this
      linarith
    have hdle : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≤ (p : ℚ) + 1 := by
      have : (j : ℕ) < p := j.2
      have : ((j : ℕ) : ℚ) ≤ p := by exact_mod_cast this.le
      have : (0 : ℚ) ≤ ((i : ℕ) : ℚ) := Nat.cast_nonneg _
      linarith
    set n : ℤ := lam i - lam j + (j : ℕ) - (i : ℕ) with hn
    have hnum : ((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) = (n : ℚ) := by
      rw [hn]; push_cast; ring
    rw [hnum] at hne ⊢
    have hn0 : n ≠ 0 := by
      intro h0; apply hne; rw [h0]; simp
    have hn1 : (1 : ℚ) ≤ |(n : ℚ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      exact_mod_cast this
    rw [abs_div, abs_of_pos hd, hc]
    rw [le_div_iff₀ hd]
    calc ((p : ℚ) + 1)⁻¹ * (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) ≤ ((p : ℚ) + 1)⁻¹ * ((p : ℚ) + 1) :=
          mul_le_mul_of_nonneg_left hdle (by positivity)
      _ = 1 := inv_mul_cancel₀ hp1.ne'
      _ ≤ _ := hn1
  have inner : ∀ i : Fin p, c ^ p ≤ |∏ j ∈ Finset.univ.filter (fun j : Fin p => i < j),
      (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))| ∨
      (∏ j ∈ Finset.univ.filter (fun j : Fin p => i < j),
      (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) = 0 := by
    intro i
    by_cases h0 : (∏ j ∈ Finset.univ.filter (fun j : Fin p => i < j),
      (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))) = 0
    · exact Or.inr h0
    left
    rw [Finset.abs_prod]
    have hcard : (Finset.univ.filter (fun j : Fin p => i < j)).card ≤ p := by
      calc _ ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_filter_le _ _
        _ = p := by simp
    calc c ^ p ≤ c ^ (Finset.univ.filter (fun j : Fin p => i < j)).card := pow_le_pow_of_le_one c0 c1 hcard
      _ = ∏ j ∈ Finset.univ.filter (fun j : Fin p => i < j), c := by rw [Finset.prod_const]
      _ ≤ _ := by
        apply Finset.prod_le_prod (fun _ _ => c0)
        intro j hj
        exact key i j hj (fun hz => h0 (Finset.prod_eq_zero hj hz))
  have outer : c ^ (p * p) ≤ |∏ i : Fin p, ∏ j ∈ Finset.univ.filter (fun j : Fin p => i < j),
      (((lam i - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) / (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))| := by
    rw [Finset.abs_prod]
    calc c ^ (p * p) = ∏ _i : Fin p, c ^ p := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
      _ ≤ _ := by
        apply Finset.prod_le_prod (fun _ _ => pow_nonneg c0 _)
        intro i _
        rcases inner i with h1 | h1
        · exact h1
        · exact absurd (Finset.prod_eq_zero (Finset.mem_univ i) h1) h
  have hpow : c ^ (p * p) * ((p : ℚ) + 1) ^ (p * p) = 1 := by
    rw [← mul_pow, hc, inv_mul_cancel₀ hp1.ne', one_pow]
  calc (1 : ℚ) = c ^ (p * p) * ((p : ℚ) + 1) ^ (p * p) := hpow.symm
    _ ≤ _ := mul_le_mul_of_nonneg_right outer (by positivity)

end GlobalTheory.CovTop.MeasLow

namespace GlobalTheory.CovTop.MeasLow

/- English proof (translation)
Establish `hs : ((Wc D i).sig (TH.tauE D τ)).1 + ((Wc D i).sig (TH.tauE D τ)).2 = D.R.r` using `(Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _).trans (rank_Wc i)`. Use `set p := ((Wc D i).sig (TH.tauE D τ)).1`. Use `set q := ((Wc D i).sig (TH.tauE D τ)).2`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt Formalism.IndefR.Mult.dimK at h ⊢`. Use `set a := Formalism.IndefR.Mult.weylDimU (fun k => NTheta.wtOf D (Wc D i) τ (Sum.inl k))`.

Use `set b := Formalism.IndefR.Mult.weylDimU (fun k => NTheta.wtOf D (Wc D i) τ (Sum.inr k))`. Establish `h' : a * b ≠ 0` using `fun h0 => h (by rw [h0]; simp)`. Establish `ha` using `one_le_abs_weylDimU_mul _ (left_ne_zero_of_mul h')`. Establish `hb` using `one_le_abs_weylDimU_mul _ (right_ne_zero_of_mul h')`. Establish `haR : (1 : ℝ) ≤ |(a : ℝ)| * ((p : ℝ) + 1) ^ (p * p)` using `by exact_mod_cast ha`.

Establish `hbR : (1 : ℝ) ≤ |(b : ℝ)| * ((q : ℝ) + 1) ^ (q * q)` using `by exact_mod_cast hb`. Establish `hpr : (p : ℝ) + 1 ≤ (D.R.r : ℝ) + 1`. Establish `: p ≤ D.R.r` using `by omega`. Establish `: (p : ℝ) ≤ D.R.r` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hqr : (q : ℝ) + 1 ≤ (D.R.r : ℝ) + 1`. Establish `: q ≤ D.R.r` using `by omega`. Establish `: (q : ℝ) ≤ D.R.r` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) + 1` using `by linarith [(Nat.cast_nonneg D.R.r : (0 : ℝ) ≤ D.R.r)]`.

Establish `hexp : p * p + q * q ≤ D.R.r * D.R.r`. Rewrite using `[← hs]`. Use the polynomial consequences of the given equalities and inequalities. Establish `e1 : ((p : ℝ) + 1) ^ (p * p) ≤ ((D.R.r : ℝ) + 1) ^ (p * p)` using `pow_le_pow_left₀ (by positivity) hpr _`. Establish `e2 : ((q : ℝ) + 1) ^ (q * q) ≤ ((D.R.r : ℝ) + 1) ^ (q * q)` using `pow_le_pow_left₀ (by positivity) hqr _`.

Establish `e3 : ((D.R.r : ℝ) + 1) ^ (p * p) * ((D.R.r : ℝ) + 1) ^ (q * q) ≤ ((D.R.r : ℝ) + 1) ^ (D.R.r * D.R.r)`. Rewrite using `[← pow_add]`. Conclude with `pow_le_pow_right₀ hr1 hexp`. Use `push_cast`. Rewrite using `[abs_mul]`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul e1 e2 (by positivity) (by positivity)`. Use `_ ≤ _ := mul_le_mul_of_nonneg_left e3 (by positivity)`.
-/
theorem one_le_abs_dimAt_mul (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (h : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ ≠ 0) :
    1 ≤ |GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ| * ((D.R.r : ℝ) + 1) ^ (D.R.r * D.R.r) := by
  have hs : ((Wc D i).sig (TH.tauE D τ)).1 + ((Wc D i).sig (TH.tauE D τ)).2 = D.R.r :=
    (Formalism.BasicNotions.sig_sum _ (D.sp.W_sig _) _).trans (rank_Wc i)
  set p := ((Wc D i).sig (TH.tauE D τ)).1
  set q := ((Wc D i).sig (TH.tauE D τ)).2
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt Formalism.IndefR.Mult.dimK at h ⊢
  set a := Formalism.IndefR.Mult.weylDimU (fun k => NTheta.wtOf D (Wc D i) τ (Sum.inl k))
  set b := Formalism.IndefR.Mult.weylDimU (fun k => NTheta.wtOf D (Wc D i) τ (Sum.inr k))
  have h' : a * b ≠ 0 := fun h0 => h (by rw [h0]; simp)
  have ha := one_le_abs_weylDimU_mul _ (left_ne_zero_of_mul h')
  have hb := one_le_abs_weylDimU_mul _ (right_ne_zero_of_mul h')
  have haR : (1 : ℝ) ≤ |(a : ℝ)| * ((p : ℝ) + 1) ^ (p * p) := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ |(b : ℝ)| * ((q : ℝ) + 1) ^ (q * q) := by exact_mod_cast hb
  have hpr : (p : ℝ) + 1 ≤ (D.R.r : ℝ) + 1 := by
    have : p ≤ D.R.r := by omega
    have : (p : ℝ) ≤ D.R.r := by exact_mod_cast this
    linarith
  have hqr : (q : ℝ) + 1 ≤ (D.R.r : ℝ) + 1 := by
    have : q ≤ D.R.r := by omega
    have : (q : ℝ) ≤ D.R.r := by exact_mod_cast this
    linarith
  have hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) + 1 := by linarith [(Nat.cast_nonneg D.R.r : (0 : ℝ) ≤ D.R.r)]
  have hexp : p * p + q * q ≤ D.R.r * D.R.r := by
    rw [← hs]; nlinarith
  have e1 : ((p : ℝ) + 1) ^ (p * p) ≤ ((D.R.r : ℝ) + 1) ^ (p * p) := pow_le_pow_left₀ (by positivity) hpr _
  have e2 : ((q : ℝ) + 1) ^ (q * q) ≤ ((D.R.r : ℝ) + 1) ^ (q * q) := pow_le_pow_left₀ (by positivity) hqr _
  have e3 : ((D.R.r : ℝ) + 1) ^ (p * p) * ((D.R.r : ℝ) + 1) ^ (q * q) ≤ ((D.R.r : ℝ) + 1) ^ (D.R.r * D.R.r) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hr1 hexp
  push_cast
  rw [abs_mul]
  calc (1 : ℝ) ≤ (|(a : ℝ)| * ((p : ℝ) + 1) ^ (p * p)) * (|(b : ℝ)| * ((q : ℝ) + 1) ^ (q * q)) := by nlinarith
    _ = |(a : ℝ)| * |(b : ℝ)| * (((p : ℝ) + 1) ^ (p * p) * ((q : ℝ) + 1) ^ (q * q)) := by ring
    _ ≤ |(a : ℝ)| * |(b : ℝ)| * (((D.R.r : ℝ) + 1) ^ (p * p) * ((D.R.r : ℝ) + 1) ^ (q * q)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul e1 e2 (by positivity) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left e3 (by positivity)

/- English proof (translation)
Distinguish the cases in `h0 : (∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) = 0`. Conclude with `Or.inl h0`. Use `right`. Establish `hne : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ ≠ 0` using `fun τ hz => h0 (Finset.prod_eq_zero (Finset.mem_univ τ) hz)`. Use `set R : ℝ := ((D.R.r : ℝ) + 1) ^ (D.R.r * D.R.r) with hR`.

Establish `hR1 : 1 ≤ R` using `one_le_pow₀ (by linarith [(Nat.cast_nonneg D.R.r : (0 : ℝ) ≤ D.R.r)])`. Establish `hprod : 1 ≤ |∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ| * R ^ D.R.f`. Rewrite using `[Finset.abs_prod, ← D.what₂.card_Tau, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpos : 0 < |∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ|` using `abs_pos.2 h0`.

Establish `hl` using `Real.log_le_log one_pos hprod`. Rewrite `hl` using `[Real.log_one, Real.log_mul hpos.ne' (by positivity), Real.log_abs, Real.log_pow, hR, Real.log_pow]`. Move the coercions through the operations in `at hl`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_prod_dimAt (D : D7) (i : Fin D.R.m) :
    (∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) = 0 ∨
      -((D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 1))) ≤ Real.log (∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) := by
  by_cases h0 : (∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) = 0
  · exact Or.inl h0
  right
  have hne : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ ≠ 0 := fun τ hz => h0 (Finset.prod_eq_zero (Finset.mem_univ τ) hz)
  set R : ℝ := ((D.R.r : ℝ) + 1) ^ (D.R.r * D.R.r) with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by linarith [(Nat.cast_nonneg D.R.r : (0 : ℝ) ≤ D.R.r)])
  have hprod : 1 ≤ |∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ| * R ^ D.R.f := by
    rw [Finset.abs_prod, ← D.what₂.card_Tau, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    calc (1 : ℝ) = ∏ _τ : D.what₂.Tau, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun τ _ => one_le_abs_dimAt_mul D i τ (hne τ))
  have hpos : 0 < |∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ| := abs_pos.2 h0
  have hl := Real.log_le_log one_pos hprod
  rw [Real.log_one, Real.log_mul hpos.ne' (by positivity), Real.log_abs, Real.log_pow, hR, Real.log_pow] at hl
  push_cast at hl
  nlinarith
end GlobalTheory.CovTop.MeasLow

namespace GlobalTheory.CovTop.MeasLow

/- English proof (translation)
Rewrite using `[hw.unit]`. Take `⟨-, hL10, hLx, hll⟩` from `hn.big`. Establish `hf8 : (8 : ℝ) ≤ D.R.f` using `by exact_mod_cast hn.f8`. Establish `hfr` using `hn.logfr.1`. Establish `hdisc` using `hn.disc`.

Establish `hA1` using `hn.poly.1`. Establish `hPx` using `hn.poly.2.1`. Establish `hroom` using `hn.room`. Establish `hpp` using `hn.ppLow`. Rewrite `hroom` using `[Real.rpow_one]`.

Establish `hx1 : (1 : ℝ) ≤ L.sc.x` using `by linarith`. Establish `hxA : L.sc.x ≤ L.sc.x ^ A`. Combine the equalities or inequalities in the displayed calculation. Establish `hb1 : (1 : ℝ) ≤ L.sc.b` using `by linarith`. Establish `hm1 : (1 : ℝ) ≤ D.R.m`.

Establish `: 1 ≤ D.R.m` using `Nat.one_le_iff_ne_zero.2 (fun h => (h ▸ i).elim0)`. Conclude with `this` after adjusting the coercions. Establish `hr0 : (0 : ℝ) ≤ D.R.r` using `Nat.cast_nonneg _`. Establish `hrb : (D.R.r : ℝ) ^ 2 ≤ L.sc.b`. Break down `Nat.eq_zero_or_pos D.R.r with h0 | h0` into its components or cases.

Rewrite using `[h0]`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr1 : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast h0`. Establish `hz : (D.R.r : ℝ) ≤ zBase L`.

Unfold `zBase`. Establish `: (1 : ℝ) ≤ (D.R.f : ℝ) * L.sc.L` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hz1 : 1 ≤ zBase L` using `le_trans hr1 hz`. Establish `: zBase L ^ 2 ≤ zBase L ^ 12` using `pow_le_pow_right₀ hz1 (by norm_num)`.

Establish `h2 : (D.R.r : ℝ) ^ 2 ≤ zBase L ^ 2` using `pow_le_pow_left₀ hr0 hz 2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog1 : (D.R.r : ℝ) ^ 2 * Real.log ((D.R.f : ℝ) * D.R.r + 3) ≤ (D.R.r : ℝ) ^ 2 * (L.sc.L + 2)`. Break down `Nat.eq_zero_or_pos D.R.r with h0 | h0` into its components or cases. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Establish `hr1 : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast h0`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Establish `hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r` using `by nlinarith`. Establish `: Real.log ((D.R.f : ℝ) * D.R.r + 3) ≤ Real.log (4 * ((D.R.f : ℝ) * D.R.r))` using `Real.log_le_log (by positivity) (by linarith)`.

Rewrite `this` using `[Real.log_mul (by norm_num) (by positivity)]`. Establish `h4 : Real.log 4 ≤ 2`. Establish `e : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring`. Use `Real.log_two_lt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlog2 : (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 1) ≤ (D.R.r : ℝ) ^ 2 * (L.sc.L + 2)`. Break down `Nat.eq_zero_or_pos D.R.r with h0 | h0` into its components or cases. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Establish `hr1 : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast h0`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Establish `hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r` using `by nlinarith`. Establish `: Real.log ((D.R.r : ℝ) + 1) ≤ Real.log (4 * ((D.R.f : ℝ) * D.R.r))` using `Real.log_le_log (by positivity) (by nlinarith)`.

Rewrite `this` using `[Real.log_mul (by norm_num) (by positivity)]`. Establish `h4 : Real.log 4 ≤ 2`. Establish `e : Real.log 4 = 2 * Real.log 2`. Rewrite using `[show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring`. Use `Real.log_two_lt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hf0 : (0 : ℝ) ≤ D.R.f` using `by linarith`. Establish `hL0 : (0 : ℝ) ≤ L.sc.L` using `by linarith`. Establish `hS : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)| ≤ 6 * ((D.R.f : ℝ) * L.sc.b * L.sc.L)`.

Establish `a1 : (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * Real.log ((D.R.f : ℝ) * D.R.r + 3)) ≤ (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * (L.sc.L + 2))` using `mul_le_mul_of_nonneg_left hlog1 hf0`. Establish `a2 : (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * (L.sc.L + 3)) ≤ (D.R.f : ℝ) * (L.sc.b * (L.sc.L + 3))` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrb (by linarith)) hf0`. Establish `a3 : (D.R.f : ℝ) * L.sc.L ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L`. Use `mul_le_mul_of_nonneg_left hb1 (mul_nonneg hf0 hL0)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `a4 : (D.R.f : ℝ) * L.sc.b * 3 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L`. Apply `mul_le_mul_of_nonneg_left (by linarith) (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hT : (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 1)) ≤ 3 * ((D.R.f : ℝ) * L.sc.b * L.sc.L)`. Establish `a1` using `mul_le_mul_of_nonneg_left hlog2 hf0`.

Establish `a2 : (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * (L.sc.L + 2)) ≤ (D.R.f : ℝ) * (L.sc.b * (L.sc.L + 2))` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrb (by linarith)) hf0`. Establish `a4 : (D.R.f : ℝ) * L.sc.b * 2 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L`. Apply `mul_le_mul_of_nonneg_left (by linarith) (by positivity)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `hU : (D.R.f : ℝ) * L.sc.b * L.sc.L ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x)`.

Establish `h0 : (0 : ℝ) ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L` using `by positivity`. Establish `: (D.R.f : ℝ) * L.sc.b * L.sc.L * 1 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x))` using `mul_le_mul_of_nonneg_left (by nlinarith) h0`. Use the polynomial consequences of the given equalities and inequalities. Establish `hCS` using `mul_le_mul_of_nonneg_left hS hC`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem size_le_unit {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (i : Fin D.R.m) {PP A C : ℝ} (hC : 0 ≤ C) (hn : HostNum D L PP A 1) (hw : WtNum p i PP) :
    C * ((D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)|) +
      (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 1)) ≤ (6 * C + 3) * unitE p := by
  rw [hw.unit]
  obtain ⟨-, hL10, hLx, hll⟩ := hn.big
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hn.f8
  have hfr := hn.logfr.1
  have hdisc := hn.disc
  have hA1 := hn.poly.1
  have hPx := hn.poly.2.1
  have hroom := hn.room
  have hpp := hn.ppLow
  rw [Real.rpow_one] at hroom
  have hx1 : (1 : ℝ) ≤ L.sc.x := by linarith
  have hxA : L.sc.x ≤ L.sc.x ^ A := by
    calc L.sc.x = L.sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ L.sc.x ^ A := Real.rpow_le_rpow_of_exponent_le hx1 hA1
  have hb1 : (1 : ℝ) ≤ L.sc.b := by linarith
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := Nat.one_le_iff_ne_zero.2 (fun h => (h ▸ i).elim0)
    exact_mod_cast this
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _

  have hrb : (D.R.r : ℝ) ^ 2 ≤ L.sc.b := by
    rcases Nat.eq_zero_or_pos D.R.r with h0 | h0
    · rw [h0]; simp; linarith
    · have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast h0
      have hz : (D.R.r : ℝ) ≤ zBase L := by
        unfold zBase
        have : (1 : ℝ) ≤ (D.R.f : ℝ) * L.sc.L := by nlinarith
        nlinarith
      have hz1 : 1 ≤ zBase L := le_trans hr1 hz
      have : zBase L ^ 2 ≤ zBase L ^ 12 := pow_le_pow_right₀ hz1 (by norm_num)
      have h2 : (D.R.r : ℝ) ^ 2 ≤ zBase L ^ 2 := pow_le_pow_left₀ hr0 hz 2
      linarith

  have hlog1 : (D.R.r : ℝ) ^ 2 * Real.log ((D.R.f : ℝ) * D.R.r + 3) ≤ (D.R.r : ℝ) ^ 2 * (L.sc.L + 2) := by
    rcases Nat.eq_zero_or_pos D.R.r with h0 | h0
    · rw [h0]; simp
    · have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast h0
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
      have : Real.log ((D.R.f : ℝ) * D.R.r + 3) ≤ Real.log (4 * ((D.R.f : ℝ) * D.R.r)) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_mul (by norm_num) (by positivity)] at this
      have h4 : Real.log 4 ≤ 2 := by
        have e : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        have := Real.log_two_lt_d9
        linarith
      linarith
  have hlog2 : (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 1) ≤ (D.R.r : ℝ) ^ 2 * (L.sc.L + 2) := by
    rcases Nat.eq_zero_or_pos D.R.r with h0 | h0
    · rw [h0]; simp
    · have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast h0
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hfr1 : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
      have : Real.log ((D.R.r : ℝ) + 1) ≤ Real.log (4 * ((D.R.f : ℝ) * D.R.r)) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_mul (by norm_num) (by positivity)] at this
      have h4 : Real.log 4 ≤ 2 := by
        have e : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
        have := Real.log_two_lt_d9
        linarith
      linarith
  have hf0 : (0 : ℝ) ≤ D.R.f := by linarith
  have hL0 : (0 : ℝ) ≤ L.sc.L := by linarith

  have hS : (D.R.f : ℝ) * (D.R.r : ℝ) ^ 2 * (Real.log ((D.R.f : ℝ) * D.R.r + 3) + 1) + Real.log |(discr D.host.E : ℝ)| ≤
      6 * ((D.R.f : ℝ) * L.sc.b * L.sc.L) := by
    have a1 : (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * Real.log ((D.R.f : ℝ) * D.R.r + 3)) ≤ (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * (L.sc.L + 2)) :=
      mul_le_mul_of_nonneg_left hlog1 hf0
    have a2 : (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * (L.sc.L + 3)) ≤ (D.R.f : ℝ) * (L.sc.b * (L.sc.L + 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrb (by linarith)) hf0
    have a3 : (D.R.f : ℝ) * L.sc.L ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
      have := mul_le_mul_of_nonneg_left hb1 (mul_nonneg hf0 hL0); nlinarith
    have a4 : (D.R.f : ℝ) * L.sc.b * 3 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hT : (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 1)) ≤ 3 * ((D.R.f : ℝ) * L.sc.b * L.sc.L) := by
    have a1 := mul_le_mul_of_nonneg_left hlog2 hf0
    have a2 : (D.R.f : ℝ) * ((D.R.r : ℝ) ^ 2 * (L.sc.L + 2)) ≤ (D.R.f : ℝ) * (L.sc.b * (L.sc.L + 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrb (by linarith)) hf0
    have a4 : (D.R.f : ℝ) * L.sc.b * 2 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by
      apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hU : (D.R.f : ℝ) * L.sc.b * L.sc.L ≤ (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) := by
    have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L := by positivity
    have : (D.R.f : ℝ) * L.sc.b * L.sc.L * 1 ≤ (D.R.f : ℝ) * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) h0
    nlinarith
  have hCS := mul_le_mul_of_nonneg_left hS hC
  nlinarith

/- English proof (translation)
Rewrite using `[hw.unit]`. Take `⟨-, hL10, hLx, hll⟩` from `hn.big`. Establish `hroom` using `hn.room`. Rewrite `hroom` using `[Real.rpow_one]`. Establish `hb : 0 ≤ L.sc.b` using `le_trans (Real.rpow_nonneg (by linarith) _) hroom`.

Establish `: (0 : ℝ) ≤ Real.log (Real.log L.sc.x)` using `by linarith`. Check the signs of the components of the expression.
-/
theorem unit_nonneg {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (i : Fin D.R.m) {PP A : ℝ} (hn : HostNum D L PP A 1) (hw : WtNum p i PP) : 0 ≤ unitE p := by
  rw [hw.unit]
  obtain ⟨-, hL10, hLx, hll⟩ := hn.big
  have hroom := hn.room
  rw [Real.rpow_one] at hroom
  have hb : 0 ≤ L.sc.b := le_trans (Real.rpow_nonneg (by linarith) _) hroom
  have : (0 : ℝ) ≤ Real.log (Real.log L.sc.x) := by linarith
  positivity

/- English proof (translation)
Take `⟨C, hC0, hC⟩` from `GlobalTheory.T.fundamental_domain_volume_lower hP`. Use `Closed.imp (Closed.and (Sizes.hostN 1) WtShape.wtN) ?_` and prove the remaining obligations. Introduce and unpack `eps Fm CH - ⟨⟨C1, -, hE1⟩, ⟨C2, -, hE2⟩⟩`. Use `⟨6 * C + 3, by positivity, ?_⟩` and prove the remaining obligations. Take `⟨x0, hx⟩` from `hE1.and hE2`.

Use `⟨x0, fun x hx' hle ι p hp i => ?_⟩` and prove the remaining obligations. Establish `hn` using `(hx x hx' hle ι p hp).1 i`. Establish `hw` using `(hx x hx' hle ι p hp).2 i`. Establish `hsz` using `size_le_unit p i hC0 hn hw`. Establish `hdim` using `log_prod_dimAt _ i`.

Establish `hm` using `hC _ _ _ _ p.charW.base.lev i p.R.triv _ _ (p.charW.base.models.νW i)`. Establish `hu0 : 0 ≤ unitE p` using `unit_nonneg p i hn hw`. Unfold `ratAt GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio`. Use `set V := ((p.R.toRealDat.νW i) (p.R.toRealDat.fdW i)).toReal with hV`. Use `set Q := ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt (Fm.D x ι) i τ with hQ`.

Establish `hK0 : -((6 * C + 3) * unitE p) ≤ 0` using `by nlinarith`. Distinguish the cases in `hV0 : V = 0`. Rewrite using `[hV0, zero_mul, Real.log_zero]`. Conclude with `hK0`. Distinguish the cases in `hQ0 : Q = 0`.

Rewrite using `[hQ0, mul_zero, Real.log_zero]`. Conclude with `hK0`. Establish `hQl : -((Fm.D x ι).R.f * (((Fm.D x ι).R.r : ℝ) ^ 2 * Real.log (((Fm.D x ι).R.r : ℝ) + 1))) ≤ Real.log Q` using `hdim.resolve_left hQ0`. Establish `htop : (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i) ≠ ⊤`. Introduce `h`.

Apply `hV0` to reduce the goal to its premises. Rewrite using `[hV, h]`. Both sides reduce to the same expression. Establish `hVe : Real.exp (-(C * (((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 * (Real.log (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r + 3) + 1) + Real.log |(discr (Fm.D x ι).host.E : ℝ)|))) ≤ V` using `(ENNReal.ofReal_le_iff_le_toReal htop).1 hm`. Establish `hVpos : 0 < V` using `lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hV0)`.

Establish `hlV` using `Real.log_le_log (Real.exp_pos _) hVe`. Rewrite `hlV` using `[Real.log_exp]`. Rewrite using `[Real.log_mul hV0 hQ0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lower (hP : Hypotheses2) :
    Closed FamHyp fun Fm _ => ∃ K : ℝ, 0 ≤ K ∧ EvTied Fm fun _ _ _ p => ∀ i, -(K * unitE p) ≤ Real.log (ratAt p i) := by
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.fundamental_domain_volume_lower hP
  refine Closed.imp (Closed.and (Sizes.hostN 1) WtShape.wtN) ?_
  rintro eps Fm CH - ⟨⟨C1, -, hE1⟩, ⟨C2, -, hE2⟩⟩
  refine ⟨6 * C + 3, by positivity, ?_⟩
  obtain ⟨x0, hx⟩ := hE1.and hE2
  refine ⟨x0, fun x hx' hle ι p hp i => ?_⟩
  have hn := (hx x hx' hle ι p hp).1 i
  have hw := (hx x hx' hle ι p hp).2 i
  have hsz := size_le_unit p i hC0 hn hw
  have hdim := log_prod_dimAt _ i
  have hm := hC _ _ _ _ p.charW.base.lev i p.R.triv _ _ (p.charW.base.models.νW i)
  have hu0 : 0 ≤ unitE p := unit_nonneg p i hn hw
  unfold ratAt GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio
  set V := ((p.R.toRealDat.νW i) (p.R.toRealDat.fdW i)).toReal with hV
  set Q := ∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt (Fm.D x ι) i τ with hQ
  have hK0 : -((6 * C + 3) * unitE p) ≤ 0 := by nlinarith
  by_cases hV0 : V = 0
  · rw [hV0, zero_mul, Real.log_zero]; exact hK0
  by_cases hQ0 : Q = 0
  · rw [hQ0, mul_zero, Real.log_zero]; exact hK0
  have hQl : -((Fm.D x ι).R.f * (((Fm.D x ι).R.r : ℝ) ^ 2 * Real.log (((Fm.D x ι).R.r : ℝ) + 1))) ≤ Real.log Q :=
    hdim.resolve_left hQ0
  have htop : (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i) ≠ ⊤ := by
    intro h; apply hV0; rw [hV, h]; rfl
  have hVe : Real.exp (-(C * (((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 *
      (Real.log (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r + 3) + 1) + Real.log |(discr (Fm.D x ι).host.E : ℝ)|))) ≤ V :=
    (ENNReal.ofReal_le_iff_le_toReal htop).1 hm
  have hVpos : 0 < V := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hV0)
  have hlV := Real.log_le_log (Real.exp_pos _) hVe
  rw [Real.log_exp] at hlV
  rw [Real.log_mul hV0 hQ0]
  linarith

end GlobalTheory.CovTop.MeasLow

end
