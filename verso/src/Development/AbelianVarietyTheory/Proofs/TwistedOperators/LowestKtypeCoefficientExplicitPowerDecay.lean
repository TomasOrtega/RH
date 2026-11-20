import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.SepReal.PowDec

/- English proof (translation)
Establish `hA` using `Matrix.isHermitian_conjTranspose_mul_self g`. Establish `h1 : hsn g ^ 2 = ∑ j, hA.eigenvalues j`. Establish `e0 : hsn g = Real.sqrt (Formalism.REAL.hs g)` using `rfl`. Rewrite using `[e0, Real.sq_sqrt (by unfold Formalism.REAL.hs; positivity), GlobalTheory.Count.Cartan.hs_eq_trace, hA.trace_eq_sum_eigenvalues]`. Simplify using `[Complex.re_sum]`.

Rewrite using `[h1]`. Establish `hle : ∀ j, hA.eigenvalues j ≤ Real.exp (2 * GlobalTheory.Count.dHS g)`. Introduce `j`. Establish `hx : |Real.log (hA.eigenvalues j) / 2| ≤ GlobalTheory.Count.dHS g`. Unfold `GlobalTheory.Count.dHS`.

Apply `Real.abs_le_sqrt` to reduce the goal to its premises. Conclude with `Finset.single_le_sum (f := fun i => (Real.log (hA.eigenvalues i) / 2) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)`. Break down `le_or_gt (hA.eigenvalues j) 0 with h0 | h0` into its components or cases. Conclude with `h0.trans (Real.exp_pos _).le`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[show 2 * (Real.log (hA.eigenvalues j) / 2) = Real.log (hA.eigenvalues j) by ring, Real.exp_log h0]`. Use `_ ≤ Real.exp (2 * GlobalTheory.Count.dHS g) := by`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Combine the linear relations using `[le_abs_self (Real.log (hA.eigenvalues j) / 2)]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hsn_sq_le {m : ℕ} (g : Mat m) : hsn g ^ 2 ≤ m * Real.exp (2 * GlobalTheory.Count.dHS g) := by
  have hA := Matrix.isHermitian_conjTranspose_mul_self g
  have h1 : hsn g ^ 2 = ∑ j, hA.eigenvalues j := by
    have e0 : hsn g = Real.sqrt (Formalism.REAL.hs g) := rfl
    rw [e0, Real.sq_sqrt (by unfold Formalism.REAL.hs; positivity), GlobalTheory.Count.Cartan.hs_eq_trace,
      hA.trace_eq_sum_eigenvalues]
    simp [Complex.re_sum]
  rw [h1]
  have hle : ∀ j, hA.eigenvalues j ≤ Real.exp (2 * GlobalTheory.Count.dHS g) := by
    intro j
    have hx : |Real.log (hA.eigenvalues j) / 2| ≤ GlobalTheory.Count.dHS g := by
      unfold GlobalTheory.Count.dHS
      apply Real.abs_le_sqrt
      exact Finset.single_le_sum (f := fun i => (Real.log (hA.eigenvalues i) / 2) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    rcases le_or_gt (hA.eigenvalues j) 0 with h0 | h0
    · exact h0.trans (Real.exp_pos _).le
    · calc hA.eigenvalues j = Real.exp (2 * (Real.log (hA.eigenvalues j) / 2)) := by
            rw [show 2 * (Real.log (hA.eigenvalues j) / 2) = Real.log (hA.eigenvalues j) by ring,
              Real.exp_log h0]
        _ ≤ Real.exp (2 * GlobalTheory.Count.dHS g) := by
            apply Real.exp_le_exp.2
            linarith [le_abs_self (Real.log (hA.eigenvalues j) / 2)]
  calc ∑ j, hA.eigenvalues j ≤ ∑ _j : Fin m, Real.exp (2 * GlobalTheory.Count.dHS g) :=
        Finset.sum_le_sum fun j _ => hle j
    _ = m * Real.exp (2 * GlobalTheory.Count.dHS g) := by simp

/- English proof (translation)
Unfold `hsn`. Apply `Real.sqrt_pos.2` to reduce the goal to its premises. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Establish `hsum : ∑ a, ∑ b, ‖g a b‖ ^ 2 = 0` using `le_antisymm hle (by positivity)`.

Establish `hg0 : g = 0`. Use extensionality with `a b`. Rewrite `hsum` using `[Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)]`. Establish `h2` using `hsum a (Finset.mem_univ _)`. Rewrite `h2` using `[Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)]`.

Simplify using `using h2 b (Finset.mem_univ _)`. Establish `hJ : gᴴ * Jm ε * g = Jm ε` using `hg`. Rewrite `hJ` using `[hg0]`. Use `congrFun (congrFun hJ ⟨0, hm⟩) ⟨0, hm⟩` as an intermediate fact. Simplify using `[Jm] at this`.

Apply the tactic sequence `split_ifs at this <;> simp at this`.
-/
theorem hsn_pos {m : ℕ} (hm : 1 ≤ m) {ε : Fin m → Bool} {g : Mat m} (hg : g ∈ UJset ε) : 0 < hsn g := by
  unfold hsn
  apply Real.sqrt_pos.2
  by_contra hle
  push_neg at hle
  have hsum : ∑ a, ∑ b, ‖g a b‖ ^ 2 = 0 := le_antisymm hle (by positivity)
  have hg0 : g = 0 := by
    ext a b
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hsum
    have h2 := hsum a (Finset.mem_univ _)
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at h2
    simpa using h2 b (Finset.mem_univ _)
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  rw [hg0] at hJ
  have := congrFun (congrFun hJ ⟨0, hm⟩) ⟨0, hm⟩
  simp [Jm] at this
  split_ifs at this <;> simp at this

/- English proof (translation)
Establish `hJ : gᴴ * Jm ε * g = Jm ε` using `hg`. Establish `hJc : Jm ε = 1 ∨ Jm ε = -1`. Unfold `GlobalTheory.Count.rkR at hq`. Break down `Nat.min_eq_zero_iff.1 hq with h | h` into its components or cases. Use `right`.

Establish `hf : ∀ a, ε a = false` using `fun a => by`. Assume the negation of the conclusion as `ha`. Establish `: a ∈ univ.filter fun a => ε a = true` using `by simpa using ha`. Rewrite `this` using `[Finset.card_eq_zero.1 h]`. Simplify using `at this`.

Use extensionality with `a b`. Apply the tactic sequence `by_cases hab : a = b <;> simp [Jm, Matrix.diagonal_apply, hab, hf, Matrix.one_apply]`. Use `left`. Establish `hf : ∀ a, ε a = true` using `fun a => by`. Assume the negation of the conclusion as `ha`.

Establish `: a ∈ univ.filter fun a => ε a = false` using `by simpa using ha`. Rewrite `this` using `[Finset.card_eq_zero.1 h]`. Simplify using `at this`. Use extensionality with `a b`. Apply the tactic sequence `by_cases hab : a = b <;> simp [Jm, Matrix.diagonal_apply, hab, hf, Matrix.one_apply]`.

Establish `hu : gᴴ * g = 1`. Break down `hJc with h | h` into its components or cases. Rewrite `hJ` using `[h, Matrix.mul_one]`. Conclude with `hJ`. Rewrite `hJ` using `[h]`.

Establish `: -(gᴴ * g) = -1` using `by simpa [Matrix.mul_neg, Matrix.neg_mul] using hJ`. Conclude with `neg_inj.1 this`. Establish `e0 : hsn g = Real.sqrt (Formalism.REAL.hs g)` using `rfl`. Rewrite using `[e0, Real.sq_sqrt (by unfold Formalism.REAL.hs; positivity), GlobalTheory.Count.Cartan.hs_eq_trace, hu]`. Simplify using the standard rewrite rules.
-/
theorem hsn_sq_definite {m : ℕ} {ε : Fin m → Bool} (hq : GlobalTheory.Count.rkR ε = 0) {g : Mat m} (hg : g ∈ UJset ε) :
    hsn g ^ 2 = m := by
  have hJ : gᴴ * Jm ε * g = Jm ε := hg
  have hJc : Jm ε = 1 ∨ Jm ε = -1 := by
    unfold GlobalTheory.Count.rkR at hq
    rcases Nat.min_eq_zero_iff.1 hq with h | h
    · right
      have hf : ∀ a, ε a = false := fun a => by
        by_contra ha
        have : a ∈ univ.filter fun a => ε a = true := by simpa using ha
        rw [Finset.card_eq_zero.1 h] at this
        simp at this
      ext a b
      by_cases hab : a = b <;> simp [Jm, Matrix.diagonal_apply, hab, hf, Matrix.one_apply]
    · left
      have hf : ∀ a, ε a = true := fun a => by
        by_contra ha
        have : a ∈ univ.filter fun a => ε a = false := by simpa using ha
        rw [Finset.card_eq_zero.1 h] at this
        simp at this
      ext a b
      by_cases hab : a = b <;> simp [Jm, Matrix.diagonal_apply, hab, hf, Matrix.one_apply]
  have hu : gᴴ * g = 1 := by
    rcases hJc with h | h
    · rw [h, Matrix.mul_one] at hJ; exact hJ
    · rw [h] at hJ
      have : -(gᴴ * g) = -1 := by simpa [Matrix.mul_neg, Matrix.neg_mul] using hJ
      exact neg_inj.1 this
  have e0 : hsn g = Real.sqrt (Formalism.REAL.hs g) := rfl
  rw [e0, Real.sq_sqrt (by unfold Formalism.REAL.hs; positivity), GlobalTheory.Count.Cartan.hs_eq_trace, hu]
  simp

end GlobalTheory.SepReal.PowDec

namespace GlobalTheory.SepReal.PowDec

/- English proof (translation)
Unfold `GlobalTheory.Count.rkR`. Conclude with `(min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))`.
-/
theorem rkR_le {m : ℕ} (ε : Fin m → Bool) : GlobalTheory.Count.rkR ε ≤ m := by
  unfold GlobalTheory.Count.rkR
  exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))

/- English proof (translation)
Establish `hm1 : (1 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hq : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ≤ m` using `by exact_mod_cast rkR_le ε`. Establish `h1 : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2)` using `Real.rpow_le_rpow (by positivity) hq (by norm_num)`. Establish `h2 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)`. Rewrite `h2` using `[Real.rpow_two]`.

Establish `h3 : 0 ≤ (m : ℝ)` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0 : ℝ) ≤ 120 * m)]`.
-/
theorem gap_ok {m : ℕ} (hm : 1 ≤ m) (ε : Fin m → Bool) :
    120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1000 * (m : ℝ) ^ 3 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ≤ m := by exact_mod_cast rkR_le ε
  have h1 : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (by positivity) hq (by norm_num)
  have h2 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  rw [Real.rpow_two] at h2
  have h3 : 0 ≤ (m : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity : (0 : ℝ) ≤ 120 * m)]

end GlobalTheory.SepReal.PowDec

namespace GlobalTheory.SepReal

open GlobalTheory.SepReal.PowDec in

/- English proof (translation)
Introduce `m ε lam B hm hlam hgap _ H _ _ π hπ v₀ hv₀ g hg`. Establish `hm1 : (1 : ℝ) ≤ m` using `by exact_mod_cast (by omega : 1 ≤ m)`. Establish `hdec` using `(GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap m ε lam H π hlam hπ (1000 * (m : ℝ) ^ 3) hgap (gap_ok (by omega) ε) g hg v₀ hv₀.2 v₀ hv₀.2).1`. Rewrite `hdec` using `[hv₀.1, mul_one, mul_one]`. Unfold `GlobalTheory.Dec.decHS at hdec`.

Use `set t := GlobalTheory.Count.dHS g with ht`. Use `set q := GlobalTheory.Count.rkR ε with hqdef`. Establish `hx` using `hsn_pos (by omega) hg`. Use `set A : ℝ := 40 * (m : ℝ) ^ 2 with hA`. Establish `hpow : hsn g ^ (-A) = Real.exp (Real.log (hsn g) * (-A))` using `Real.rpow_def_of_pos hx _`.

Rewrite using `[hpow, ← Real.exp_add]`. Use `hdec.trans (Real.exp_le_exp.2 ?_)` and prove the remaining obligations. Establish `hlogm : Real.log m ≤ m` using `(Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)`. Establish `ht0 : 0 ≤ t` using `Real.sqrt_nonneg _`. Establish `hm0 : (0 : ℝ) ≤ m` using `by positivity`.

Break down `Nat.eq_zero_or_pos q with hq | hq` into its components or cases. Establish `hs2` using `hsn_sq_definite hq hg`. Establish `hL : 2 * Real.log (hsn g) = Real.log m`. Rewrite using `[← Real.log_rpow hx, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hs2]`. Establish `hM : min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) = 0`.

Rewrite using `[hq]`. Simplify using the standard rewrite rules. Check the signs of the components of the expression. Rewrite using `[hM]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]`.

Establish `hs2` using `hsn_sq_le g`. Establish `hL : 2 * Real.log (hsn g) ≤ Real.log m + 2 * t`. Establish `h1 : Real.log (hsn g ^ 2) ≤ Real.log (m * Real.exp (2 * t))` using `Real.log_le_log (by positivity) hs2`. Rewrite `h1` using `[Real.log_pow, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]`. Move the coercions through the operations in `at h1`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqr : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hqm : (q : ℝ) ≤ m` using `by exact_mod_cast rkR_le ε`. Establish `hm3 : (3 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hsq : Real.sqrt (2 * (q : ℝ)) ≤ m`.

Rewrite using `[Real.sqrt_le_left (by positivity)]; nlinarith`. Establish `hsq0 : 0 < Real.sqrt (2 * (q : ℝ))` using `Real.sqrt_pos.2 (by positivity)`. Establish `hkey : t - 1 ≤ (m : ℝ) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ)))`. Break down `le_total t 1 with h1 | h1` into its components or cases. Establish `: 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ)))` using `le_min (by positivity) (by positivity)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `a1 : t ≤ (m : ℝ) * t ^ 2` using `by nlinarith`. Establish `a2 : t ≤ (m : ℝ) * (t / Real.sqrt (2 * (q : ℝ)))`. Rewrite using `[mul_div_assoc', le_div_iff₀ hsq0]`. Use the polynomial consequences of the given equalities and inequalities.

Apply the tactic sequence `rcases min_choice (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) with e | e <;> rw [e] <;> linarith`. Establish `hL' : Real.log (hsn g) * A ≤ 20 * (m : ℝ) ^ 3 + 40 * (m : ℝ) ^ 2 * t`. Rewrite using `[hA]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2), mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 20 * (m : ℝ) ^ 2)]`. Establish `hk2` using `mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 125 * (m : ℝ) ^ 2)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem decPow : DecPow := by
  intro m ε lam B hm hlam hgap _ H _ _ π hπ v₀ hv₀ g hg
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have hdec := (GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap m ε lam H π hlam hπ
    (1000 * (m : ℝ) ^ 3) hgap (gap_ok (by omega) ε) g hg v₀ hv₀.2 v₀ hv₀.2).1
  rw [hv₀.1, mul_one, mul_one] at hdec
  unfold GlobalTheory.Dec.decHS at hdec
  set t := GlobalTheory.Count.dHS g with ht
  set q := GlobalTheory.Count.rkR ε with hqdef
  have hx := hsn_pos (by omega) hg
  set A : ℝ := 40 * (m : ℝ) ^ 2 with hA
  have hpow : hsn g ^ (-A) = Real.exp (Real.log (hsn g) * (-A)) := Real.rpow_def_of_pos hx _
  rw [hpow, ← Real.exp_add]
  refine hdec.trans (Real.exp_le_exp.2 ?_)
  have hlogm : Real.log m ≤ m := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) ≤ m := by positivity
  rcases Nat.eq_zero_or_pos q with hq | hq
  ·
    have hs2 := hsn_sq_definite hq hg
    have hL : 2 * Real.log (hsn g) = Real.log m := by
      rw [← Real.log_rpow hx, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hs2]
    have hM : min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) = 0 := by
      rw [hq]; simp; positivity
    rw [hM]
    nlinarith [mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]
  · have hs2 := hsn_sq_le g
    have hL : 2 * Real.log (hsn g) ≤ Real.log m + 2 * t := by
      have h1 : Real.log (hsn g ^ 2) ≤ Real.log (m * Real.exp (2 * t)) := Real.log_le_log (by positivity) hs2
      rw [Real.log_pow, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h1
      push_cast at h1; linarith
    have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqm : (q : ℝ) ≤ m := by exact_mod_cast rkR_le ε
    have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hsq : Real.sqrt (2 * (q : ℝ)) ≤ m := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have hsq0 : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by positivity)

    have hkey : t - 1 ≤ (m : ℝ) * min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := by
      rcases le_total t 1 with h1 | h1
      · have : 0 ≤ min (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) := le_min (by positivity) (by positivity)
        nlinarith
      · have a1 : t ≤ (m : ℝ) * t ^ 2 := by nlinarith
        have a2 : t ≤ (m : ℝ) * (t / Real.sqrt (2 * (q : ℝ))) := by
          rw [mul_div_assoc', le_div_iff₀ hsq0]; nlinarith
        rcases min_choice (t ^ 2) (t / Real.sqrt (2 * (q : ℝ))) with e | e <;> rw [e] <;> linarith
    have hL' : Real.log (hsn g) * A ≤ 20 * (m : ℝ) ^ 3 + 40 * (m : ℝ) ^ 2 * t := by
      rw [hA]
      nlinarith [mul_le_mul_of_nonneg_left hlogm (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2),
        mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 20 * (m : ℝ) ^ 2)]
    have hk2 := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ 125 * (m : ℝ) ^ 2)
    nlinarith

end GlobalTheory.SepReal

end
