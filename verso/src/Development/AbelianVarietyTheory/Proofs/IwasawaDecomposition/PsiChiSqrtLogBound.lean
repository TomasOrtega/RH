import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Psi0TruncatedExplicitFormulaStatement
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.GoodLarge

/- English proof (translation)
Rewrite using `[← MulChar.star_eq_inv]`. Use extensionality with `a`. Rewrite using `[MulChar.star_apply]`. Conclude with `Complex.conj_eq_iff_im.2 (h _)`.
-/
theorem inv_eq_self {q : ℕ} (χ : DirichletCharacter ℂ q) (h : GlobalTheoryTheory.IsRealChar χ) : χ⁻¹ = χ := by
  rw [← MulChar.star_eq_inv]
  ext a
  rw [MulChar.star_apply]
  exact Complex.conj_eq_iff_im.2 (h _)

/- English proof (translation)
Take `⟨h0, h1, hT, hL⟩` from `hρ`. Establish `h2` using `((zeros_symm_one_sub q χ hg.1 ρ h0 h1).1).1 hL`. Rewrite `h2` using `[inv_eq_self χ hg.2.1]`. Establish `h3 : 1 / 400 ≤ ρ.re`. Assume the negation of the conclusion as `hc`.

Use `hg.2.2.2 (1 - ρ) ?_ ?_ h2` and prove the remaining obligations. Simplify using `only [Complex.sub_re, Complex.one_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]`. Rewrite `hT` using `[sub_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : 1 / 400 ≤ ‖ρ‖` using `h3.trans (Complex.re_le_norm ρ)`. Rewrite using `[div_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem inv_norm_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hQ : 1 ≤ Q)
    (hg : GlobalTheoryTheory.GoodFor Q χ) {ρ : ℂ} (hρ : ρ ∈ zerosIn χ 0 1) : 1 / ‖ρ‖ ≤ 400 := by
  obtain ⟨h0, h1, hT, hL⟩ := hρ
  have h2 := ((zeros_symm_one_sub q χ hg.1 ρ h0 h1).1).1 hL
  rw [inv_eq_self χ hg.2.1] at h2
  have h3 : 1 / 400 ≤ ρ.re := by
    by_contra hc
    refine hg.2.2.2 (1 - ρ) ?_ ?_ h2
    · simp only [Complex.sub_re, Complex.one_re]; linarith
    · simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      rw [sub_zero] at hT; linarith
  have h4 : 1 / 400 ≤ ‖ρ‖ := h3.trans (Complex.re_le_norm ρ)
  rw [div_le_iff₀ (by linarith)]
  linarith

/- English proof (translation)
Establish `hf` using `(ZeroWindow.finite_and_one_le_zmult q χ 0 1).1`. Rewrite using `[zsumR_eq_sum_toFinset χ 0 1 _ hf, zsumR_eq_sum_toFinset χ 0 1 _ hf, Finset.mul_sum]`. Use `Finset.sum_le_sum fun ρ hρ => ?_` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (inv_norm_le hQ hg (by simpa using hρ)) (Nat.cast_nonneg (α := ℝ) (zmult χ ρ))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem zsumR_inv_norm_one_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hQ : 1 ≤ Q)
    (hg : GlobalTheoryTheory.GoodFor Q χ) :
    zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 400 * zsumR χ 0 1 (fun _ => 1) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  rw [zsumR_eq_sum_toFinset χ 0 1 _ hf, zsumR_eq_sum_toFinset χ 0 1 _ hf, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have := mul_le_mul_of_nonneg_left (inv_norm_le hQ hg (by simpa using hρ))
    (Nat.cast_nonneg (α := ℝ) (zmult χ ρ))
  linarith

/- English proof (translation)
Establish `hf` using `(ZeroWindow.finite_and_one_le_zmult q χ 0 T).1`. Establish `hf1` using `(ZeroWindow.finite_and_one_le_zmult q χ 0 1).1`. Establish `h1` using `sum_indicator_le_zsumR χ 0 1 hf.toFinset hf1`. Rewrite using `[zsumR_eq_sum_toFinset χ 0 T _ hf, zsumR_eq_sum_toFinset χ 0 T _ hf]`. Use `le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) le_rfl)` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_le_sum fun ρ hρ => ?_` and prove the remaining obligations. Establish `hρ' : ρ ∈ zerosIn χ 0 T` using `by simpa using hρ`. Establish `hm : (0 : ℝ) ≤ zmult χ ρ` using `Nat.cast_nonneg _`. Distinguish the cases in `h : 1 < |ρ.im|`.

Apply the tactic sequence `rw [if_pos h] split_ifs <;> linarith`. Establish `h2 : ρ ∈ zerosIn χ 0 1` using `⟨hρ'.1, hρ'.2.1, by rw [sub_zero]; linarith, hρ'.2.2.2⟩`. Rewrite using `[if_neg h, if_pos h2]`. Use `mul_le_mul_of_nonneg_left (inv_norm_le hQ hg h2) hm` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem zsumR_inv_norm_le {Q : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hQ : 1 ≤ Q)
    (hg : GlobalTheoryTheory.GoodFor Q χ) (T : ℝ) :
    zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) ≤ 400 * zsumR χ 0 1 (fun _ => 1) +
      zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) := by
  classical
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  have hf1 := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have h1 := sum_indicator_le_zsumR χ 0 1 hf.toFinset hf1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hf, zsumR_eq_sum_toFinset χ 0 T _ hf]
  refine le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) le_rfl)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hρ' : ρ ∈ zerosIn χ 0 T := by simpa using hρ
  have hm : (0 : ℝ) ≤ zmult χ ρ := Nat.cast_nonneg _
  by_cases h : 1 < |ρ.im|
  · rw [if_pos h]
    split_ifs <;> linarith
  · have h2 : ρ ∈ zerosIn χ 0 1 := ⟨hρ'.1, hρ'.2.1, by rw [sub_zero]; linarith, hρ'.2.2.2⟩
    rw [if_neg h, if_pos h2]
    have := mul_le_mul_of_nonneg_left (inv_norm_le hQ hg h2) hm
    linarith

/- English proof (translation)
Establish `hf` using `(ZeroWindow.finite_and_one_le_zmult q χ 0 T).1`. Rewrite using `[zsumR_eq_sum_toFinset χ 0 T _ hf, zsum, finsum_mem_eq_finite_toFinset_sum _ hf, Finset.mul_sum]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_div, Complex.norm_natCast, mul_left_comm, mul_one_div]`. Conclude with `mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (h ρ (by simpa using hρ)) (norm_nonneg _)) (Nat.cast_nonneg _)`.
-/
theorem norm_zsum_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u T M : ℝ)
    (h : ∀ ρ ∈ zerosIn χ 0 T, ‖(u : ℂ) ^ ρ‖ ≤ M) :
    ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ M * zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hf, zsum, finsum_mem_eq_finite_toFinset_sum _ hf, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  rw [norm_mul, norm_div, Complex.norm_natCast, mul_left_comm, mul_one_div]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (h ρ (by simpa using hρ)) (norm_nonneg _)) (Nat.cast_nonneg _)

/- English proof (translation)
Take `⟨c, hc, H⟩` from `hZ`. Use `⟨min (c / 4) (1 / 400), by positivity, (min_le_right _ _).trans (by norm_num), ?_⟩` and prove the remaining obligations. Introduce `Q q _ χ hQ hχ hg s hs hqs ρ ⟨h0, h1, hT, hL⟩`. Rewrite `hT` using `[sub_zero]`. Establish `hs0 : 0 < s` using `by linarith`.

Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)`. Distinguish the cases in `hR : Formalism.ZeroFreeDirichlet.InRegion c q ρ`. Establish `him` using `(H q χ ρ hR ⟨Or.inl hχ, hL⟩).2.2.1`. Establish `h2 : ρ.re ≤ 1 - 1 / 400`. Assume the negation of the conclusion as `hn`.

Conclude with `hg.2.2.2 ρ (not_le.1 hn) (by rw [him, abs_zero]; exact hQ.le) hL`. Establish `h3 : min (c / 4) (1 / 400) / s ≤ 1 / 400` using `(div_le_self (by positivity) hs).trans (min_le_right _ _)`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `Formalism.ZeroFreeDirichlet.InRegion at hR`. Establish `ha : 0 ≤ |ρ.im|` using `abs_nonneg _`.

Establish `hLpos : 0 < Real.log (q * (|ρ.im| + 2))` using `Real.log_pos (by nlinarith)`. Establish `hL4 : Real.log (q * (|ρ.im| + 2)) ≤ 4 * s`. Rewrite using `[Real.log_mul (by positivity) (by positivity)]`. Establish `h1 : Real.log (|ρ.im| + 2) ≤ s + 2`. Rewrite using `[Real.log_le_iff_le_exp (by positivity), Real.exp_add]`.

Establish `e1 : 1 ≤ Real.exp s` using `Real.one_le_exp hs0.le`. Establish `e2 : 3 ≤ Real.exp 2`. Use `Real.add_one_le_exp 2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : c / (4 * s) ≤ c / Real.log (q * (|ρ.im| + 2))` using `div_le_div_of_nonneg_left hc.le hLpos hL4`. Establish `h3 : min (c / 4) (1 / 400) / s ≤ c / (4 * s)`. Rewrite using `[← div_div]`. Conclude with `div_le_div_of_nonneg_right (min_le_left _ _) hs0.le`.

Combine the linear relations using `[not_le.1 hR]`.
-/
theorem re_le (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
    ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 0 < Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ →
      ∀ s : ℝ, 1 ≤ s → Real.log q ≤ s → ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ρ.re ≤ 1 - c / s := by
  obtain ⟨c, hc, H⟩ := hZ
  refine ⟨min (c / 4) (1 / 400), by positivity, (min_le_right _ _).trans (by norm_num), ?_⟩
  intro Q q _ χ hQ hχ hg s hs hqs ρ ⟨h0, h1, hT, hL⟩
  rw [sub_zero] at hT
  have hs0 : 0 < s := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  by_cases hR : Formalism.ZeroFreeDirichlet.InRegion c q ρ
  · have him := (H q χ ρ hR ⟨Or.inl hχ, hL⟩).2.2.1
    have h2 : ρ.re ≤ 1 - 1 / 400 := by
      by_contra hn
      exact hg.2.2.2 ρ (not_le.1 hn) (by rw [him, abs_zero]; exact hQ.le) hL
    have h3 : min (c / 4) (1 / 400) / s ≤ 1 / 400 :=
      (div_le_self (by positivity) hs).trans (min_le_right _ _)
    linarith
  · unfold Formalism.ZeroFreeDirichlet.InRegion at hR
    have ha : 0 ≤ |ρ.im| := abs_nonneg _
    have hLpos : 0 < Real.log (q * (|ρ.im| + 2)) := Real.log_pos (by nlinarith)
    have hL4 : Real.log (q * (|ρ.im| + 2)) ≤ 4 * s := by
      rw [Real.log_mul (by positivity) (by positivity)]
      have h1 : Real.log (|ρ.im| + 2) ≤ s + 2 := by
        rw [Real.log_le_iff_le_exp (by positivity), Real.exp_add]
        have e1 : 1 ≤ Real.exp s := Real.one_le_exp hs0.le
        have e2 : 3 ≤ Real.exp 2 := by
          have := Real.add_one_le_exp 2
          linarith
        nlinarith
      linarith
    have h2 : c / (4 * s) ≤ c / Real.log (q * (|ρ.im| + 2)) :=
      div_le_div_of_nonneg_left hc.le hLpos hL4
    have h3 : min (c / 4) (1 / 400) / s ≤ c / (4 * s) := by
      rw [← div_div]
      exact div_le_div_of_nonneg_right (min_le_left _ _) hs0.le
    linarith [not_le.1 hR]

/- English proof (translation)
Introduce `h1 h2 h3 h4 h5`. Take `⟨A₀, hA₀⟩` from `GlobalTheory.T.norm_psi0_add_zsum_le_of_isPrimitive h5 h1 h2`. Take `⟨B₀, hB₀⟩` from `zsumR_recip_le h3`. Take `⟨c, hc, hc1, hre⟩` from `re_le h4`. Use `set A := max A₀ 0 with hA`.

Use `set B := max B₀ 0 with hB`. Establish `hA0 : 0 ≤ A` using `le_max_right _ _`. Establish `hB0 : 0 ≤ B` using `le_max_right _ _`. Use `⟨(1 + 1204 * B + A * (11 + 1200 * B)) * (24 / (c / 2) ^ 4), c / 2, by positivity, by positivity, ?_⟩` and prove the remaining obligations. Introduce `Q q _ χ hQ hχ hg u hu`.

Establish `hQ0 : 0 < Q` using `by linarith`. Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)`. Establish `hlQ : 1 ≤ Real.log Q`. Rewrite using `[Real.le_log_iff_exp_le hQ0]`. Use `Real.exp_one_lt_d9` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu0 : 0 < u` using `lt_of_lt_of_le (Real.exp_pos _) hu`. Establish `hlu : Real.log Q ^ 2 ≤ Real.log u` using `(Real.le_log_iff_exp_le hu0).2 hu`. Establish `hlu0 : 0 ≤ Real.log u` using `le_trans (sq_nonneg _) hlu`. Use `set s := Real.sqrt (Real.log u) with hs`.

Establish `hss : s ^ 2 = Real.log u` using `Real.sq_sqrt hlu0`. Establish `hQs : Real.log Q ≤ s` using `Real.le_sqrt_of_sq_le hlu`. Establish `hs1 : 1 ≤ s` using `hlQ.trans hQs`. Establish `hs0 : 0 < s` using `by linarith`. Establish `hqs : Real.log q ≤ s` using `(Real.log_le_log (by linarith) hg.2.2.1).trans hQs`.

Establish `hq0 : 0 ≤ Real.log q` using `Real.log_nonneg hq`. Establish `hT2 : 2 ≤ Real.exp s` using `by linarith [Real.add_one_le_exp s]`. Establish `hs2 : s ≤ s ^ 2` using `by nlinarith`. Establish `hs4 : s ^ 2 ≤ s ^ 4` using `pow_le_pow_right₀ hs1 (by norm_num)`. Establish `hTu : Real.exp s ≤ u`.

Rewrite using `[← Real.le_log_iff_exp_le hu0, ← hss]`. Conclude with `hs2`. Use `set M := u * Real.exp (-c * s) with hM`. Establish `hM' : u / Real.exp s ≤ M`. Rewrite using `[div_eq_mul_inv, ← Real.exp_neg]`.

Conclude with `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hu0.le`. Establish `hM1 : 1 ≤ M` using `le_trans ((one_le_div (Real.exp_pos _)).2 hTu) hM'`. Establish `hMz : ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ‖(u : ℂ) ^ ρ‖ ≤ M`. Introduce `ρ hρ`. Establish `hre'` using `hre Q q χ hQ0 hχ hg s hs1 hqs ρ hρ`.

Rewrite using `[Complex.norm_cpow_eq_rpow_re_of_pos hu0, Real.rpow_def_of_pos hu0]`. Establish `e : M = Real.exp (Real.log u * (1 - c / s))`. Rewrite using `[hM]`. Use `conv_lhs => rw [← Real.exp_log hu0]`. Rewrite using `[← Real.exp_add, ← hss]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hre' hlu0)`.

Take `⟨hb1, hb2⟩` from `hB₀ q χ hg.1 (Real.exp s) hT2`. Establish `hl1 : Real.log (q * Real.exp s) ^ 2 ≤ 4 * s ^ 4`. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_exp]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hl2 : Real.log (3 * q) ≤ 3 * s ^ 4`.

Rewrite using `[Real.log_mul (by positivity) (by positivity)]`. Use `Real.log_le_sub_one_of_pos (x := 3) (by norm_num)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl2' : 0 ≤ Real.log (3 * q)` using `Real.log_nonneg (by linarith)`. Establish `hc1' : zsumR χ 0 (Real.exp s) (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) ≤ B * (4 * s ^ 4)` using `hb1.trans (mul_le_mul (le_max_left _ _) hl1 (sq_nonneg _) hB0)`.

Establish `hc2 : zsumR χ 0 1 (fun _ => 1) ≤ B * (3 * s ^ 4)` using `hb2.trans (mul_le_mul (le_max_left _ _) hl2 hl2' hB0)`. Establish `hS1 : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 1200 * B * s ^ 4`. Use `zsumR_inv_norm_one_le (by linarith) hg` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hS0 : 0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)`.

Rewrite using `[zsumR_eq_sum_toFinset χ 0 1 _ (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1]`. Conclude with `Finset.sum_nonneg fun ρ _ => by positivity`. Establish `hST : zsumR χ 0 (Real.exp s) (fun ρ => 1 / ‖ρ‖) ≤ 1204 * B * s ^ 4`. Use `zsumR_inv_norm_le (by linarith) hg (Real.exp s)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hZ : ‖zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ M * (1204 * B * s ^ 4)` using `(norm_zsum_le χ u _ M hMz).trans (mul_le_mul_of_nonneg_left hST (by linarith))`. Establish `hE` using `hA₀ q χ hg.1 u (Real.exp s) hT2 hTu`. Establish `hp : GlobalTheoryTheory.psi0 χ u = psiChi χ u`. Rewrite using `[GlobalTheoryTheory.psi0, if_neg hχ, sub_zero, psiChi]`. Rewrite `hE` using `[hp]`.

Establish `hl3 : Real.log (q * u * Real.exp s) ^ 2 ≤ 9 * s ^ 4`. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp, ← hss]`. Combine the equalities or inequalities in the displayed calculation. Establish `hl4 : Real.log (q * u) ≤ 2 * s ^ 4`. Rewrite using `[Real.log_mul (by positivity) (by positivity), ← hss]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl4' : 0 ≤ Real.log (q * u)`. Rewrite using `[Real.log_mul (by positivity) (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `he1 : u * Real.log (q * u * Real.exp s) ^ 2 / Real.exp s ≤ M * (9 * s ^ 4)`.

Rewrite using `[mul_div_right_comm]`. Conclude with `mul_le_mul hM' hl3 (sq_nonneg _) (by linarith)`. Establish `he2 : 2 * s ^ 4 + 1200 * B * s ^ 4 ≤ M * (2 * s ^ 4 + 1200 * B * s ^ 4)` using `le_mul_of_one_le_left (by positivity) hM1`. Establish `hE' : ‖psiChi χ u + zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ A * (M * (9 * s ^ 4) + M * (2 * s ^ 4 + 1200 * B * s ^ 4))` using `hE.trans (mul_le_mul (le_max_left _ _) (by linarith) (add_nonneg (add_nonneg (by positivity) hl4') hS0) hA0)`. Establish `hfin : ‖psiChi χ u‖ ≤ (1 + 1204 * B + A * (11 + 1200 * B)) * (M * s ^ 4)`.

Establish `h` using `norm_sub_le (psiChi χ u + zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ)) (zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))`. Rewrite `h` using `[add_sub_cancel_right]`. Establish `: 0 ≤ M * s ^ 4` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsq : s ^ 4 ≤ 24 / (c / 2) ^ 4 * Real.exp (c / 2 * s)`.

Establish `h` using `Real.pow_div_factorial_le_exp (c / 2 * s) (by positivity) 4`. Rewrite using `[div_mul_eq_mul_div, le_div_iff₀ (by positivity)]`. Rewrite `h` using `[mul_pow]`. Evaluate the numerical expressions using `[Nat.factorial] at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `hfin.trans ?_` and prove the remaining obligations. Establish `e : Real.exp (-(c / 2) * s) = Real.exp (-c * s) * Real.exp (c / 2 * s)`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem psi_le_of_large : GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.ExplZeta → ∃ C₁ c₁ : ℝ, 0 < C₁ ∧ 0 < c₁ ∧ ∀ (Q : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 3 ≤ Q → χ ≠ 1 → GlobalTheoryTheory.GoodFor Q χ → ∀ u : ℝ, Real.exp (Real.log Q ^ 2) ≤ u → ‖psiChi χ u‖ ≤ C₁ * u * Real.exp (-c₁ * Real.sqrt (Real.log u)) := by
  intro h1 h2 h3 h4 h5
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.T.norm_psi0_add_zsum_le_of_isPrimitive h5 h1 h2
  obtain ⟨B₀, hB₀⟩ := zsumR_recip_le h3
  obtain ⟨c, hc, hc1, hre⟩ := re_le h4
  set A := max A₀ 0 with hA
  set B := max B₀ 0 with hB
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  refine ⟨(1 + 1204 * B + A * (11 + 1200 * B)) * (24 / (c / 2) ^ 4), c / 2, by positivity, by positivity, ?_⟩
  intro Q q _ χ hQ hχ hg u hu
  have hQ0 : 0 < Q := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have hlQ : 1 ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le hQ0]
    have := Real.exp_one_lt_d9
    linarith
  have hu0 : 0 < u := lt_of_lt_of_le (Real.exp_pos _) hu
  have hlu : Real.log Q ^ 2 ≤ Real.log u := (Real.le_log_iff_exp_le hu0).2 hu
  have hlu0 : 0 ≤ Real.log u := le_trans (sq_nonneg _) hlu
  set s := Real.sqrt (Real.log u) with hs
  have hss : s ^ 2 = Real.log u := Real.sq_sqrt hlu0
  have hQs : Real.log Q ≤ s := Real.le_sqrt_of_sq_le hlu
  have hs1 : 1 ≤ s := hlQ.trans hQs
  have hs0 : 0 < s := by linarith
  have hqs : Real.log q ≤ s := (Real.log_le_log (by linarith) hg.2.2.1).trans hQs
  have hq0 : 0 ≤ Real.log q := Real.log_nonneg hq
  have hT2 : 2 ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  have hs2 : s ≤ s ^ 2 := by nlinarith
  have hs4 : s ^ 2 ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  have hTu : Real.exp s ≤ u := by
    rw [← Real.le_log_iff_exp_le hu0, ← hss]; exact hs2
  set M := u * Real.exp (-c * s) with hM
  have hM' : u / Real.exp s ≤ M := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hu0.le
  have hM1 : 1 ≤ M := le_trans ((one_le_div (Real.exp_pos _)).2 hTu) hM'
  have hMz : ∀ ρ ∈ zerosIn χ 0 (Real.exp s), ‖(u : ℂ) ^ ρ‖ ≤ M := by
    intro ρ hρ
    have hre' := hre Q q χ hQ0 hχ hg s hs1 hqs ρ hρ
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, Real.rpow_def_of_pos hu0]
    have e : M = Real.exp (Real.log u * (1 - c / s)) := by
      rw [hM]
      conv_lhs => rw [← Real.exp_log hu0]
      rw [← Real.exp_add, ← hss]
      congr 1
      field_simp
      ring
    rw [e]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hre' hlu0)
  obtain ⟨hb1, hb2⟩ := hB₀ q χ hg.1 (Real.exp s) hT2
  have hl1 : Real.log (q * Real.exp s) ^ 2 ≤ 4 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp]
    nlinarith
  have hl2 : Real.log (3 * q) ≤ 3 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
    linarith
  have hl2' : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have hc1' : zsumR χ 0 (Real.exp s) (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) ≤ B * (4 * s ^ 4) :=
    hb1.trans (mul_le_mul (le_max_left _ _) hl1 (sq_nonneg _) hB0)
  have hc2 : zsumR χ 0 1 (fun _ => 1) ≤ B * (3 * s ^ 4) :=
    hb2.trans (mul_le_mul (le_max_left _ _) hl2 hl2' hB0)
  have hS1 : zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 1200 * B * s ^ 4 := by
    have := zsumR_inv_norm_one_le (by linarith) hg
    linarith
  have hS0 : 0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
    rw [zsumR_eq_sum_toFinset χ 0 1 _ (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1]
    exact Finset.sum_nonneg fun ρ _ => by positivity
  have hST : zsumR χ 0 (Real.exp s) (fun ρ => 1 / ‖ρ‖) ≤ 1204 * B * s ^ 4 := by
    have := zsumR_inv_norm_le (by linarith) hg (Real.exp s)
    linarith
  have hZ : ‖zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ M * (1204 * B * s ^ 4) :=
    (norm_zsum_le χ u _ M hMz).trans (mul_le_mul_of_nonneg_left hST (by linarith))
  have hE := hA₀ q χ hg.1 u (Real.exp s) hT2 hTu
  have hp : GlobalTheoryTheory.psi0 χ u = psiChi χ u := by
    rw [GlobalTheoryTheory.psi0, if_neg hχ, sub_zero, psiChi]
  rw [hp] at hE
  have hl3 : Real.log (q * u * Real.exp s) ^ 2 ≤ 9 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_exp, ← hss]
    calc _ ≤ (3 * s ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = _ := by ring
  have hl4 : Real.log (q * u) ≤ 2 * s ^ 4 := by
    rw [Real.log_mul (by positivity) (by positivity), ← hss]
    linarith
  have hl4' : 0 ≤ Real.log (q * u) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    linarith
  have he1 : u * Real.log (q * u * Real.exp s) ^ 2 / Real.exp s ≤ M * (9 * s ^ 4) := by
    rw [mul_div_right_comm]
    exact mul_le_mul hM' hl3 (sq_nonneg _) (by linarith)
  have he2 : 2 * s ^ 4 + 1200 * B * s ^ 4 ≤ M * (2 * s ^ 4 + 1200 * B * s ^ 4) :=
    le_mul_of_one_le_left (by positivity) hM1
  have hE' : ‖psiChi χ u + zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤
      A * (M * (9 * s ^ 4) + M * (2 * s ^ 4 + 1200 * B * s ^ 4)) :=
    hE.trans (mul_le_mul (le_max_left _ _) (by linarith)
      (add_nonneg (add_nonneg (by positivity) hl4') hS0) hA0)
  have hfin : ‖psiChi χ u‖ ≤ (1 + 1204 * B + A * (11 + 1200 * B)) * (M * s ^ 4) := by
    have h := norm_sub_le (psiChi χ u + zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))
      (zsum χ 0 (Real.exp s) (fun ρ => (u : ℂ) ^ ρ / ρ))
    rw [add_sub_cancel_right] at h
    have : 0 ≤ M * s ^ 4 := by positivity
    linarith
  have hsq : s ^ 4 ≤ 24 / (c / 2) ^ 4 * Real.exp (c / 2 * s) := by
    have h := Real.pow_div_factorial_le_exp (c / 2 * s) (by positivity) 4
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    rw [mul_pow] at h
    norm_num [Nat.factorial] at h
    linarith
  refine hfin.trans ?_
  have e : Real.exp (-(c / 2) * s) = Real.exp (-c * s) * Real.exp (c / 2 * s) := by
    rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ (1 + 1204 * B + A * (11 + 1200 * B)) * (M * (24 / (c / 2) ^ 4 * Real.exp (c / 2 * s))) := by
        gcongr
    _ = _ := by rw [e, hM]; ring

end GlobalTheory.Mem.An.GoodLarge
