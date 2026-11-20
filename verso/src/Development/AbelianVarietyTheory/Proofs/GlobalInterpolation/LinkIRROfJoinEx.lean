import Mathlib
import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
import Formalism.LocalToGlobal.HilbertRowConditions.AllJoinP
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLabelWeightsOfGreenCuspidalParametrisa

noncomputable section

namespace GlobalTheory.Top.Irr

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.ConcNWeight Formalism.L2.GlobalTheoryTheory.AllJoin

/- English proof (translation)
Introduce `k` and use `⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩`.
-/
theorem tieAdmG_holds (D : D7) : TieAdmG D := fun k =>
  ⟨D.host.g_prime k, D.nd.g_split k, D.ntypes.g_Mray k, D.ntypes.g_cond k⟩

/- English proof (translation)
Take `⟨x0, hx0⟩` from `h`. Establish `hez : 0 < Fm.ez` using `div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)`. Use `linkIRR_of_allRows eps Cs c he he1 hc Fm ⟨max x0 ((3 / 2 : ℝ) ^ (1 / Fm.ez)), fun x hx i => ?_⟩` and prove the remaining obligations. Take `⟨A, hT, hJ, hL, hC, hS⟩` from `hx0 x (le_trans (le_max_left _ _) hx) i`. Establish `hx1 : (3 / 2 : ℝ) ^ (1 / Fm.ez) ≤ x` using `le_trans (le_max_right _ _) hx`.

Establish `hxe : 3 / 2 ≤ x ^ Fm.ez`. Establish `hpos : 0 ≤ (3 / 2 : ℝ) ^ (1 / Fm.ez)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_mul (by norm_num), one_div_mul_cancel hez.ne', Real.rpow_one]`. Use `_ ≤ x ^ Fm.ez := Real.rpow_le_rpow hpos hx1 hez.le`.

Conclude with `⟨A, hT, hC, weight_of_join hL (tieAdmG_holds _) (rangeW_of_sizes hS hxe) hJ, hS⟩`.
-/
theorem linkIRR_of_join_ex (eps Cs c : ℝ) (he : 0 < eps) (he1 : eps ≤ 1) (hc : 0 < c) (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i),
      LabelCountGoodInjective A ∧ AllJoinA A ∧ admLq (Fm.D x i) ∧
        CountAllRows A (epsC c (Fm.D x i).R.r (Fm.D x i).R.f) ∧ SizesRec (Fm.D x i) x Fm.ez Cs) :
    LinkIRR Fm := by
  obtain ⟨x0, hx0⟩ := h
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  refine linkIRR_of_allRows eps Cs c he he1 hc Fm ⟨max x0 ((3 / 2 : ℝ) ^ (1 / Fm.ez)), fun x hx i => ?_⟩
  obtain ⟨A, hT, hJ, hL, hC, hS⟩ := hx0 x (le_trans (le_max_left _ _) hx) i
  have hx1 : (3 / 2 : ℝ) ^ (1 / Fm.ez) ≤ x := le_trans (le_max_right _ _) hx
  have hxe : 3 / 2 ≤ x ^ Fm.ez := by
    have hpos : 0 ≤ (3 / 2 : ℝ) ^ (1 / Fm.ez) := by positivity
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (1 / Fm.ez)) ^ Fm.ez := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hez.ne', Real.rpow_one]
      _ ≤ x ^ Fm.ez := Real.rpow_le_rpow hpos hx1 hez.le
  exact ⟨A, hT, hC, weight_of_join hL (tieAdmG_holds _) (rangeW_of_sizes hS hxe) hJ, hS⟩

end

section
open Formalism.BasicNotions Formalism.MainNotions

/- English proof (translation)
Take `⟨hN, -, hK, -, -, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩` from `Fm.sizes x hx i`. Establish `hLx : (Fm.L x i).sc.x = x` using `Fm.L_x x i hx`. Establish `hLe : (Fm.L x i).sc.eps = eps` using `Fm.L_eps x i`. Establish `hε0 : 0 < eps` using `hLe ▸ (Fm.L x i).sc.eps_pos`. Establish `hε1 : eps < 1 / 52` using `hLe ▸ (Fm.L x i).sc.eps_lt`.

Establish `hx1 : (1 : ℝ) ≤ x` using `by linarith`. Establish `hx0 : (0 : ℝ) < x` using `by linarith`. Establish `hLz : (Fm.L x i).sc.ez = Fm.ez` using `Fm.toFamCore.L_ez x i`. Establish `hz0 : 0 < Fm.ez` using `div_pos hε0 (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)`. Establish `hzle : Fm.ez ≤ eps` using `div_le_self hε0.le Fm.toFamCore.one_le_J`.

Simplify using `only [SizeN, SizeK, SizeQD, SizeG, szTh, hLx, hLe, hLz] at hN hK hQD hG`. Establish `hf : ((Fm.D x i).R.f : ℝ) = 2 * ((Fm.D x i).R.n : ℝ)` using `by simp [Ranks.f]`. Establish `hfk : (Fm.D x i).R.f ≤ (Fm.D x i).R.k`. Use `(Fm.D x i).R.f_le_k` as an intermediate fact. Simplify `this` using `[Ranks.f, Ranks.n]`.

Establish `hmf : (Fm.D x i).R.m ≤ (Fm.D x i).R.f`. Use `(Fm.D x i).R.m_le_f` as an intermediate fact. Simplify `this` using `[Ranks.f, Ranks.n]`. Establish `hm2 : 2 ≤ (Fm.D x i).R.m` using `(Fm.D x i).R.two_le_m`. Establish `hrk : (Fm.D x i).R.k ≤ (Fm.D x i).R.r` using `by unfold Ranks.r; omega`.

Establish `hr2k : (Fm.D x i).R.r ≤ 2 * (Fm.D x i).R.k` using `by unfold Ranks.r; omega`. Establish `h5 : x ^ (9 / 2 + 10 * eps + eps / 100) ≤ x ^ (5 : ℝ)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `h56 : x ^ (5 : ℝ) ≤ x ^ Cs` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `h6 : x ^ (6 : ℝ) ≤ x ^ Cs` using `Real.rpow_le_rpow_of_exponent_le hx1 hCs`. Establish `h4 : x ^ (4 : ℝ) ≤ x ^ (9 / 2 + 10 * eps - eps / 100)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`.

Establish `h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps - eps / 100)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hx4p : (256 : ℝ) ≤ x ^ (4 : ℝ)`. Rewrite using `[show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`. Establish `: (4 : ℝ) ^ 4 ≤ x ^ 4` using `pow_le_pow_left₀ (by norm_num) hx4 4`. Evaluate the numerical expressions using `at this ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx65 : 2 * x ^ (5 : ℝ) ≤ x ^ (6 : ℝ)`. Rewrite using `[show (6 : ℝ) = 5 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]`. Establish `h0 : 0 ≤ x ^ (5 : ℝ)` using `Real.rpow_nonneg hx0.le _`. Use `mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ x by linarith) h0` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkx : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ)` using `le_trans hK.2 h5`. Establish `hkl : (256 : ℝ) ≤ (Fm.D x i).R.k` using `le_trans (le_trans hx4p h4) hK.1`. Establish `hfkR : ((Fm.D x i).R.f : ℝ) ≤ (Fm.D x i).R.k` using `by exact_mod_cast hfk`. Establish `hmfR : ((Fm.D x i).R.m : ℝ) ≤ (Fm.D x i).R.f` using `by exact_mod_cast hmf`.

Establish `hr2kR : ((Fm.D x i).R.r : ℝ) ≤ 2 * (Fm.D x i).R.k` using `by exact_mod_cast hr2k`. Establish `hrkR : ((Fm.D x i).R.k : ℝ) ≤ (Fm.D x i).R.r` using `by exact_mod_cast hrk`. Establish `hεq : x ^ (Fm.ez / 6) ≤ x ^ (Fm.ez / 5 - Fm.ez / 100)` using `Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)`. Establish `hpos6 : 0 < x ^ (Fm.ez / 6)` using `Real.rpow_pos_of_pos hx0 _`. Establish `hq : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.q : ℝ)`.

Establish `hl` using `hQD.1`. Establish `hq0 : (0 : ℝ) < (Fm.D x i).host.q`. Break down `Nat.eq_zero_or_pos (Fm.D x i).host.q with h0 | h0` into its components or cases. Rewrite `hl` using `[h0]`. Simplify using `at hl`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h0` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Establish `hd : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.d : ℝ)`. Establish `hl : x ^ (Fm.ez / 6) ≤ Real.log (Fm.D x i).host.d` using `le_trans hεq hQD.2.2.2.1`.

Establish `hd0 : (0 : ℝ) < (Fm.D x i).host.d`. Break down `Nat.eq_zero_or_pos (Fm.D x i).host.d with h0 | h0` into its components or cases. Rewrite `hl` using `[h0]`. Simplify using `at hl`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h0` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Introduce `j`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hg` using `(hG j j).1`.

Establish `hb : Real.exp (8 * x ^ eps) = (Real.exp (x ^ eps)) ^ 8`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions. Establish `hb0 : 0 ≤ Real.exp (x ^ eps)` using `(Real.exp_pos _).le`. Establish `hkb : Real.exp (x ^ eps) ≤ ((Fm.D x i).R.k : ℝ) * Real.exp (x ^ eps)`.

Establish `: (1 : ℝ) ≤ (Fm.D x i).R.k` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsc : (Fm.L x i).sc.b = Real.exp (x ^ eps)`. Rewrite using `[show (Fm.L x i).sc.b = Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) from rfl, hLx, hLe]`. Rewrite `hg` using `[hsc]`.

Establish `hze : x ^ Fm.ez ≤ x ^ eps` using `Real.rpow_le_rpow_of_exponent_le hx1 hzle`. Use `le_trans (Real.exp_le_exp.2 (by linarith : 8 * x ^ Fm.ez ≤ 8 * x ^ eps)) ?_` and prove the remaining obligations. Rewrite using `[hb]`. Conclude with `le_trans (pow_le_pow_left₀ hb0 hkb 8) hg`. Rewrite using `[← Real.rpow_two]`.

Establish `hn0 : (0 : ℝ) ≤ (Fm.D x i).R.n` using `Nat.cast_nonneg _`. Establish `hnf : ((Fm.D x i).R.n : ℝ) ≤ (Fm.D x i).R.f` using `by rw [hf]; linarith`. Conclude with `le_trans h2 (le_trans hN.1 hnf)`. Conclude with `le_trans hfkR (le_trans hkx h56)`. Conclude with `le_trans hmfR (le_trans hfkR (le_trans hkx h56))`.

Establish `h256 : 256 ≤ (Fm.D x i).R.k` using `by exact_mod_cast hkl`. Use linear arithmetic over natural numbers and integers. Establish `h2k : 2 * ((Fm.D x i).R.k : ℝ) ≤ 2 * x ^ (5 : ℝ)` using `mul_le_mul_of_nonneg_left hkx (by norm_num)`. Conclude with `le_trans hr2kR (le_trans h2k (le_trans hx65 h6))`. Rewrite using `[Nat.cast_min]`.

Conclude with `le_min hq hd`.
-/
theorem sizesRec_at {eps : ℝ} (Fm : FamP eps) {x : ℝ} (hx : Fm.x1 < x) (hx4 : 4 ≤ x) (i : Fm.Ix x) {Cs : ℝ}
    (hCs : 6 ≤ Cs) : Formalism.L2.GlobalTheoryTheory.ConcN.SizesRec (Fm.D x i) x Fm.ez Cs := by
  obtain ⟨hN, -, hK, -, -, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -, -⟩ := Fm.sizes x hx i
  have hLx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hLe : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have hε0 : 0 < eps := hLe ▸ (Fm.L x i).sc.eps_pos
  have hε1 : eps < 1 / 52 := hLe ▸ (Fm.L x i).sc.eps_lt
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hLz : (Fm.L x i).sc.ez = Fm.ez := Fm.toFamCore.L_ez x i
  have hz0 : 0 < Fm.ez := div_pos hε0 (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  have hzle : Fm.ez ≤ eps := div_le_self hε0.le Fm.toFamCore.one_le_J
  simp only [SizeN, SizeK, SizeQD, SizeG, szTh, hLx, hLe, hLz] at hN hK hQD hG

  have hf : ((Fm.D x i).R.f : ℝ) = 2 * ((Fm.D x i).R.n : ℝ) := by simp [Ranks.f]
  have hfk : (Fm.D x i).R.f ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.f_le_k
    simpa [Ranks.f, Ranks.n] using this
  have hmf : (Fm.D x i).R.m ≤ (Fm.D x i).R.f := by
    have := (Fm.D x i).R.m_le_f
    simpa [Ranks.f, Ranks.n] using this
  have hm2 : 2 ≤ (Fm.D x i).R.m := (Fm.D x i).R.two_le_m
  have hrk : (Fm.D x i).R.k ≤ (Fm.D x i).R.r := by unfold Ranks.r; omega
  have hr2k : (Fm.D x i).R.r ≤ 2 * (Fm.D x i).R.k := by unfold Ranks.r; omega

  have h5 : x ^ (9 / 2 + 10 * eps + eps / 100) ≤ x ^ (5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h56 : x ^ (5 : ℝ) ≤ x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h6 : x ^ (6 : ℝ) ≤ x ^ Cs := Real.rpow_le_rpow_of_exponent_le hx1 hCs
  have h4 : x ^ (4 : ℝ) ≤ x ^ (9 / 2 + 10 * eps - eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps - eps / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hx4p : (256 : ℝ) ≤ x ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have : (4 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx4 4
    norm_num at this ⊢; linarith
  have hx65 : 2 * x ^ (5 : ℝ) ≤ x ^ (6 : ℝ) := by
    rw [show (6 : ℝ) = 5 + 1 by norm_num, Real.rpow_add hx0, Real.rpow_one]
    have h0 : 0 ≤ x ^ (5 : ℝ) := Real.rpow_nonneg hx0.le _
    have := mul_le_mul_of_nonneg_left (show (2 : ℝ) ≤ x by linarith) h0
    linarith
  have hkx : ((Fm.D x i).R.k : ℝ) ≤ x ^ (5 : ℝ) := le_trans hK.2 h5
  have hkl : (256 : ℝ) ≤ (Fm.D x i).R.k := le_trans (le_trans hx4p h4) hK.1
  have hfkR : ((Fm.D x i).R.f : ℝ) ≤ (Fm.D x i).R.k := by exact_mod_cast hfk
  have hmfR : ((Fm.D x i).R.m : ℝ) ≤ (Fm.D x i).R.f := by exact_mod_cast hmf
  have hr2kR : ((Fm.D x i).R.r : ℝ) ≤ 2 * (Fm.D x i).R.k := by exact_mod_cast hr2k
  have hrkR : ((Fm.D x i).R.k : ℝ) ≤ (Fm.D x i).R.r := by exact_mod_cast hrk

  have hεq : x ^ (Fm.ez / 6) ≤ x ^ (Fm.ez / 5 - Fm.ez / 100) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hpos6 : 0 < x ^ (Fm.ez / 6) := Real.rpow_pos_of_pos hx0 _
  have hq : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.q : ℝ) := by
    have hl := hQD.1
    have hq0 : (0 : ℝ) < (Fm.D x i).host.q := by
      rcases Nat.eq_zero_or_pos (Fm.D x i).host.q with h0 | h0
      · rw [h0] at hl; simp at hl; linarith
      · exact_mod_cast h0
    calc Real.exp (x ^ (Fm.ez / 6)) ≤ Real.exp (Real.log (Fm.D x i).host.q) := Real.exp_le_exp.2 hl
      _ = (Fm.D x i).host.q := Real.exp_log hq0
  have hd : Real.exp (x ^ (Fm.ez / 6)) ≤ ((Fm.D x i).host.d : ℝ) := by
    have hl : x ^ (Fm.ez / 6) ≤ Real.log (Fm.D x i).host.d := le_trans hεq hQD.2.2.2.1
    have hd0 : (0 : ℝ) < (Fm.D x i).host.d := by
      rcases Nat.eq_zero_or_pos (Fm.D x i).host.d with h0 | h0
      · rw [h0] at hl; simp at hl; linarith
      · exact_mod_cast h0
    calc Real.exp (x ^ (Fm.ez / 6)) ≤ Real.exp (Real.log (Fm.D x i).host.d) := Real.exp_le_exp.2 hl
      _ = (Fm.D x i).host.d := Real.exp_log hd0
  intro j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hg := (hG j j).1
    have hb : Real.exp (8 * x ^ eps) = (Real.exp (x ^ eps)) ^ 8 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hb0 : 0 ≤ Real.exp (x ^ eps) := (Real.exp_pos _).le
    have hkb : Real.exp (x ^ eps) ≤ ((Fm.D x i).R.k : ℝ) * Real.exp (x ^ eps) := by
      have : (1 : ℝ) ≤ (Fm.D x i).R.k := by linarith
      nlinarith
    have hsc : (Fm.L x i).sc.b = Real.exp (x ^ eps) := by
      rw [show (Fm.L x i).sc.b = Real.exp ((Fm.L x i).sc.x ^ (Fm.L x i).sc.eps) from rfl, hLx, hLe]
    rw [hsc] at hg
    have hze : x ^ Fm.ez ≤ x ^ eps := Real.rpow_le_rpow_of_exponent_le hx1 hzle
    refine le_trans (Real.exp_le_exp.2 (by linarith : 8 * x ^ Fm.ez ≤ 8 * x ^ eps)) ?_
    rw [hb]
    exact le_trans (pow_le_pow_left₀ hb0 hkb 8) hg
  ·
    rw [← Real.rpow_two]
    have hn0 : (0 : ℝ) ≤ (Fm.D x i).R.n := Nat.cast_nonneg _
    have hnf : ((Fm.D x i).R.n : ℝ) ≤ (Fm.D x i).R.f := by rw [hf]; linarith
    exact le_trans h2 (le_trans hN.1 hnf)
  · exact le_trans hfkR (le_trans hkx h56)
  · exact le_trans hmfR (le_trans hfkR (le_trans hkx h56))
  ·
    have h256 : 256 ≤ (Fm.D x i).R.k := by exact_mod_cast hkl
    omega
  · have h2k : 2 * ((Fm.D x i).R.k : ℝ) ≤ 2 * x ^ (5 : ℝ) := mul_le_mul_of_nonneg_left hkx (by norm_num)
    exact le_trans hr2kR (le_trans h2k (le_trans hx65 h6))
  · rw [Nat.cast_min]
    exact le_min hq hd

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

/- English proof (translation)
Introduce `hG 𝒜 sel cIc hcI irrC`. Establish `irr : Closed (D3 3 𝒜) fun {eps} Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i), Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧ Formalism.Main …` using `closed_of_mem (irrC.imp fun Fm _ _ H hc => by`. Take `⟨x0, H⟩` from `H`. Use `⟨max (max x0 (sel Fm (d3_a hc)).1) (max (Fm.x1 + 1) 4), fun x hx i => ?_⟩` and prove the remaining obligations. Establish `h1 : Fm.x1 < x` using `by have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx; linarith`.

Establish `hs : (sel Fm (d3_a hc)).1 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Take `⟨A, a, b, c⟩` from `H x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) i`. Conclude with `⟨A, a, b, GlobalTheory.Top.Lq.admissibleLabelWeights_of_greenCuspidalParametrisation hG _ _ ((sel Fm (d3_a hc)).2 x h1 hs i).T.n.types, c, sizesRec_at Fm h1 (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) i le_rfl⟩)`. Conclude with `(irr.and (closed_eps_le_one _)).imp fun Fm _ he ⟨h, h1⟩ => linkIRR_of_join_ex _ 6 cIc he h1 hcI Fm h`.
-/
theorem link_irr : GlobalTheory.GLq.Green → ∀ (𝒜 : FamClass)
    (sel : Formalism.L2.TSel 𝒜)
    (cIc : ℝ)
    (hcI : 0 < cIc)
    (irrC : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f)), Closed (D3 3 𝒜) fun Fm _ => LinkIRR Fm := by
  intro hG 𝒜 sel cIc hcI irrC
  have irr : Closed (D3 3 𝒜) fun {eps} Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧ Formalism.MainNotions.ArithmeticCylinders.admLq (Fm.D x i) ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.SizesRec (Fm.D x i) x Fm.ez 6 :=
    closed_of_mem (irrC.imp fun Fm _ _ H hc => by
      obtain ⟨x0, H⟩ := H
      refine ⟨max (max x0 (sel Fm (d3_a hc)).1) (max (Fm.x1 + 1) 4), fun x hx i => ?_⟩
      have h1 : Fm.x1 < x := by have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx; linarith
      have hs : (sel Fm (d3_a hc)).1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
      obtain ⟨A, a, b, c⟩ := H x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) i
      exact ⟨A, a, b, GlobalTheory.Top.Lq.admissibleLabelWeights_of_greenCuspidalParametrisation hG _ _ ((sel Fm (d3_a hc)).2 x h1 hs i).T.n.types, c,
        sizesRec_at Fm h1 (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) i le_rfl⟩)
  exact (irr.and (closed_eps_le_one _)).imp fun Fm _ he ⟨h, h1⟩ =>
      linkIRR_of_join_ex _ 6 cIc he h1 hcI Fm h

end GlobalTheory.Top.Irr
