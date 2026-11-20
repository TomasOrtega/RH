import Formalism.SharpRestriction.CuspSpanNormBounds.MassRatioBound

noncomputable section

namespace Formalism.MainNotions.MassRatioBoundPower

open NumberField Formalism.MainNotions.MassRatioZetaBound

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `tprod_nonneg fun P => (eulerFac_le hM P.1 (by haveI := P.2; exact two_le_absNorm P.1)).1.le`.
-/
theorem lValEta_nonneg [StarRing K] {M : ℕ} (hM : 3 ≤ M) : 0 ≤ Formalism.HermitianLatticesTheory.lValEta K M :=
  tprod_nonneg fun P => (eulerFac_le hM P.1 (by haveI := P.2; exact two_le_absNorm P.1)).1.le

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.massRatioRightSide`. Establish `hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K` using `by have := one_le_two_vInv (K := K); linarith`. Conclude with `mul_nonneg (div_nonneg (by positivity) (Real.sqrt_nonneg _)) (lValEta_nonneg hM)`.
-/
theorem mass_ratio_rhs_nonneg [StarRing K] {M : ℕ} (hM : 3 ≤ M) : 0 ≤ Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by have := one_le_two_vInv (K := K); linarith
  exact mul_nonneg (div_nonneg (by positivity) (Real.sqrt_nonneg _)) (lValEta_nonneg hM)

/- English proof (translation)
The claim follows from `tsum_nonneg fun m => by positivity`.
-/
theorem zeta_three_halves_nonneg : 0 ≤ zetaGL3GL2 := tsum_nonneg fun m => by positivity

def cZ : ℕ := Nat.ceil (4 * zetaGL3GL2 / Real.log 2)

/- English proof (translation)
Establish `hl : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Establish `e : (2 : ℝ) ^ cZ = Real.exp ((cZ : ℝ) * Real.log 2)`. Rewrite using `[Real.exp_nat_mul, Real.exp_log (by norm_num)]`. Rewrite using `[e]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_le_two_pow : Real.exp (4 * zetaGL3GL2) ≤ 2 ^ cZ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have e : (2 : ℝ) ^ cZ = Real.exp ((cZ : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e]
  apply Real.exp_le_exp.2
  calc 4 * zetaGL3GL2 = (4 * zetaGL3GL2 / Real.log 2) * Real.log 2 := by field_simp
    _ ≤ (cZ : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hl.le

/- English proof (translation)
Use `(mass_ratio_rhs_le_factorial h3).trans ?_` and prove the remaining obligations. Use `set f := Formalism.HermitianLatticesTheory.fDeg K with hf`. Establish `hY1 : (1 : ℝ) ≤ Y` using `by linarith`. Establish `hv0 : 0 ≤ Formalism.HermitianLatticesTheory.vInv K` using `by have := one_le_two_vInv (K := K); linarith`. Establish `hfac : (((M - 1).factorial : ℕ) : ℝ) ≤ Y ^ n`.

Establish `h1 : (M - 1).factorial ≤ (M - 1) ^ (M - 1)` using `Nat.factorial_le_pow (M - 1)`. Establish `h2 : ((M - 1 : ℕ) : ℝ) ≤ Y`. Establish `: ((M - 1 : ℕ) : ℝ) ≤ (n : ℝ)` using `by exact_mod_cast (Nat.sub_le M 1).trans hMn`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.

Establish `hvp : Formalism.HermitianLatticesTheory.vInv K / Real.pi ≤ Y`. Establish `hpi : 1 ≤ Real.pi` using `by linarith [Real.pi_gt_three]`. Combine the equalities or inequalities in the displayed calculation. Establish `hpow : (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M ≤ Y ^ n` using `(pow_le_pow_left₀ (by positivity) hvp M).trans (pow_le_pow_right₀ hY1 (by omega))`. Establish `hA : ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ f ≤ (Y ^ n * Y ^ n) ^ f` using `pow_le_pow_left₀ (by positivity) (mul_le_mul hfac hpow (by positivity) (by positivity)) f`.

Establish `hB : Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) ≤ (Y ^ cZ) ^ f`. Establish `hd' : (Module.finrank ℚ K : ℝ) ≤ 2 * (f : ℝ)` using `by exact_mod_cast hd`. Combine the equalities or inequalities in the displayed calculation. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Use polynomial arithmetic with `[zeta_three_halves_nonneg]`.

Use `_ = Real.exp (4 * zetaGL3GL2) ^ f := Real.exp_nat_mul _ _`. Use `_ ≤ ((2 : ℝ) ^ cZ) ^ f := pow_le_pow_left₀ (Real.exp_pos _).le exp_le_two_pow f`. Use `_ ≤ (Y ^ cZ) ^ f := pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hY _) f`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_add, ← mul_pow, ← pow_add, ← pow_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mass_ratio_rhs_le_pow_Y [StarRing K] (hd : Module.finrank ℚ K ≤ 2 * Formalism.HermitianLatticesTheory.fDeg K) {n M : ℕ} (h3 : 3 ≤ M) (hMn : M ≤ n)
    {Y : ℝ} (hY : 2 ≤ Y) (hn : (n : ℝ) ≤ Y) (hv : 2 * Formalism.HermitianLatticesTheory.vInv K ≤ Y) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K M ≤ Y ^ ((2 * n + cZ) * Formalism.HermitianLatticesTheory.fDeg K) := by
  refine (mass_ratio_rhs_le_factorial h3).trans ?_
  set f := Formalism.HermitianLatticesTheory.fDeg K with hf
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hv0 : 0 ≤ Formalism.HermitianLatticesTheory.vInv K := by have := one_le_two_vInv (K := K); linarith
  have hfac : (((M - 1).factorial : ℕ) : ℝ) ≤ Y ^ n := by
    have h1 : (M - 1).factorial ≤ (M - 1) ^ (M - 1) := Nat.factorial_le_pow (M - 1)
    have h2 : ((M - 1 : ℕ) : ℝ) ≤ Y := by
      have : ((M - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.sub_le M 1).trans hMn
      linarith
    calc (((M - 1).factorial : ℕ) : ℝ) ≤ (((M - 1) ^ (M - 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((M - 1 : ℕ) : ℝ) ^ (M - 1) := by push_cast; ring
      _ ≤ Y ^ (M - 1) := pow_le_pow_left₀ (by positivity) h2 _
      _ ≤ Y ^ n := pow_le_pow_right₀ hY1 (by omega)
  have hvp : Formalism.HermitianLatticesTheory.vInv K / Real.pi ≤ Y := by
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc Formalism.HermitianLatticesTheory.vInv K / Real.pi ≤ Formalism.HermitianLatticesTheory.vInv K := div_le_self hv0 hpi
      _ ≤ Y := by linarith
  have hpow : (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M ≤ Y ^ n :=
    (pow_le_pow_left₀ (by positivity) hvp M).trans (pow_le_pow_right₀ hY1 (by omega))
  have hA : ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ f ≤ (Y ^ n * Y ^ n) ^ f :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul hfac hpow (by positivity) (by positivity)) f
  have hB : Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) ≤ (Y ^ cZ) ^ f := by
    have hd' : (Module.finrank ℚ K : ℝ) ≤ 2 * (f : ℝ) := by exact_mod_cast hd
    calc Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) ≤ Real.exp ((f : ℝ) * (4 * zetaGL3GL2)) := by
          apply Real.exp_le_exp.2; nlinarith [zeta_three_halves_nonneg]
      _ = Real.exp (4 * zetaGL3GL2) ^ f := Real.exp_nat_mul _ _
      _ ≤ ((2 : ℝ) ^ cZ) ^ f := pow_le_pow_left₀ (Real.exp_pos _).le exp_le_two_pow f
      _ ≤ (Y ^ cZ) ^ f := pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hY _) f
  calc ((((M - 1).factorial : ℕ) : ℝ) * (Formalism.HermitianLatticesTheory.vInv K / Real.pi) ^ M) ^ f *
        Real.exp (2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)) ≤ (Y ^ n * Y ^ n) ^ f * (Y ^ cZ) ^ f :=
        mul_le_mul hA hB (Real.exp_pos _).le (by positivity)
    _ = Y ^ ((2 * n + cZ) * f) := by
        rw [← pow_add, ← mul_pow, ← pow_add, ← pow_mul]; congr 1; ring

/- English proof (translation)
Establish `hY1 : (1 : ℝ) ≤ Y` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Use `pow_le_pow_right₀ (one_le_pow₀ hY1) ?_` and prove the remaining obligations. Rewrite using `[Nat.card_Icc]`. Use linear arithmetic over natural numbers and integers.

Use `_ = Y ^ ((2 * n + cZ) * n * Formalism.HermitianLatticesTheory.fDeg K) := by rw [← pow_mul]; congr 1; ring`.
-/
theorem prod_massRatio_le [StarRing K] (hd : Module.finrank ℚ K ≤ 2 * Formalism.HermitianLatticesTheory.fDeg K) (n : ℕ) {Y : ℝ} (hY : 2 ≤ Y)
    (hn : (n : ℝ) ≤ Y) (hv : 2 * Formalism.HermitianLatticesTheory.vInv K ≤ Y) :
    ∏ M ∈ Finset.Icc 3 n, Formalism.HermitianLatticesTheory.massRatioRightSide K M ≤ Y ^ ((2 * n + cZ) * n * Formalism.HermitianLatticesTheory.fDeg K) := by
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  calc ∏ M ∈ Finset.Icc 3 n, Formalism.HermitianLatticesTheory.massRatioRightSide K M
      ≤ ∏ _M ∈ Finset.Icc 3 n, Y ^ ((2 * n + cZ) * Formalism.HermitianLatticesTheory.fDeg K) :=
        Finset.prod_le_prod (fun M hM => mass_ratio_rhs_nonneg (Finset.mem_Icc.1 hM).1)
          (fun M hM => mass_ratio_rhs_le_pow_Y hd (Finset.mem_Icc.1 hM).1 (Finset.mem_Icc.1 hM).2 hY hn hv)
    _ = (Y ^ ((2 * n + cZ) * Formalism.HermitianLatticesTheory.fDeg K)) ^ (Finset.Icc 3 n).card := Finset.prod_const _
    _ ≤ (Y ^ ((2 * n + cZ) * Formalism.HermitianLatticesTheory.fDeg K)) ^ n := by
        refine pow_le_pow_right₀ (one_le_pow₀ hY1) ?_
        rw [Nat.card_Icc]; omega
    _ = Y ^ ((2 * n + cZ) * n * Formalism.HermitianLatticesTheory.fDeg K) := by rw [← pow_mul]; congr 1; ring

/- English proof (translation)
Use `set N : ℝ := ((Ideal.absNorm P : ℕ) : ℝ) with hNdef`. Establish `hN2 : (2 : ℝ) ≤ N` using `by rw [hNdef]; exact_mod_cast hN`. Establish `hN0 : 0 < N` using `by linarith`. Take `⟨hb1, hb2⟩` from `rpow_bounds hN2 hM`. Use `set y : ℝ := 1 / N ^ ((3 : ℝ) / 2) with hy`.

Establish `hy0 : 0 ≤ y` using `by positivity`. Establish `hle1 : Real.exp (-(2 * y)) ≤ 1` using `Real.exp_le_one_iff.2 (by linarith)`. Unfold `Formalism.HermitianLatticesTheory.eulerFac`. Use `split_ifs with hc`. Establish `hx : Real.sqrt N ^ (-(M : ℤ)) = N ^ (-(M : ℝ) / 2)`.

Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hN0.le]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hNdef, hx]`.

Use `set x : ℝ := N ^ (-(M : ℝ) / 2) with hxdef`. Establish `hx0 : 0 < x` using `Real.rpow_pos_of_pos hN0 _`. Establish `h1 : x ≤ 1 / 2` using `hb1.trans hb2`. Break down `Nat.even_or_odd M with he | ho` into its components or cases. Rewrite using `[he.neg_one_pow, one_mul]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ho.neg_one_pow, neg_one_mul, sub_neg_eq_add]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_le_inv₀ (Real.exp_pos _) (by linarith)]`. Combine the linear relations using `[Real.add_one_le_exp x]`.

Rewrite using `[← hNdef] set z : ℝ := N ^ (-(M : ℤ)) with hz`. Establish `hz0 : 0 < z` using `zpow_pos hN0 _`. Establish `hzx : z ≤ N ^ (-(M : ℝ) / 2)`. Rewrite using `[hz, ← Real.rpow_intCast]`. Apply `Real.rpow_le_rpow_of_exponent_le (by linarith)` to reduce the goal to its premises.

Use `push_cast`. Establish `: (0 : ℝ) ≤ M` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz1 : z ≤ 1 / 2` using `hzx.trans (hb1.trans hb2)`. Establish `hpos : 0 < 1 - z` using `by linarith`.

Establish `e : (1 - z) ^ ((-1 : ℝ) / 2) = ((1 - z)⁻¹) ^ ((1 : ℝ) / 2)`. Rewrite using `[Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Establish `hge1 : 1 ≤ (1 - z)⁻¹` using `one_le_inv₀ hpos |>.2 (by linarith)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem eulerFac_ge [StarRing K] {M : ℕ} (hM : 3 ≤ M) (P : Ideal (𝓞 K)) (hN : 2 ≤ Ideal.absNorm P) :
    Real.exp (-(2 * (1 / ((Ideal.absNorm P : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))) ≤ Formalism.HermitianLatticesTheory.eulerFac K M P := by
  set N : ℝ := ((Ideal.absNorm P : ℕ) : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast hN
  have hN0 : 0 < N := by linarith
  obtain ⟨hb1, hb2⟩ := rpow_bounds hN2 hM
  set y : ℝ := 1 / N ^ ((3 : ℝ) / 2) with hy
  have hy0 : 0 ≤ y := by positivity
  have hle1 : Real.exp (-(2 * y)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  unfold Formalism.HermitianLatticesTheory.eulerFac
  split_ifs with hc
  · have hx : Real.sqrt N ^ (-(M : ℤ)) = N ^ (-(M : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hN0.le]
      congr 1; push_cast; ring
    rw [← hNdef, hx]
    set x : ℝ := N ^ (-(M : ℝ) / 2) with hxdef
    have hx0 : 0 < x := Real.rpow_pos_of_pos hN0 _
    have h1 : x ≤ 1 / 2 := hb1.trans hb2
    rcases Nat.even_or_odd M with he | ho
    · rw [he.neg_one_pow, one_mul]
      calc Real.exp (-(2 * y)) ≤ 1 := hle1
        _ ≤ (1 - x)⁻¹ := one_le_inv₀ (by linarith) |>.2 (by linarith)
    · rw [ho.neg_one_pow, neg_one_mul, sub_neg_eq_add]
      calc Real.exp (-(2 * y)) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
        _ = (Real.exp x)⁻¹ := Real.exp_neg x
        _ ≤ (1 + x)⁻¹ := by
            rw [inv_le_inv₀ (Real.exp_pos _) (by linarith)]
            linarith [Real.add_one_le_exp x]
  · rw [← hNdef]
    set z : ℝ := N ^ (-(M : ℤ)) with hz
    have hz0 : 0 < z := zpow_pos hN0 _
    have hzx : z ≤ N ^ (-(M : ℝ) / 2) := by
      rw [hz, ← Real.rpow_intCast]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      push_cast
      have : (0 : ℝ) ≤ M := by positivity
      linarith
    have hz1 : z ≤ 1 / 2 := hzx.trans (hb1.trans hb2)
    have hpos : 0 < 1 - z := by linarith
    have e : (1 - z) ^ ((-1 : ℝ) / 2) = ((1 - z)⁻¹) ^ ((1 : ℝ) / 2) := by
      rw [Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]; congr 1; ring
    rw [e]
    have hge1 : 1 ≤ (1 - z)⁻¹ := one_le_inv₀ hpos |>.2 (by linarith)
    calc Real.exp (-(2 * y)) ≤ 1 := hle1
      _ ≤ ((1 - z)⁻¹) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hge1 (by norm_num)

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.lValEta`. Establish `hN : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 2 ≤ Ideal.absNorm P.1` using `fun P => by haveI := P.2; exact two_le_absNorm P.1`. Distinguish the cases in `hm : Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1)`. Use `ge_of_tendsto' hm.hasProd fun s => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (by norm_num)))` and prove the remaining obligations. Establish `e : ∑ P ∈ s, 1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) = ∑ Q ∈ s.map (Function.Embedding.subtype _), 1 / ((Ideal.absNorm Q : ℕ) : ℝ) ^ ((3 : ℝ) / 2)`. Rewrite using `[Finset.sum_map]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Use `sum_norm_le _ fun Q hQ => ?_` and prove the remaining obligations. Take `⟨P, -, rfl⟩` from `Finset.mem_map.1 hQ`. Conclude with `P.2`. Use `_ = ∏ P ∈ s, Real.exp (-(2 * (1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))) := by`. Rewrite using `[← Real.exp_sum]`.

Use `congr 1`. Rewrite using `[Finset.mul_sum, ← Finset.sum_neg_distrib]`. Use `_ ≤ ∏ P ∈ s, Formalism.HermitianLatticesTheory.eulerFac K M P.1 := Finset.prod_le_prod (fun P _ => (Real.exp_pos _).le) (fun P _ => eulerFac_ge hM P.1 (hN P))`. Rewrite using `[tprod_eq_one_of_not_multipliable hm]`. Conclude with `Real.exp_le_one_iff.2 (by have := zeta_three_halves_nonneg; have : (0 : ℝ) ≤ Module.finrank ℚ K := by positivity nlinarith)`.
-/
theorem lValEta_ge [StarRing K] {M : ℕ} (hM : 3 ≤ M) :
    Real.exp (-(2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2))) ≤ Formalism.HermitianLatticesTheory.lValEta K M := by
  classical
  unfold Formalism.HermitianLatticesTheory.lValEta
  have hN : ∀ P : {P : Ideal (𝓞 K) // P.IsMaximal}, 2 ≤ Ideal.absNorm P.1 := fun P => by
    haveI := P.2; exact two_le_absNorm P.1
  by_cases hm : Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1)
  · refine ge_of_tendsto' hm.hasProd fun s => ?_
    calc Real.exp (-(2 * ((Module.finrank ℚ K : ℝ) * zetaGL3GL2)))
        ≤ Real.exp (-(2 * ∑ P ∈ s, 1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))) := by
          refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
          have e : ∑ P ∈ s, 1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) =
              ∑ Q ∈ s.map (Function.Embedding.subtype _), 1 / ((Ideal.absNorm Q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
            rw [Finset.sum_map]; rfl
          rw [e]
          refine sum_norm_le _ fun Q hQ => ?_
          obtain ⟨P, -, rfl⟩ := Finset.mem_map.1 hQ
          exact P.2
      _ = ∏ P ∈ s, Real.exp (-(2 * (1 / ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)))) := by
          rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      _ ≤ ∏ P ∈ s, Formalism.HermitianLatticesTheory.eulerFac K M P.1 :=
          Finset.prod_le_prod (fun P _ => (Real.exp_pos _).le) (fun P _ => eulerFac_ge hM P.1 (hN P))
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact Real.exp_le_one_iff.2 (by have := zeta_three_halves_nonneg; have : (0 : ℝ) ≤ Module.finrank ℚ K := by positivity
                                    nlinarith)

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.massRatioRightSide`. Establish `hv : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv K` using `one_le_two_vInv`. Establish `hv0 : 0 < Formalism.HermitianLatticesTheory.vInv K` using `by linarith`. Establish `hL : 0 < Formalism.HermitianLatticesTheory.lValEta K M` using `lt_of_lt_of_le (Real.exp_pos _) (lValEta_ge hM)`. Establish `hb : 0 < Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K)` using `Real.sqrt_pos.2 (by positivity)`.

Establish `hf : (0 : ℝ) < (((M - 1).factorial : ℕ) : ℝ)` using `by exact_mod_cast Nat.factorial_pos _`. Conclude with `mul_pos (div_pos (by positivity) hb) hL`.
-/
theorem massRatio_pos [StarRing K] {M : ℕ} (hM : 3 ≤ M) : 0 < Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  have hv : 1 ≤ 2 * Formalism.HermitianLatticesTheory.vInv K := one_le_two_vInv
  have hv0 : 0 < Formalism.HermitianLatticesTheory.vInv K := by linarith
  have hL : 0 < Formalism.HermitianLatticesTheory.lValEta K M := lt_of_lt_of_le (Real.exp_pos _) (lValEta_ge hM)
  have hb : 0 < Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) := Real.sqrt_pos.2 (by positivity)
  have hf : (0 : ℝ) < (((M - 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  exact mul_pos (div_pos (by positivity) hb) hL

end Formalism.MainNotions.MassRatioBoundPower

end
