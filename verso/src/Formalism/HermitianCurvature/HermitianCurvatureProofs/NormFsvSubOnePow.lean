import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormLeDecay
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormWaveMDiff

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

/- English proof (translation)
Establish `e : ∀ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t) = fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t) + 3 * (fsv (s + σ) t * φ t) - fsv s t * φ t`. Introduce `t`. Establish `e1 : fsv (s + σ) t = fsv s t * fsv σ t` using `(fsv_mul_fsv s σ t).symm`. Establish `e2 : fsv (s + 2 * σ) t = fsv s t * fsv σ t * fsv σ t`. Rewrite using `[fsv_mul_fsv, fsv_mul_fsv]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : fsv (s + 3 * σ) t = fsv s t * fsv σ t * fsv σ t * fsv σ t`. Rewrite using `[fsv_mul_fsv, fsv_mul_fsv, fsv_mul_fsv]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, e3]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e]`. Establish `i0` using `integrable_fsv_mul hφ hi s`.

Establish `i1` using `integrable_fsv_mul hφ hi (s + σ)`. Establish `i2` using `integrable_fsv_mul hφ hi (s + 2 * σ)`. Establish `i3` using `integrable_fsv_mul hφ hi (s + 3 * σ)`. Establish `j1 : Integrable (fun t => fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t))` using `i3.sub (i2.const_mul 3)`. Establish `j2 : Integrable (fun t => fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t) + 3 * (fsv (s + σ) t * φ t))` using `j1.add (i1.const_mul 3)`.

Rewrite using `[integral_sub j2 i0, integral_add j1 (i1.const_mul 3), integral_sub i3 (i2.const_mul 3), integral_const_mul, integral_const_mul]`.
-/
theorem transform_diff3 {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) (σ s : ℂ) :
    ∫ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t) =
      (∫ t, fsv (s + 3 * σ) t * φ t) - 3 * (∫ t, fsv (s + 2 * σ) t * φ t) + 3 * (∫ t, fsv (s + σ) t * φ t) -
        ∫ t, fsv s t * φ t := by
  have e : ∀ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t) =
      fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t) + 3 * (fsv (s + σ) t * φ t) - fsv s t * φ t := by
    intro t
    have e1 : fsv (s + σ) t = fsv s t * fsv σ t := (fsv_mul_fsv s σ t).symm
    have e2 : fsv (s + 2 * σ) t = fsv s t * fsv σ t * fsv σ t := by
      rw [fsv_mul_fsv, fsv_mul_fsv]; congr 1; ring
    have e3 : fsv (s + 3 * σ) t = fsv s t * fsv σ t * fsv σ t * fsv σ t := by
      rw [fsv_mul_fsv, fsv_mul_fsv, fsv_mul_fsv]; congr 1; ring
    rw [e1, e2, e3]; ring
  simp only [e]
  have i0 := integrable_fsv_mul hφ hi s
  have i1 := integrable_fsv_mul hφ hi (s + σ)
  have i2 := integrable_fsv_mul hφ hi (s + 2 * σ)
  have i3 := integrable_fsv_mul hφ hi (s + 3 * σ)
  have j1 : Integrable (fun t => fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t)) := i3.sub (i2.const_mul 3)
  have j2 : Integrable (fun t => fsv (s + 3 * σ) t * φ t - 3 * (fsv (s + 2 * σ) t * φ t) +
      3 * (fsv (s + σ) t * φ t)) := j1.add (i1.const_mul 3)
  rw [integral_sub j2 i0, integral_add j1 (i1.const_mul 3), integral_sub i3 (i2.const_mul 3),
    integral_const_mul, integral_const_mul]

/- English proof (translation)
Rewrite using `[norm_pow]`. Establish `: ‖fsv σ t - 1‖ ≤ 2` using `(norm_sub_le _ _).trans (by rw [norm_fsv, norm_one]; norm_num)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_fsv_sub_one_pow (σ t : ℂ) : ‖(fsv σ t - 1) ^ 3‖ ≤ 8 := by
  rw [norm_pow]
  have : ‖fsv σ t - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_fsv, norm_one]; norm_num)
  calc ‖fsv σ t - 1‖ ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) this 3
    _ = 8 := by norm_num

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `hP Cb`. Take `⟨CcF, hFL⟩` from `Formalism.FourierDecayAlt.P.limit_of_module_forms Cb`. Take `⟨CcW, hWD⟩` from `hWDF hP Cb`. Use `⟨max CcF CcW, ?_⟩` and prove the remaining obligations. Introduce `Wp Wq _ _ _ _ _ _ P p f χ ε A N cut lo hi hθ hχ hε hf hfA hthr hcut hon hroom j hj w hw hN h h' hh hh'`.

Establish `hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)` using `by positivity`. Establish `hthrF : CcF * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A`. Use `mul_le_mul_of_nonneg_right (le_max_left CcF CcW) hX` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hthrW : CcW * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A`.

Use `mul_le_mul_of_nonneg_right (le_max_right CcF CcW) hX` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Take `⟨hcpt, hlim⟩` from `hFL Wp Wq P p f χ ε A (N + 3) cut hθ hχ hε hf hfA hthrF hcut`. Establish `hWDa` using `hWD Wp Wq P p f χ ε A N cut hθ hχ hε hf hfA hthrW hcut j hj w hw hN h hh`. Take `⟨grid, hinj, hgr⟩` from `grid_exists P p.l0 lo hi hon w hw j (by`.

Establish `h1 : (w.length : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `h2 : (j : ℝ) ≤ P.r` using `by exact_mod_cast hj`. Use the proof step `nlinarith)`. Establish `hlp : ∀ n : Fin 3 → Fin (2 * j + 1), (KB.plusW (List.ofFn fun a => grid a (n a)) w).length ≤ N + 3`. Introduce `n`.

Rewrite using `[Formalism.FourierDecayAlt.P.PBD.plusW_eq]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `hlm : ∀ n : Fin 3 → Fin (2 * j + 1), (KB.minusW (List.ofFn fun a => grid a (n a)) w).length ≤ N + 3`. Introduce `n`.

Rewrite using `[Formalism.FourierDecayAlt.P.PBD.minusW_eq]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `bnd : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' → w'.length ≤ N + 3 → ∀ a : C.LPt, ∃ B, 0 ≤ B ∧ ∀ n, ‖p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) j w' a a‖ ≤ B` using `fun w' hw' hl a => bdd_of_tendsto (hlim j w' hw' hl a a)`. Use `choose Bp hBp0 hBp using fun n => bnd _ (hgr n).1 (hlp n) h`.

Use `choose Bm hBm0 hBm using fun n => bnd _ (hgr n).2.1 (hlm n) h'`. Take `⟨Bh, hBh0, hBh⟩` from `bnd w hw (by omega) h`. Take `⟨Bh', hBh'0, hBh'⟩` from `bnd w hw (by omega) h'`. Use `set B := Bh + Bh' + ∑ n, (Bp n + Bm n) with hBdef`. Establish `hS0 : 0 ≤ ∑ n, (Bp n + Bm n)` using `Finset.sum_nonneg fun n _ => add_nonneg (hBp0 n) (hBm0 n)`.

Establish `hB0 : 0 ≤ B` using `by positivity`. Establish `hBpB : ∀ n, Bp n ≤ B` using `fun n => by`. Use `Finset.single_le_sum (f := fun n => Bp n + Bm n) (fun n _ => add_nonneg (hBp0 n) (hBm0 n)) (Finset.mem_univ n)` as an intermediate fact. Combine the linear relations using `[hBm0 n]`. Establish `hBmB : ∀ n, Bm n ≤ B` using `fun n => by`.

Use `Finset.single_le_sum (f := fun n => Bp n + Bm n) (fun n _ => add_nonneg (hBp0 n) (hBm0 n)) (Finset.mem_univ n)` as an intermediate fact. Combine the linear relations using `[hBp0 n]`. Establish `hBhB : Bh ≤ B` using `by linarith`. Establish `hBh'B : Bh' ≤ B` using `by linarith`. Use `choose Cw hCw using fun n : Fin 3 → Fin (2 * j + 1) => hWDa (List.ofFn fun a => grid a (n a)) (by simp) (hgr n).1`.

Take `⟨C0, hC0⟩` from `hWDa [] (by simp) hw`. Use `set CW := |C0| + ∑ n, |Cw n| with hCWdef`. Establish `hCW0 : 0 ≤ CW` using `by positivity`. Establish `hCwW : ∀ n, Cw n ≤ CW` using `fun n => by`. Use `Finset.single_le_sum (f := fun n => |Cw n|) (fun n _ => abs_nonneg _) (Finset.mem_univ n)` as an intermediate fact.

Combine the linear relations using `[le_abs_self (Cw n), abs_nonneg C0]`. Establish `hC0W : C0 ≤ CW`. Combine the linear relations using `[le_abs_self C0, Finset.sum_nonneg (fun n (_ : n ∈ Finset.univ) => abs_nonneg (Cw n))]`. Use `set K := ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| / Real.sqrt (((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod) with hKdef`. Establish `hK : 0 ≤ K` using `Finset.sum_nonneg fun n _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)`.

Use `set T1 := 8 * (1 + K) * Real.sqrt (B * B) with hT1`. Establish `hT10 : 0 ≤ T1` using `by positivity`. Establish `hxi : ∀ m s, ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2)) (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ T1 * ((1 + ‖s‖) ^ 3)⁻¹`. Introduce `m s`. Use `xi_bound hP P p (fun g => cut m g • D.cutF p.T.base χ f ε g) (hcpt m) j hj w hw h h' hh hh' grid hinj hgr LinearMap.id (fun ε x hx => hx) (fun x hx => hx) B B ?_ ?_ ?_ ?_ s` and prove the remaining obligations.

Use `show ‖p.form j hj w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2) (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2)‖ ≤ B`. Rewrite using `[← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh]`. Conclude with `(hBh m).trans hBhB`. Rewrite using `[← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh']`. Conclude with `(hBh' m).trans hBh'B`.

Introduce `n`. Rewrite using `[onOld_eq_self (w := w) (⇑(LinearMap.id (R := ℂ) (M := Wd.Ix (Fin w.length) → FourierDecayAlt.B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))) (fun x => rfl), ← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj _ h hh]`. Conclude with `(hBp n m).trans (hBpB n)`. Introduce `n`. Rewrite using `[← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj _ h' hh']`.

Conclude with `(hBm n m).trans (hBmB n)`. Use `set I3 := ∫ s : ℂ, ((1 + ‖s‖) ^ 3)⁻¹ with hI3`. Establish `hI30 : 0 ≤ I3` using `integral_nonneg fun s => by positivity`. Use `set C := T1 + 8 * T1 * I3 + (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3 with hCdef`. Establish `hX3 : 0 ≤ (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3` using `by positivity`.

Establish `hT8 : 0 ≤ 8 * T1 * I3` using `mul_nonneg (mul_nonneg (by norm_num) hT10) hI30`. Establish `hC1 : T1 ≤ C` using `by rw [hCdef]; linarith only [hX3, hT8]`. Use `clear_value C I3 T1 K CW B`. Use `⟨C, fun m => ⟨fun c hc => ?_, fun s => ?_⟩⟩` and prove the remaining obligations. Use `swap`.

Establish `hs0 : (0 : ℝ) ≤ ((1 + ‖s‖) ^ 3)⁻¹` using `inv_nonneg.2 (pow_nonneg (by positivity) 3)`. Conclude with `(hxi m s).trans (mul_le_mul_of_nonneg_right hC1 hs0)`. Take `⟨φ, hφc, hφi, hφeq, hφs⟩` from `pStdCpt_of_heads hP hRH hHT Wp Wq P p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h h' hh hh' Cb hθ (hcpt m) hw`. Rewrite using `[← hφeq c hc]`. Establish `hΞ : ∀ s, ‖∫ t, fsv s t * φ t‖ ≤ T1 * ((1 + ‖s‖) ^ 3)⁻¹` using `fun s => by rw [hφs s]; exact hxi m s`.

Take `⟨hΞi, hΞI⟩` from `integral_norm_le_decay (continuous_transform hφc hφi) hΞ`. Establish `hφle` using `norm_le_integral_fsv φ hφc hφi hΞi c`. Establish `hu : 0 < 1 + ‖c‖` using `by positivity`. Rewrite using `[← div_eq_mul_inv, le_div_iff₀ (pow_pos hu 3)]`. Distinguish the cases in `hc1 : ‖c‖ ≤ 1`.

Establish `hu8 : (1 + ‖c‖) ^ 3 ≤ 8`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : ‖φ c‖ ≤ T1 * I3` using `hφle.trans (by rw [hI3]; exact hΞI)`. Establish `hTI : 0 ≤ T1 * I3` using `mul_nonneg hT10 hI30`. Combine the equalities or inequalities in the displayed calculation.

Use `push Not at hc1`. Take `⟨hfσ, hσn⟩` from `fsv_sigma hc`. Use `set σ := Complex.I * (Real.pi : ℂ) / (2 * c) with hσdef`. Establish `hc0 : 0 < ‖c‖` using `by linarith`. Establish `hσ2 : ‖σ‖ ≤ 2`.

Rewrite using `[hσn, div_le_iff₀ (by linarith only [hc0])]`. Combine the linear relations using `only [Real.pi_le_four, hc1]`. Use `clear_value σ`. Establish `hxc : ∀ e, KB.CptCoef (p.T.bs j) ((KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2) e)` using `fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p _ j hj w h hh (hcpt m) e`. Establish `hyc : ∀ e, KB.CptCoef (p.T.bs j) ((KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2) e)` using `fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p _ j hj w h' hh' (hcpt m) e`.

Establish `hfc : Continuous (fun t => (fsv σ t - 1) ^ 3)` using `((continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).sub continuous_const).pow 3`. Establish `hψc : Continuous (fun t => (fsv σ t - 1) ^ 3 * φ t)` using `hfc.mul hφc`. Establish `hψi : Integrable (fun t => (fsv σ t - 1) ^ 3 * φ t)` using `hφi.bdd_mul (c := 8) hfc.aestronglyMeasurable (Filter.Eventually.of_forall fun t => norm_fsv_sub_one_pow σ t)`. Establish `hσ6 : 0 ≤ ‖σ‖ ^ 6` using `pow_nonneg (norm_nonneg _) 6`. Establish `hΨb : ∀ s, ‖∫ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t)‖ ≤ (8 * (1 + K) * Real.sqrt (CW * ‖σ‖ ^ 6 * B)) * ((1 + ‖s‖) ^ 3)⁻¹`.

Introduce `s`. Rewrite using `[transform_diff3 hφc hφi σ s, hφs, hφs, hφs, hφs, ← form_wave_mDiff P p j hj w _ _ hxc hyc s σ]`. Establish `hA0 : ‖p.form j hj w (mDiff (p.T.bs j) σ w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2)) (mDiff (p.T.bs j) σ w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2))‖ ≤ CW * ‖σ‖ ^ 6` using `(hC0 m σ hσ2).trans (mul_le_mul_of_nonneg_right hC0W hσ6)`. Establish `hB0' : ‖p.form j hj w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2) (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ B`. Rewrite using `[← rr_eq_form p _ j hj w h' hh']`.

Conclude with `(hBh' m).trans hBh'B`. Establish `key` using `xi_bound hP P p _ (hcpt m) j hj w hw h h' hh hh' grid hinj hgr (mDiff (p.T.bs j) σ w) (fun ε x hx => mDiff_nice _ σ w ε x hx) (fun x hx => mDiff_cpt hP P p j hj w hw σ x hx) (CW * ‖σ‖ ^ 6) B hA0 hB0' (fun n => (hCw n m σ hσ2).trans (mul_le_mul_of_nonneg_right (hCwW n) hσ6)) (fun …`. Rewrite `key` using `[← hKdef]`. Conclude with `key`. Take `⟨hΨi, hΨI⟩` from `integral_norm_le_decay (continuous_transform hψc hψi) hΨb`.

Establish `hψle` using `norm_le_integral_fsv _ hψc hψi hΨi c`. Establish `hψc' : ‖(fsv σ c - 1) ^ 3 * φ c‖ = 8 * ‖φ c‖`. Rewrite using `[hfσ, norm_mul]`. Evaluate the numerical expressions. Establish `hsq : Real.sqrt (CW * ‖σ‖ ^ 6 * B) = ‖σ‖ ^ 3 * Real.sqrt (CW * B)`.

Rewrite using `[show CW * ‖σ‖ ^ 6 * B = (‖σ‖ ^ 3) ^ 2 * (CW * B) by ring, Real.sqrt_mul (pow_nonneg (pow_nonneg (norm_nonneg _) 3) 2), Real.sqrt_sq (pow_nonneg (norm_nonneg _) 3)]`. Establish `h1 : 8 * ‖φ c‖ ≤ 8 * (1 + K) * (‖σ‖ ^ 3 * Real.sqrt (CW * B)) * I3`. Rewrite using `[← hψc', ← hsq, hI3]`. Conclude with `hψle.trans hΨI`. Establish `h2 : ‖φ c‖ ≤ (1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3` using `by linarith only [h1]`.

Establish `hu8 : (1 + ‖c‖) ^ 3 ≤ 8 * ‖c‖ ^ 3`. Combine the equalities or inequalities in the displayed calculation. Establish `hπ : ‖σ‖ ^ 3 * (8 * ‖c‖ ^ 3) = Real.pi ^ 3`. Establish `hc3 : (2 : ℝ) ^ 3 * ‖c‖ ^ 3 ≠ 0` using `(mul_pos (by norm_num) (pow_pos hc0 3)).ne'`. Rewrite using `[hσn, div_pow, mul_pow, div_mul_eq_mul_div, mul_div_assoc, show (8 : ℝ) * ‖c‖ ^ 3 / (2 ^ 3 * ‖c‖ ^ 3) = 1 by rw [div_eq_one_iff_eq hc3]; norm_num, mul_one]`.

Establish `hK1 : (0 : ℝ) ≤ 1 + K` using `by linarith only [hK]`. Establish `hs3 : (0 : ℝ) ≤ ‖σ‖ ^ 3` using `pow_nonneg (norm_nonneg σ) 3`. Establish `hQ4 : 0 ≤ (1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3` using `mul_nonneg (mul_nonneg (mul_nonneg hK1 (Real.sqrt_nonneg (CW * B))) hs3) hI30`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem decayUnif_of (hRH : KB.RadHead) (hHT : KB.HeadTop) (hWDF : WaveDiffForm) : DecayUnif := by
  intro hP Cb
  obtain ⟨CcF, hFL⟩ := Formalism.FourierDecayAlt.P.limit_of_module_forms Cb
  obtain ⟨CcW, hWD⟩ := hWDF hP Cb
  refine ⟨max CcF CcW, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f χ ε A N cut lo hi hθ hχ hε hf hfA hthr hcut hon hroom j hj w hw hN h h' hh hh'
  have hX : 0 ≤ ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) := by positivity
  have hthrF : CcF * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    have := mul_le_mul_of_nonneg_right (le_max_left CcF CcW) hX
    nlinarith
  have hthrW : CcW * ((P.r : ℝ) + 1) ^ 4 * (((N + 3 : ℕ) : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A := by
    have := mul_le_mul_of_nonneg_right (le_max_right CcF CcW) hX
    nlinarith
  obtain ⟨hcpt, hlim⟩ := hFL Wp Wq P p f χ ε A (N + 3) cut hθ hχ hε hf hfA hthrF hcut
  have hWDa := hWD Wp Wq P p f χ ε A N cut hθ hχ hε hf hfA hthrW hcut j hj w hw hN h hh

  obtain ⟨grid, hinj, hgr⟩ := grid_exists P p.l0 lo hi hon w hw j (by
    have h1 : (w.length : ℝ) ≤ N := by exact_mod_cast hN
    have h2 : (j : ℝ) ≤ P.r := by exact_mod_cast hj
    nlinarith)
  have hlp : ∀ n : Fin 3 → Fin (2 * j + 1), (KB.plusW (List.ofFn fun a => grid a (n a)) w).length ≤ N + 3 := by
    intro n; rw [Formalism.FourierDecayAlt.P.PBD.plusW_eq]; simp; omega
  have hlm : ∀ n : Fin 3 → Fin (2 * j + 1), (KB.minusW (List.ofFn fun a => grid a (n a)) w).length ≤ N + 3 := by
    intro n; rw [Formalism.FourierDecayAlt.P.PBD.minusW_eq]; simp; omega

  have bnd : ∀ (w' : List C.Letter), KB.CutWord P p.l0 w' → w'.length ≤ N + 3 → ∀ a : C.LPt,
      ∃ B, 0 ≤ B ∧ ∀ n, ‖p.RR (fun g => cut n g • D.cutF p.T.base χ f ε g) j w' a a‖ ≤ B :=
    fun w' hw' hl a => bdd_of_tendsto (hlim j w' hw' hl a a)
  choose Bp hBp0 hBp using fun n => bnd _ (hgr n).1 (hlp n) h
  choose Bm hBm0 hBm using fun n => bnd _ (hgr n).2.1 (hlm n) h'
  obtain ⟨Bh, hBh0, hBh⟩ := bnd w hw (by omega) h
  obtain ⟨Bh', hBh'0, hBh'⟩ := bnd w hw (by omega) h'
  set B := Bh + Bh' + ∑ n, (Bp n + Bm n) with hBdef
  have hS0 : 0 ≤ ∑ n, (Bp n + Bm n) := Finset.sum_nonneg fun n _ => add_nonneg (hBp0 n) (hBm0 n)
  have hB0 : 0 ≤ B := by positivity
  have hBpB : ∀ n, Bp n ≤ B := fun n => by
    have := Finset.single_le_sum (f := fun n => Bp n + Bm n) (fun n _ => add_nonneg (hBp0 n) (hBm0 n))
      (Finset.mem_univ n)
    linarith [hBm0 n]
  have hBmB : ∀ n, Bm n ≤ B := fun n => by
    have := Finset.single_le_sum (f := fun n => Bp n + Bm n) (fun n _ => add_nonneg (hBp0 n) (hBm0 n))
      (Finset.mem_univ n)
    linarith [hBp0 n]
  have hBhB : Bh ≤ B := by linarith
  have hBh'B : Bh' ≤ B := by linarith

  choose Cw hCw using fun n : Fin 3 → Fin (2 * j + 1) => hWDa (List.ofFn fun a => grid a (n a)) (by simp)
    (hgr n).1
  obtain ⟨C0, hC0⟩ := hWDa [] (by simp) hw
  set CW := |C0| + ∑ n, |Cw n| with hCWdef
  have hCW0 : 0 ≤ CW := by positivity
  have hCwW : ∀ n, Cw n ≤ CW := fun n => by
    have := Finset.single_le_sum (f := fun n => |Cw n|) (fun n _ => abs_nonneg _) (Finset.mem_univ n)
    linarith [le_abs_self (Cw n), abs_nonneg C0]
  have hC0W : C0 ≤ CW := by
    linarith [le_abs_self C0, Finset.sum_nonneg (fun n (_ : n ∈ Finset.univ) => abs_nonneg (Cw n))]

  set K := ∑ n : Fin 3 → Fin (2 * j + 1), |∏ a, F7.lagCo (grid a) (n a)| /
        Real.sqrt (((List.ofFn fun a => grid a (n a)).map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod)
    with hKdef
  have hK : 0 ≤ K := Finset.sum_nonneg fun n _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  set T1 := 8 * (1 + K) * Real.sqrt (B * B) with hT1
  have hT10 : 0 ≤ T1 := by positivity
  have hxi : ∀ m s, ‖p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2))
      (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ T1 * ((1 + ‖s‖) ^ 3)⁻¹ := by
    intro m s
    refine xi_bound hP P p (fun g => cut m g • D.cutF p.T.base χ f ε g) (hcpt m) j hj w hw h h' hh hh' grid hinj hgr LinearMap.id
      (fun ε x hx => hx) (fun x hx => hx) B B ?_ ?_ ?_ ?_ s
    · show ‖p.form j hj w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2) (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2)‖ ≤ B
      rw [← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh]; exact (hBh m).trans hBhB
    · rw [← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh']; exact (hBh' m).trans hBh'B
    · intro n
      rw [onOld_eq_self (w := w) (⇑(LinearMap.id (R := ℂ)
        (M := Wd.Ix (Fin w.length) → FourierDecayAlt.B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)))) (fun x => rfl), ← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj _ h hh]
      exact (hBp n m).trans (hBpB n)
    · intro n
      rw [← rr_eq_form p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj _ h' hh']
      exact (hBm n m).trans (hBmB n)
  set I3 := ∫ s : ℂ, ((1 + ‖s‖) ^ 3)⁻¹ with hI3
  have hI30 : 0 ≤ I3 := integral_nonneg fun s => by positivity
  set C := T1 + 8 * T1 * I3 + (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3 with hCdef
  have hX3 : 0 ≤ (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3 := by positivity
  have hT8 : 0 ≤ 8 * T1 * I3 := mul_nonneg (mul_nonneg (by norm_num) hT10) hI30
  have hC1 : T1 ≤ C := by rw [hCdef]; linarith only [hX3, hT8]
  clear_value C I3 T1 K CW B
  refine ⟨C, fun m => ⟨fun c hc => ?_, fun s => ?_⟩⟩
  swap
  · have hs0 : (0 : ℝ) ≤ ((1 + ‖s‖) ^ 3)⁻¹ := inv_nonneg.2 (pow_nonneg (by positivity) 3)
    exact (hxi m s).trans (mul_le_mul_of_nonneg_right hC1 hs0)
  obtain ⟨φ, hφc, hφi, hφeq, hφs⟩ := pStdCpt_of_heads hP hRH hHT Wp Wq P p (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h h' hh hh' Cb hθ
    (hcpt m) hw
  rw [← hφeq c hc]
  have hΞ : ∀ s, ‖∫ t, fsv s t * φ t‖ ≤ T1 * ((1 + ‖s‖) ^ 3)⁻¹ := fun s => by rw [hφs s]; exact hxi m s
  obtain ⟨hΞi, hΞI⟩ := integral_norm_le_decay (continuous_transform hφc hφi) hΞ
  have hφle := norm_le_integral_fsv φ hφc hφi hΞi c
  have hu : 0 < 1 + ‖c‖ := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hu 3)]
  by_cases hc1 : ‖c‖ ≤ 1
  · have hu8 : (1 + ‖c‖) ^ 3 ≤ 8 := by
      calc (1 + ‖c‖) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hu.le (by linarith) 3
        _ = 8 := by norm_num
    have h1 : ‖φ c‖ ≤ T1 * I3 := hφle.trans (by rw [hI3]; exact hΞI)
    have hTI : 0 ≤ T1 * I3 := mul_nonneg hT10 hI30
    calc ‖φ c‖ * (1 + ‖c‖) ^ 3 ≤ (T1 * I3) * 8 := mul_le_mul h1 hu8 (pow_nonneg hu.le 3) hTI
      _ = 8 * T1 * I3 := by ring
      _ ≤ C := by rw [hCdef]; linarith only [hX3, hT10]
  · push Not at hc1
    obtain ⟨hfσ, hσn⟩ := fsv_sigma hc
    set σ := Complex.I * (Real.pi : ℂ) / (2 * c) with hσdef
    have hc0 : 0 < ‖c‖ := by linarith
    have hσ2 : ‖σ‖ ≤ 2 := by
      rw [hσn, div_le_iff₀ (by linarith only [hc0])]
      linarith only [Real.pi_le_four, hc1]
    clear_value σ
    have hxc : ∀ e, KB.CptCoef (p.T.bs j) ((KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2) e) := fun e =>
      Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p _ j hj w h hh (hcpt m) e
    have hyc : ∀ e, KB.CptCoef (p.T.bs j) ((KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2) e) := fun e =>
      Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p _ j hj w h' hh' (hcpt m) e
    have hfc : Continuous (fun t => (fsv σ t - 1) ^ 3) :=
      ((continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).sub continuous_const).pow 3
    have hψc : Continuous (fun t => (fsv σ t - 1) ^ 3 * φ t) := hfc.mul hφc
    have hψi : Integrable (fun t => (fsv σ t - 1) ^ 3 * φ t) :=
      hφi.bdd_mul (c := 8) hfc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => norm_fsv_sub_one_pow σ t)
    have hσ6 : 0 ≤ ‖σ‖ ^ 6 := pow_nonneg (norm_nonneg _) 6
    have hΨb : ∀ s, ‖∫ t, fsv s t * ((fsv σ t - 1) ^ 3 * φ t)‖ ≤
        (8 * (1 + K) * Real.sqrt (CW * ‖σ‖ ^ 6 * B)) * ((1 + ‖s‖) ^ 3)⁻¹ := by
      intro s
      rw [transform_diff3 hφc hφi σ s, hφs, hφs, hφs, hφs, ← form_wave_mDiff P p j hj w _ _ hxc hyc s σ]
      have hA0 : ‖p.form j hj w (mDiff (p.T.bs j) σ w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2)) (mDiff (p.T.bs j) σ w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h hh.2))‖ ≤ CW * ‖σ‖ ^ 6 :=
        (hC0 m σ hσ2).trans (mul_le_mul_of_nonneg_right hC0W hσ6)
      have hB0' : ‖p.form j hj w (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2) (KB.slv p.T (fun g => cut m g • D.cutF p.T.base χ f ε g) j hj w h' hh'.2)‖ ≤ B := by
        rw [← rr_eq_form p _ j hj w h' hh']; exact (hBh' m).trans hBh'B
      have key := xi_bound hP P p _ (hcpt m) j hj w hw h h' hh hh' grid hinj hgr (mDiff (p.T.bs j) σ w)
        (fun ε x hx => mDiff_nice _ σ w ε x hx) (fun x hx => mDiff_cpt hP P p j hj w hw σ x hx)
        (CW * ‖σ‖ ^ 6) B hA0 hB0'
        (fun n => (hCw n m σ hσ2).trans (mul_le_mul_of_nonneg_right (hCwW n) hσ6))
        (fun n => by rw [← rr_eq_form p _ j hj _ h' hh']; exact (hBm n m).trans (hBmB n)) s
      rw [← hKdef] at key
      exact key
    obtain ⟨hΨi, hΨI⟩ := integral_norm_le_decay (continuous_transform hψc hψi) hΨb
    have hψle := norm_le_integral_fsv _ hψc hψi hΨi c
    have hψc' : ‖(fsv σ c - 1) ^ 3 * φ c‖ = 8 * ‖φ c‖ := by
      rw [hfσ, norm_mul]; norm_num
    have hsq : Real.sqrt (CW * ‖σ‖ ^ 6 * B) = ‖σ‖ ^ 3 * Real.sqrt (CW * B) := by
      rw [show CW * ‖σ‖ ^ 6 * B = (‖σ‖ ^ 3) ^ 2 * (CW * B) by ring, Real.sqrt_mul (pow_nonneg (pow_nonneg (norm_nonneg _) 3) 2),
        Real.sqrt_sq (pow_nonneg (norm_nonneg _) 3)]
    have h1 : 8 * ‖φ c‖ ≤ 8 * (1 + K) * (‖σ‖ ^ 3 * Real.sqrt (CW * B)) * I3 := by
      rw [← hψc', ← hsq, hI3]; exact hψle.trans hΨI
    have h2 : ‖φ c‖ ≤ (1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3 := by linarith only [h1]
    have hu8 : (1 + ‖c‖) ^ 3 ≤ 8 * ‖c‖ ^ 3 := by
      calc (1 + ‖c‖) ^ 3 ≤ (2 * ‖c‖) ^ 3 := pow_le_pow_left₀ hu.le (by linarith only [hc1]) 3
        _ = 8 * ‖c‖ ^ 3 := by ring
    have hπ : ‖σ‖ ^ 3 * (8 * ‖c‖ ^ 3) = Real.pi ^ 3 := by
      have hc3 : (2 : ℝ) ^ 3 * ‖c‖ ^ 3 ≠ 0 := (mul_pos (by norm_num) (pow_pos hc0 3)).ne'
      rw [hσn, div_pow, mul_pow, div_mul_eq_mul_div, mul_div_assoc,
        show (8 : ℝ) * ‖c‖ ^ 3 / (2 ^ 3 * ‖c‖ ^ 3) = 1 by rw [div_eq_one_iff_eq hc3]; norm_num, mul_one]
    have hK1 : (0 : ℝ) ≤ 1 + K := by linarith only [hK]
    have hs3 : (0 : ℝ) ≤ ‖σ‖ ^ 3 := pow_nonneg (norm_nonneg σ) 3
    have hQ4 : 0 ≤ (1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3 :=
      mul_nonneg (mul_nonneg (mul_nonneg hK1 (Real.sqrt_nonneg (CW * B))) hs3) hI30
    calc ‖φ c‖ * (1 + ‖c‖) ^ 3 ≤ ((1 + K) * Real.sqrt (CW * B) * ‖σ‖ ^ 3 * I3) * (8 * ‖c‖ ^ 3) :=
          mul_le_mul h2 hu8 (pow_nonneg hu.le 3) hQ4
      _ = (1 + K) * Real.sqrt (CW * B) * I3 * (‖σ‖ ^ 3 * (8 * ‖c‖ ^ 3)) := by ring
      _ = (1 + K) * Real.sqrt (CW * B) * I3 * Real.pi ^ 3 := by rw [hπ]
      _ ≤ C := by rw [hCdef]; linarith only [hT10, hT8]

end Formalism.FourierDecayAlt.P.PBO
