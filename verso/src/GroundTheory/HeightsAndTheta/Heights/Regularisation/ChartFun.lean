import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContinuousTmaxShift
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsChartBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier tmax regMax le_tmax tmax_le regMax_ge regMax_le)

noncomputable section

namespace LogLogRegularisation

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : ReciprocityTheory.AnForm.M.FinHolAtlas D X}

open Classical in

/- English proof (translation)
Unfold `PotentialCharts.glue`. Conclude with `le_add_of_le_of_nonneg ((le_tmax (fun i : {i // x ∈ P.mid i} => a i x) ⟨j, hx⟩).trans (regMax_ge ε _)) (by linarith)`.
-/
theorem le_glue (P : PotentialCharts A) (a : Fin P.N → X → ℝ) {ε : ℝ} (hε : 0 ≤ ε) {x : X}
    {j : Fin P.N} (hx : x ∈ P.mid j) : a j x ≤ P.glue a ε x := by
  unfold PotentialCharts.glue
  exact le_add_of_le_of_nonneg
    ((le_tmax (fun i : {i // x ∈ P.mid i} => a i x) ⟨j, hx⟩).trans (regMax_ge ε _)) (by linarith)

open Classical in

/- English proof (translation)
Unfold `PotentialCharts.glue`. Establish `h1` using `regMax_le hε (fun i : {i // x ∈ P.mid i} => a i x)`. Establish `h2 : tmax (fun i : {i // x ∈ P.mid i} => a i x) ≤ c` using `tmax_le fun i => h i.1 i.2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem glue_le (P : PotentialCharts A) (a : Fin P.N → X → ℝ) {ε c : ℝ} (hε : 0 ≤ ε) {x : X}
    (h : ∀ j, x ∈ P.mid j → a j x ≤ c) : P.glue a ε x ≤ c + ε := by
  unfold PotentialCharts.glue
  have h1 := regMax_le hε (fun i : {i // x ∈ P.mid i} => a i x)
  have h2 : tmax (fun i : {i // x ∈ P.mid i} => a i x) ≤ c := tmax_le fun i => h i.1 i.2
  linarith

/- English proof (translation)
Introduce `X _ _ _ D A R`. Take `⟨ρ⟩` from `ReciprocityTheory.AnForm.A.mollifierInhabit_thm D`. Take `⟨C1, t1, ht1, hC1⟩` from `h1 X D A R ρ`. Take `⟨C2, t2, ht2, hC2⟩` from `h2 X D A R ρ`. Take `⟨η, Cη, hη⟩` from `h3 X D A R.toPotentialCharts`.

Take `⟨C4, t4, ht4, hC4⟩` from `h4 X D A R ρ`. Take `⟨L, hL⟩` from `eventually_atTop.1 ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C2 (1 / 6) (by norm_num)).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (|C2| + 1) by positivity)))`. Use `set E : ℝ := |C1| + 1 with hE`. Use `set Cup : ℝ := |C4| + 2 * E with hCup`. Use `set C : ℝ := Cup + (|C1| + |C2| + |C4|) + 8 * |Cη| * E + 2 * E + |R.Clog| with hC`.

Establish `hE0 : 0 ≤ E` using `by positivity`. Establish `hCup0 : 0 ≤ Cup` using `by positivity`. Use `⟨C, max (max L (Real.exp 1)) (max (-Real.log t1) (max (-Real.log t2) (-Real.log t4)) + 1), fun t ht hℓ => ?_⟩` and prove the remaining obligations. Use `set ℓ := Real.log t⁻¹ with hℓdef`. Establish `hℓL : L ≤ ℓ` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hℓ`.

Establish `hℓe : Real.exp 1 ≤ ℓ` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hℓ`. Establish `hℓt : max (-Real.log t1) (max (-Real.log t2) (-Real.log t4)) + 1 ≤ ℓ` using `le_trans (le_max_right _ _) hℓ`. Establish `hℓ0 : 0 < ℓ` using `(Real.exp_pos 1).trans_le hℓe`. Establish `hlogt : Real.log t = -ℓ` using `by rw [hℓdef, Real.log_inv, neg_neg]`. Establish `hlt : ∀ s, 0 < s → -Real.log s + 1 ≤ ℓ → t < s` using `fun s hs h => (Real.log_lt_log_iff ht hs).1 (by linarith)`.

Establish `htt1 : t < t1` using `hlt t1 ht1 (le_trans (by simp) hℓt)`. Establish `htt2 : t < t2` using `hlt t2 ht2 (le_trans (by simp) hℓt)`. Establish `htt4 : t < t4` using `hlt t4 ht4 (le_trans (by simp) hℓt)`. Establish `hlog1 : 1 ≤ Real.log ℓ`. Rewrite using `[Real.le_log_iff_exp_le hℓ0]`.

Conclude with `hℓe`. Use `set q := Real.log ℓ / ℓ with hqdef`. Establish `hq0 : 0 ≤ q` using `div_nonneg (by linarith) hℓ0.le`. Establish `hq1 : q ≤ 1` using `(div_le_one hℓ0).2 (by linarith [Real.log_le_sub_one_of_pos hℓ0])`. Establish `htexp : t = Real.exp (-ℓ)` using `by rw [← hlogt, Real.exp_log ht]`.

Establish `htq : t ≤ q`. Rewrite using `[htexp, Real.exp_neg, hqdef]`. Rewrite using `[inv_le_iff_one_le_mul₀ (Real.exp_pos ℓ)]`. Establish `h5 : ℓ + 1 ≤ Real.exp ℓ` using `Real.add_one_le_exp ℓ`. Establish `h6 : 1 ≤ Real.exp ℓ * (Real.log ℓ / ℓ)`.

Rewrite using `[mul_div_assoc', le_div_iff₀ hℓ0, one_mul]`. Use `le_mul_of_one_le_right (Real.exp_pos ℓ).le hlog1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[mul_comm]`. Conclude with `h6`.

Establish `hCq : ∀ c : ℝ, c * Real.log ℓ / ℓ = c * q` using `fun c => by rw [hqdef, mul_div_assoc]`. Use `set K : ℝ := (|C1| + |C2|) * Real.log ℓ with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`. Establish `hlog0 : 0 ≤ Real.log ℓ` using `by linarith`. Establish `hK1 : C1 * Real.log ℓ ≤ K`.

Use `mul_le_mul_of_nonneg_right (le_abs_self C1) hlog0` as an intermediate fact. Use `mul_nonneg (abs_nonneg C2) hlog0` as an intermediate fact. Rewrite using `[hK]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hK2 : C2 * Real.log ℓ ≤ K`.

Use `mul_le_mul_of_nonneg_right (le_abs_self C2) hlog0` as an intermediate fact. Use `mul_nonneg (abs_nonneg C1) hlog0` as an intermediate fact. Rewrite using `[hK]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set ε : ℝ := E * (q + t) with hεdef`.

Establish `hε : 0 < ε` using `by positivity`. Establish `hε2 : ε ≤ 2 * E * q`. Use `mul_le_mul_of_nonneg_left htq hE0` as an intermediate fact. Rewrite using `[hεdef]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hεE : ε ≤ 2 * E`. Use `mul_le_mul_of_nonneg_left hq1 hE0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hterm : 0 ≤ 8 * |Cη| * E` using `by positivity`. Establish `hClog0 : 0 ≤ |R.Clog|` using `abs_nonneg _`.

Establish `ha1` using `abs_nonneg C1`. Establish `ha2` using `abs_nonneg C2`. Establish `ha4` using `abs_nonneg C4`. Establish `hcomp : ∀ j k, ∀ x ∈ R.mid j ∩ R.mid k, |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤ ε`. Introduce `j k x hx`.

Use `(hC1 t ht htt1 K hK1 j k x hx).trans ?_` and prove the remaining obligations. Rewrite using `[hCq]`. Establish `hC1E : C1 ≤ E` using `by linarith [le_abs_self C1]`. Use `mul_le_mul_of_nonneg_right hC1E hq0` as an intermediate fact. Use `mul_le_mul_of_nonneg_right hC1E ht.le` as an intermediate fact.

Rewrite using `[hεdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hball, hbd⟩` from `hC4 t ht htt4`. Take `⟨hsmooth, hlevi⟩` from `h0 X D A R ρ η Cη K t ε hη ht hε hball hcomp`. Use `set φt := R.regularised ρ K t ε η with hφt`.

Establish `harg : ∀ j x, x ∈ R.mid j → R.phReg ρ K t j x + 4 * ε * η j x ≤ R.phReg ρ K t j x` using `fun j x hx => by`. Use `mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * ε) (hη.bounds j x hx).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hup : ∀ x, φt x ≤ Cup`. Introduce `x`.

Use `(glue_le R.toPotentialCharts _ hε.le (c := C4) fun j hx => (harg j x hx).trans (hbd K hK0 j x hx).2.1).trans ?_` and prove the remaining obligations. Rewrite using `[hCup]`. Combine the linear relations using `[le_abs_self C4]`. Establish `hlow : ∀ x, ∃ k, x ∈ R.mid k ∧ R.phReg ρ K t k x ≤ φt x`. Introduce `x`.

Take `⟨k, hk⟩` from `R.cover x`. Establish `hkm` using `R.inner_subset_mid k hk`. Use `⟨k, hkm, ?_⟩` and prove the remaining obligations. Use `le_glue R.toPotentialCharts (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) hε.le hkm` as an intermediate fact. Establish `e : φt x = R.glue (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) ε x` using `rfl`.

Rewrite using `[e]`. Simplify `this` using `[hη.eq_zero k x hk]`. Establish `hCbig : |C1| + |C2| + |C4| ≤ C`. Rewrite using `[hC]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hC0 : 0 ≤ C` using `le_trans (by positivity) hCbig`. Establish `hd1 : ∀ x ∈ R.Yo, R.r x ≤ ℓ → φt x ≤ R.ph x + t ^ (1 / 3 : ℝ) + C * q`. Introduce `x hxY hr`. Establish `hnear : ∀ j, x ∈ R.mid j → R.phReg ρ K t j x + 4 * ε * η j x ≤ R.ph x + C2 * ℓ ^ C2 * t ^ (1 / 2 : ℝ)`. Introduce `j hx`.

Use `(harg j x hx).trans ?_` and prove the remaining obligations. Establish `h` using `hC2 t ht htt2 K hK2 j x ⟨hx, hxY⟩ hr`. Establish `hsrc` using `R.mid_subset_source j hx`. Simplify using `only [RegChartData.u, PotentialCharts.chartFun, (R.chart j).left_inv hsrc] at h`. Simplify using `only [RegChartData.phReg]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hg` using `glue_le R.toPotentialCharts (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) hε.le hnear`. Establish `e : φt x = R.glue (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) ε x` using `rfl`. Rewrite `hg` using `[← e]`. Establish `h16 : t ^ (1 / 6 : ℝ) = Real.exp (-(1 / 6) * ℓ)`.

Rewrite using `[Real.rpow_def_of_pos ht, hlogt]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hsplit : t ^ (1 / 2 : ℝ) = t ^ (1 / 3 : ℝ) * t ^ (1 / 6 : ℝ)`. Rewrite using `[← Real.rpow_add ht]`.

Evaluate the numerical expressions. Establish `hP` using `hL ℓ hℓL`. Use `set P := ℓ ^ C2 * Real.exp (-(1 / 6) * ℓ) with hPdef`. Establish `hP0 : 0 ≤ P` using `mul_nonneg (Real.rpow_nonneg hℓ0.le _) (Real.exp_pos _).le`. Establish `hCP : C2 * P ≤ 1`.

Establish `h7 : |C2| * P ≤ |C2| * (1 / (|C2| + 1))` using `mul_le_mul_of_nonneg_left hP.le (abs_nonneg _)`. Establish `h8 : |C2| * (1 / (|C2| + 1)) ≤ 1`. Rewrite using `[mul_one_div, div_le_one (by positivity)]; linarith`. Use `mul_le_mul_of_nonneg_right (le_abs_self C2) hP0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h13 : 0 ≤ t ^ (1 / 3 : ℝ)` using `Real.rpow_nonneg ht.le _`. Establish `hkey : C2 * ℓ ^ C2 * t ^ (1 / 2 : ℝ) ≤ t ^ (1 / 3 : ℝ)`. Rewrite using `[hsplit, h16]`. Establish `: C2 * ℓ ^ C2 * (t ^ (1 / 3 : ℝ) * Real.exp (-(1 / 6) * ℓ)) = (C2 * P) * t ^ (1 / 3 : ℝ)` using `by rw [hPdef]; ring`. Rewrite using `[this]`.

Conclude with `mul_le_of_le_one_left h13 hCP`. Establish `hεC : ε ≤ C * q`. Use `hε2.trans (mul_le_mul_of_nonneg_right ?_ hq0)` and prove the remaining obligations. Rewrite using `[hC]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨φt, hsmooth, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hxY`. Take `⟨k, hk, hle⟩` from `hlow x`. Conclude with `((hbd K hK0 k x hk).2.2 hxY).trans hle`.

Introduce `x`. Conclude with `(hup x).trans (by rw [hC]; linarith)`. Introduce `x`. Take `⟨k, hk, hle⟩` from `hlow x`. Establish `h` using `(hbd K hK0 k x hk).1`.

Establish `h9` using `mul_le_mul_of_nonneg_right hCbig hlog0`. Establish `h10` using `le_mul_of_one_le_right (abs_nonneg C4) hlog1`. Establish `h11` using `le_abs_self C4`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `k x hx w`.

Use `le_trans ?_ (hlevi k x hx w)` and prove the remaining obligations. Rewrite using `[hCq]`. Establish `hw : 0 ≤ ‖w‖ ^ 2` using `by positivity`. Establish `h11 : 4 * Cη * ε ≤ 8 * |Cη| * E * q`. Establish `h12` using `mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cη] : 4 * Cη ≤ 4 * |Cη|) hε.le`.

Establish `h13` using `mul_le_mul_of_nonneg_left hε2 (by positivity : (0 : ℝ) ≤ 4 * |Cη|)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h14 : 8 * |Cη| * E * q ≤ C * q`. Use `mul_le_mul_of_nonneg_right ?_ hq0` and prove the remaining obligations. Rewrite using `[hC]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h15` using `mul_le_mul_of_nonneg_right (h11.trans h14) hw`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x hxY hr`. Rewrite using `[hCq]`.

Conclude with `hd1 x hxY hr`. Introduce `x hxY`. Rewrite using `[hCq]`. Establish `hr1` using `R.one_le_r x hxY`. Establish `hr0 : 0 < R.r x` using `by linarith`.

Establish `h13 : 0 ≤ t ^ (1 / 3 : ℝ)` using `Real.rpow_nonneg ht.le _`. Distinguish the cases in `hr : R.r x ≤ ℓ`. Use `hd1 x hxY hr` as an intermediate fact. Use `le_mul_of_one_le_right (mul_nonneg hC0 hq0) hr1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `push Not at hr`. Establish `hlogr : Real.log (R.r x) ≤ q * R.r x`. Establish `h15` using `Real.log_div_self_antitoneOn (Set.mem_Ici.2 hℓe) (Set.mem_Ici.2 (hℓe.trans hr.le)) hr.le`. Simplify using `only at h15`. Rewrite `h15` using `[div_le_iff₀ hr0]`.

Conclude with `h15`. Establish `hqr : 1 ≤ q * R.r x`. Establish `e1 : q * ℓ = Real.log ℓ` using `by rw [hqdef]; field_simp`. Use `mul_le_mul_of_nonneg_left hr.le hq0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hph` using `R.ph_ge x hxY`. Establish `hlr0 : 0 ≤ Real.log (R.r x)` using `Real.log_nonneg hr1`. Establish `h16 : -R.Clog * Real.log (R.r x) ≥ -|R.Clog| * Real.log (R.r x)`. Use `mul_le_mul_of_nonneg_right (le_abs_self R.Clog) hlr0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h17 : Cup + |R.Clog| * Real.log (R.r x) ≤ C * q * R.r x`. Establish `h18 : Cup ≤ Cup * (q * R.r x)` using `le_mul_of_one_le_right hCup0 hqr`. Establish `h19 : |R.Clog| * Real.log (R.r x) ≤ |R.Clog| * (q * R.r x)` using `mul_le_mul_of_nonneg_left hlogr (abs_nonneg _)`. Establish `h20 : Cup + |R.Clog| ≤ C`. Rewrite using `[hC]`.

Combine the linear relations using `[abs_nonneg C1, abs_nonneg C2, abs_nonneg C4]`. Establish `h21 : 0 ≤ q * R.r x` using `by positivity`. Use `mul_le_mul_of_nonneg_right h20 h21` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `hup x` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem proof (h0 : GlueRegularised.Statement) (h1 : ChartComparison.Statement)
    (h2 : MollifiedNearSmooth.Statement) (h3 : CutoffsExist.Statement)
    (h4 : ChartMollifiedBounds.Statement) : LogLogRegularisation.Statement := by
  intro X _ _ _ D A R
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm D
  obtain ⟨C1, t1, ht1, hC1⟩ := h1 X D A R ρ
  obtain ⟨C2, t2, ht2, hC2⟩ := h2 X D A R ρ
  obtain ⟨η, Cη, hη⟩ := h3 X D A R.toPotentialCharts
  obtain ⟨C4, t4, ht4, hC4⟩ := h4 X D A R ρ
  obtain ⟨L, hL⟩ := eventually_atTop.1 ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero C2 (1 / 6)
    (by norm_num)).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (|C2| + 1) by positivity)))
  set E : ℝ := |C1| + 1 with hE
  set Cup : ℝ := |C4| + 2 * E with hCup
  set C : ℝ := Cup + (|C1| + |C2| + |C4|) + 8 * |Cη| * E + 2 * E + |R.Clog| with hC
  have hE0 : 0 ≤ E := by positivity
  have hCup0 : 0 ≤ Cup := by positivity
  refine ⟨C, max (max L (Real.exp 1)) (max (-Real.log t1) (max (-Real.log t2) (-Real.log t4)) + 1),
    fun t ht hℓ => ?_⟩
  set ℓ := Real.log t⁻¹ with hℓdef
  have hℓL : L ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hℓ
  have hℓe : Real.exp 1 ≤ ℓ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hℓ
  have hℓt : max (-Real.log t1) (max (-Real.log t2) (-Real.log t4)) + 1 ≤ ℓ :=
    le_trans (le_max_right _ _) hℓ
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le hℓe
  have hlogt : Real.log t = -ℓ := by rw [hℓdef, Real.log_inv, neg_neg]
  have hlt : ∀ s, 0 < s → -Real.log s + 1 ≤ ℓ → t < s := fun s hs h =>
    (Real.log_lt_log_iff ht hs).1 (by linarith)
  have htt1 : t < t1 := hlt t1 ht1 (le_trans (by simp) hℓt)
  have htt2 : t < t2 := hlt t2 ht2 (le_trans (by simp) hℓt)
  have htt4 : t < t4 := hlt t4 ht4 (le_trans (by simp) hℓt)
  have hlog1 : 1 ≤ Real.log ℓ := by
    rw [Real.le_log_iff_exp_le hℓ0]; exact hℓe
  set q := Real.log ℓ / ℓ with hqdef
  have hq0 : 0 ≤ q := div_nonneg (by linarith) hℓ0.le
  have hq1 : q ≤ 1 := (div_le_one hℓ0).2 (by linarith [Real.log_le_sub_one_of_pos hℓ0])
  have htexp : t = Real.exp (-ℓ) := by rw [← hlogt, Real.exp_log ht]
  have htq : t ≤ q := by
    rw [htexp, Real.exp_neg, hqdef]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos ℓ)]
    have h5 : ℓ + 1 ≤ Real.exp ℓ := Real.add_one_le_exp ℓ
    have h6 : 1 ≤ Real.exp ℓ * (Real.log ℓ / ℓ) := by
      rw [mul_div_assoc', le_div_iff₀ hℓ0, one_mul]
      have := le_mul_of_one_le_right (Real.exp_pos ℓ).le hlog1
      linarith
    rw [mul_comm]; exact h6
  have hCq : ∀ c : ℝ, c * Real.log ℓ / ℓ = c * q := fun c => by rw [hqdef, mul_div_assoc]

  set K : ℝ := (|C1| + |C2|) * Real.log ℓ with hK
  have hK0 : 0 ≤ K := by positivity
  have hlog0 : 0 ≤ Real.log ℓ := by linarith
  have hK1 : C1 * Real.log ℓ ≤ K := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C1) hlog0
    have := mul_nonneg (abs_nonneg C2) hlog0
    rw [hK]; linarith
  have hK2 : C2 * Real.log ℓ ≤ K := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C2) hlog0
    have := mul_nonneg (abs_nonneg C1) hlog0
    rw [hK]; linarith
  set ε : ℝ := E * (q + t) with hεdef
  have hε : 0 < ε := by positivity
  have hε2 : ε ≤ 2 * E * q := by
    have := mul_le_mul_of_nonneg_left htq hE0
    rw [hεdef]; linarith
  have hεE : ε ≤ 2 * E := by
    have := mul_le_mul_of_nonneg_left hq1 hE0
    linarith
  have hterm : 0 ≤ 8 * |Cη| * E := by positivity
  have hClog0 : 0 ≤ |R.Clog| := abs_nonneg _
  have ha1 := abs_nonneg C1
  have ha2 := abs_nonneg C2
  have ha4 := abs_nonneg C4
  have hcomp : ∀ j k, ∀ x ∈ R.mid j ∩ R.mid k, |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤ ε := by
    intro j k x hx
    refine (hC1 t ht htt1 K hK1 j k x hx).trans ?_
    rw [hCq]
    have hC1E : C1 ≤ E := by linarith [le_abs_self C1]
    have := mul_le_mul_of_nonneg_right hC1E hq0
    have := mul_le_mul_of_nonneg_right hC1E ht.le
    rw [hεdef]; linarith
  obtain ⟨hball, hbd⟩ := hC4 t ht htt4
  obtain ⟨hsmooth, hlevi⟩ := h0 X D A R ρ η Cη K t ε hη ht hε hball hcomp
  set φt := R.regularised ρ K t ε η with hφt
  have harg : ∀ j x, x ∈ R.mid j → R.phReg ρ K t j x + 4 * ε * η j x ≤ R.phReg ρ K t j x :=
    fun j x hx => by
      have := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℝ) ≤ 4 * ε) (hη.bounds j x hx).2
      linarith
  have hup : ∀ x, φt x ≤ Cup := by
    intro x
    refine (glue_le R.toPotentialCharts _ hε.le (c := C4) fun j hx =>
      (harg j x hx).trans (hbd K hK0 j x hx).2.1).trans ?_
    rw [hCup]; linarith [le_abs_self C4]
  have hlow : ∀ x, ∃ k, x ∈ R.mid k ∧ R.phReg ρ K t k x ≤ φt x := by
    intro x
    obtain ⟨k, hk⟩ := R.cover x
    have hkm := R.inner_subset_mid k hk
    refine ⟨k, hkm, ?_⟩
    have := le_glue R.toPotentialCharts
      (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) hε.le hkm
    have e : φt x = R.glue (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) ε x := rfl
    rw [e]
    simpa [hη.eq_zero k x hk] using this
  have hCbig : |C1| + |C2| + |C4| ≤ C := by
    rw [hC]; linarith
  have hC0 : 0 ≤ C := le_trans (by positivity) hCbig

  have hd1 : ∀ x ∈ R.Yo, R.r x ≤ ℓ → φt x ≤ R.ph x + t ^ (1 / 3 : ℝ) + C * q := by
    intro x hxY hr
    have hnear : ∀ j, x ∈ R.mid j → R.phReg ρ K t j x + 4 * ε * η j x ≤
        R.ph x + C2 * ℓ ^ C2 * t ^ (1 / 2 : ℝ) := by
      intro j hx
      refine (harg j x hx).trans ?_
      have h := hC2 t ht htt2 K hK2 j x ⟨hx, hxY⟩ hr
      have hsrc := R.mid_subset_source j hx
      simp only [RegChartData.u, PotentialCharts.chartFun, (R.chart j).left_inv hsrc] at h
      simp only [RegChartData.phReg]
      linarith
    have hg := glue_le R.toPotentialCharts (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) hε.le hnear
    have e : φt x = R.glue (fun j x => R.phReg ρ K t j x + 4 * ε * η j x) ε x := rfl
    rw [← e] at hg
    have h16 : t ^ (1 / 6 : ℝ) = Real.exp (-(1 / 6) * ℓ) := by
      rw [Real.rpow_def_of_pos ht, hlogt]; congr 1; ring
    have hsplit : t ^ (1 / 2 : ℝ) = t ^ (1 / 3 : ℝ) * t ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add ht]; norm_num
    have hP := hL ℓ hℓL
    set P := ℓ ^ C2 * Real.exp (-(1 / 6) * ℓ) with hPdef
    have hP0 : 0 ≤ P := mul_nonneg (Real.rpow_nonneg hℓ0.le _) (Real.exp_pos _).le
    have hCP : C2 * P ≤ 1 := by
      have h7 : |C2| * P ≤ |C2| * (1 / (|C2| + 1)) :=
        mul_le_mul_of_nonneg_left hP.le (abs_nonneg _)
      have h8 : |C2| * (1 / (|C2| + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]; linarith
      have := mul_le_mul_of_nonneg_right (le_abs_self C2) hP0
      linarith
    have h13 : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
    have hkey : C2 * ℓ ^ C2 * t ^ (1 / 2 : ℝ) ≤ t ^ (1 / 3 : ℝ) := by
      rw [hsplit, h16]
      have : C2 * ℓ ^ C2 * (t ^ (1 / 3 : ℝ) * Real.exp (-(1 / 6) * ℓ)) =
          (C2 * P) * t ^ (1 / 3 : ℝ) := by rw [hPdef]; ring
      rw [this]; exact mul_le_of_le_one_left h13 hCP
    have hεC : ε ≤ C * q := by
      refine hε2.trans (mul_le_mul_of_nonneg_right ?_ hq0)
      rw [hC]; linarith
    linarith
  refine ⟨φt, hsmooth, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hxY
    obtain ⟨k, hk, hle⟩ := hlow x
    exact ((hbd K hK0 k x hk).2.2 hxY).trans hle
  ·
    intro x
    exact (hup x).trans (by rw [hC]; linarith)
  ·
    intro x
    obtain ⟨k, hk, hle⟩ := hlow x
    have h := (hbd K hK0 k x hk).1
    have h9 := mul_le_mul_of_nonneg_right hCbig hlog0
    have h10 := le_mul_of_one_le_right (abs_nonneg C4) hlog1
    have h11 := le_abs_self C4
    linarith
  ·
    intro k x hx w
    refine le_trans ?_ (hlevi k x hx w)
    rw [hCq]
    have hw : 0 ≤ ‖w‖ ^ 2 := by positivity
    have h11 : 4 * Cη * ε ≤ 8 * |Cη| * E * q := by
      have h12 := mul_le_mul_of_nonneg_right (by linarith [le_abs_self Cη] : 4 * Cη ≤ 4 * |Cη|) hε.le
      have h13 := mul_le_mul_of_nonneg_left hε2 (by positivity : (0 : ℝ) ≤ 4 * |Cη|)
      linarith
    have h14 : 8 * |Cη| * E * q ≤ C * q := by
      refine mul_le_mul_of_nonneg_right ?_ hq0
      rw [hC]; linarith
    have h15 := mul_le_mul_of_nonneg_right (h11.trans h14) hw
    linarith
  ·
    intro x hxY hr
    rw [hCq]
    exact hd1 x hxY hr
  ·
    intro x hxY
    rw [hCq]
    have hr1 := R.one_le_r x hxY
    have hr0 : 0 < R.r x := by linarith
    have h13 : 0 ≤ t ^ (1 / 3 : ℝ) := Real.rpow_nonneg ht.le _
    by_cases hr : R.r x ≤ ℓ
    · have := hd1 x hxY hr
      have := le_mul_of_one_le_right (mul_nonneg hC0 hq0) hr1
      linarith
    · push Not at hr
      have hlogr : Real.log (R.r x) ≤ q * R.r x := by
        have h15 := Real.log_div_self_antitoneOn (Set.mem_Ici.2 hℓe)
          (Set.mem_Ici.2 (hℓe.trans hr.le)) hr.le
        simp only at h15
        rw [div_le_iff₀ hr0] at h15
        exact h15
      have hqr : 1 ≤ q * R.r x := by
        have e1 : q * ℓ = Real.log ℓ := by rw [hqdef]; field_simp
        have := mul_le_mul_of_nonneg_left hr.le hq0
        linarith
      have hph := R.ph_ge x hxY
      have hlr0 : 0 ≤ Real.log (R.r x) := Real.log_nonneg hr1
      have h16 : -R.Clog * Real.log (R.r x) ≥ -|R.Clog| * Real.log (R.r x) := by
        have := mul_le_mul_of_nonneg_right (le_abs_self R.Clog) hlr0
        linarith
      have h17 : Cup + |R.Clog| * Real.log (R.r x) ≤ C * q * R.r x := by
        have h18 : Cup ≤ Cup * (q * R.r x) := le_mul_of_one_le_right hCup0 hqr
        have h19 : |R.Clog| * Real.log (R.r x) ≤ |R.Clog| * (q * R.r x) :=
          mul_le_mul_of_nonneg_left hlogr (abs_nonneg _)
        have h20 : Cup + |R.Clog| ≤ C := by
          rw [hC]; linarith [abs_nonneg C1, abs_nonneg C2, abs_nonneg C4]
        have h21 : 0 ≤ q * R.r x := by positivity
        have := mul_le_mul_of_nonneg_right h20 h21
        linarith
      have := hup x
      linarith

end LogLogRegularisation

end

end GroundTheory.Heights₂.Heights.Regular
