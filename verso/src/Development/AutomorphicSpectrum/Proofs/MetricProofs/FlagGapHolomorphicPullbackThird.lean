import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentMulSelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetGramSubharmonicStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize

/- English proof (translation)
Establish `h1 : ContinuousAt ((f ∘ c.symm) ∘ c) x` using `ContinuousAt.comp h (c.continuousAt hx)`. Use `h1.congr ?_` and prove the remaining obligations. Use `filter_upwards [c.open_source.mem_nhds hx] with z hz`. Simplify using `[c.left_inv hz]`.
-/
theorem continuousAt_of_chart {X E F : Type*} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace F]
    (c : OpenPartialHomeomorph X E) {f : X → F} {x : X} (hx : x ∈ c.source)
    (h : ContinuousAt (f ∘ c.symm) (c x)) : ContinuousAt f x := by
  have h1 : ContinuousAt ((f ∘ c.symm) ∘ c) x := ContinuousAt.comp h (c.continuousAt hx)
  refine h1.congr ?_
  filter_upwards [c.open_source.mem_nhds hx] with z hz
  simp [c.left_inv hz]

/- English proof (translation)
Take `⟨j, hj⟩` from `A.cover x`. Use `continuousAt_of_chart (A.chart j) hj ?_` and prove the remaining obligations. Establish `hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W` using `⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩`. Conclude with `(h j _ hm).continuousAt`.
-/
theorem holoOn_continuousAt {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) {W : Set X}
    {g : X → ℂ} (h : A.HoloOn W g) {x : X} (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  refine continuousAt_of_chart (A.chart j) hj ?_
  have hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  exact (h j _ hm).continuousAt

/- English proof (translation)
Take `⟨j, hj⟩` from `A.cover x`. Use `continuousAt_of_chart (A.chart j) hj ?_` and prove the remaining obligations. Establish `hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W` using `⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩`. Establish `ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W)` using `(A.chart j).isOpen_inter_preimage_symm hW`. Conclude with `((h j).continuousOn).continuousAt (ho.mem_nhds hm)`.
-/
theorem smoothOn_continuousAt {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) {W : Set X}
    (hW : IsOpen W) {g : X → ℝ} (h : A.SmoothOn W g) {x : X} (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  refine continuousAt_of_chart (A.chart j) hj ?_
  have hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hW
  exact ((h j).continuousOn).continuousAt (ho.mem_nhds hm)

variable {N : ℕ}

/- English proof (translation)
The claim follows from `|Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * V).det.re| ≤ N * Real.log m := by refine (GlobalTheory.T.log_det_comparable_gram_bound N k G 1 V m hm Matrix.PosDef.one hG h1 h2 hV).trans ?_ have : (k : ℝ) ≤ N := by exact_mod_cast hk exact mul_le_mu …`.
-/
theorem gram_cmp {k : ℕ} (hk : k ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (V : Matrix (Fin N) (Fin k) ℂ) {m : ℝ}
    (hm : 1 ≤ m) (hG : G.PosDef) (h1 : ((m : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef)
    (h2 : ((m : ℂ) • G - 1).PosSemidef) (hV : LinearIndependent ℂ Vᵀ) :
    |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * V).det.re| ≤ N * Real.log m := by
  refine (GlobalTheory.T.log_det_comparable_gram_bound N k G 1 V m hm Matrix.PosDef.one hG h1 h2 hV).trans ?_
  have : (k : ℝ) ≤ N := by exact_mod_cast hk
  exact mul_le_mul_of_nonneg_right this (Real.log_nonneg hm)

/- English proof (translation)
Simplify using `using S.card_le_univ`.
-/
theorem card_le (S : Finset (Fin N)) : S.card ≤ N := by
  simpa using S.card_le_univ

/- English proof (translation)
The claim follows from `|blockPot j i G h - blockPot j i 1 h| ≤ (3 / 2) * N * Real.log m := by obtain ⟨hS, hHS, hP⟩ := GramPot.blockPot_eq_gram N j i G h obtain ⟨-, -, hP1⟩ := GramPot.blockPot_eq_gram N j i 1 h have e1 := hP hG have e2 := hP1 Matrix.PosDef.one have tW := abs_le.1 (gram_cmp (card_le (wId …`.
-/
theorem blockPot_sub_le (j : ℕ) (i : Fin N) {G h : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (hd : h.det ≠ 0)
    {m : ℝ} (hm : 1 ≤ m) (h1 : ((m : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef)
    (h2 : ((m : ℂ) • G - 1).PosSemidef) :
    |blockPot j i G h - blockPot j i 1 h| ≤ (3 / 2) * N * Real.log m := by
  obtain ⟨hS, hHS, hP⟩ := GramPot.blockPot_eq_gram N j i G h
  obtain ⟨-, -, hP1⟩ := GramPot.blockPot_eq_gram N j i 1 h
  have e1 := hP hG
  have e2 := hP1 Matrix.PosDef.one
  have tW := abs_le.1 (gram_cmp (card_le (wIdx N j)) (selM (wIdx N j)) hm hG h1 h2 (hS _))
  have tO := abs_le.1 (gram_cmp (card_le (omIdx N j)) (selM (omIdx N j)) hm hG h1 h2 (hS _))
  have tH := abs_le.1 (gram_cmp (card_le (stepCols N j i)) (h * selM (stepCols N j i)) hm hG h1 h2 (hHS hd _))
  have hl : 0 ≤ (N : ℝ) * Real.log m := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hm)
  rw [e1, e2, abs_le]
  split_ifs <;> constructor <;> linarith [tW.1, tW.2, tO.1, tO.2, tH.1, tH.2]

/- English proof (translation)
Establish `hd : (0 : ℝ) ≤ r ^ |c| - r ^ c` using `sub_nonneg.2 (Real.rpow_le_rpow_of_exponent_le hr (le_abs_self c))`. Establish `hd' : (0 : ℂ) ≤ ((r ^ |c| - r ^ c : ℝ) : ℂ)` using `by exact_mod_cast hd`. Prove the components needed by the constructor for the conclusion. Use `h.1.add (Matrix.PosSemidef.one.smul hd')` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Use `module`. Use `h.2.add (hG.posSemidef.smul hd')` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `push_cast`.

Use `module`.
-/
theorem size_abs {G : Matrix (Fin N) (Fin N) ℂ} {r c : ℝ} (hr : 1 ≤ r) (hG : G.PosDef)
    (h : (((r ^ c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef ∧
      (((r ^ c : ℝ) : ℂ) • G - 1).PosSemidef) :
    (((r ^ |c| : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef ∧
      (((r ^ |c| : ℝ) : ℂ) • G - 1).PosSemidef := by
  have hd : (0 : ℝ) ≤ r ^ |c| - r ^ c := sub_nonneg.2 (Real.rpow_le_rpow_of_exponent_le hr (le_abs_self c))
  have hd' : (0 : ℂ) ≤ ((r ^ |c| - r ^ c : ℝ) : ℂ) := by exact_mod_cast hd
  constructor
  · have := h.1.add (Matrix.PosSemidef.one.smul hd')
    convert this using 1
    push_cast
    module
  · have := h.2.add (hG.posSemidef.smul hd')
    convert this using 1
    push_cast
    module

/- English proof (translation)
Establish `hu : IsUnit h` using `(Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit`. Establish `hp : (hᴴ * 1 * h).PosDef` using `Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)`. Conclude with `(Complex.lt_def.1 (GramPot.minor_pos hp S)).1`.
-/
theorem gram_one_pos {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (S : Finset (Fin N)) :
    0 < (minorIJ (hᴴ * 1 * h) S S).re := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit
  have hp : (hᴴ * 1 * h).PosDef :=
    Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
  exact (Complex.lt_def.1 (GramPot.minor_pos hp S)).1

/- English proof (translation)
Simplify using `only [minorIJ, dif_pos]`. Use `Complex.continuous_re.comp (Continuous.matrix_det ?_)` and prove the remaining obligations. Use `Continuous.matrix_submatrix ?_ _ _` and prove the remaining obligations. Use `fun_prop`.
-/
theorem continuous_gram (S : Finset (Fin N)) :
    Continuous fun h : Matrix (Fin N) (Fin N) ℂ => (minorIJ (hᴴ * 1 * h) S S).re := by
  simp only [minorIJ, dif_pos]
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine Continuous.matrix_submatrix ?_ _ _
  fun_prop

/- English proof (translation)
Establish `hc : ContinuousAt H x` using `continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => hH a b`. Unfold `blockPot`. Use `continuousAt_const.add ?_` and prove the remaining obligations. Use `split_ifs`. Use `continuousAt_const.mul (ContinuousAt.log ((continuous_gram _).continuousAt.comp hc) ?_)` and prove the remaining obligations.

Conclude with `(gram_one_pos hd _).ne'`. Conclude with `continuousAt_const`.
-/
theorem continuousAt_blockPot_one {X : Type*} [TopologicalSpace X] (j : ℕ) (i : Fin N)
    {H : X → Matrix (Fin N) (Fin N) ℂ} {x : X} (hH : ∀ a b, ContinuousAt (fun y => H y a b) x)
    (hd : (H x).det ≠ 0) : ContinuousAt (fun y => blockPot j i 1 (H y)) x := by
  have hc : ContinuousAt H x :=
    continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => hH a b
  unfold blockPot
  refine continuousAt_const.add ?_
  split_ifs
  · refine continuousAt_const.mul (ContinuousAt.log ((continuous_gram _).continuousAt.comp hc) ?_)
    exact (gram_one_pos hd _).ne'
  · exact continuousAt_const

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hch hpot`. Establish `hr : ∀ x, Real.exp 1 ≤ rW BM.L BM.s x` using `fun x => by`. Use `BM.norm_le x` as an intermediate fact. Simplify using `only [rW]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hrpos : ∀ x, 0 < rW BM.L BM.s x` using `fun x => (Real.exp_pos 1).trans_le (hr x)`. Establish `hr1 : ∀ x, 1 ≤ rW BM.L BM.s x` using `fun x => (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ Real.exp 1).trans (hr x)`. Establish `hlog : ∀ x, 1 ≤ Real.log (rW BM.L BM.s x)` using `fun x => (Real.le_log_iff_exp_le (hrpos x)).2 (hr x)`. Establish `key : ∀ y₀ : R.X, ∃ t ∈ 𝓝 y₀, ∃ C : ℝ, ∀ x ∈ t, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) → |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x)`. Introduce `y₀`.

Take `⟨W, l, H, D, hW, hy₀, -, hO, hH, hHd, hD, hDne, heq⟩` from `hch y₀ y₀ (R.mem_U y₀)`. Set `u : R.X → ℝ` to `fun y' => blockPot j p.2 1 (H y') + Real.log ‖D y'‖ - Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift y₀ y'))`. Establish `hu : ContinuousAt u y₀`. Use `((continuousAt_blockPot_one j p.2 (fun a b => holoOn_continuousAt R.A (hH a b) hy₀) (hHd y₀ hy₀).2).add ?_).sub ?_` and prove the remaining obligations. Conclude with `ContinuousAt.log (holoOn_continuousAt R.A hD hy₀).norm (norm_ne_zero_iff.2 (hDne y₀ hy₀))`.

Conclude with `smoothOn_continuousAt R.A (R.isOpen_U y₀) (hpot.1 y₀) (R.mem_U y₀)`. Use `⟨W ∩ {y' | |u y'| < |u y₀| + 1}, inter_mem (hW.mem_nhds hy₀) (hu.abs.eventually_lt continuousAt_const (lt_add_one _)), (3 / 2) * N * |BM.Cst| + (|u y₀| + 1), ?_⟩` and prove the remaining obligations. Introduce and unpack `y' ⟨hy'W, hy'u⟩ hb`. Establish `hb' : pr y' ∉ bdry BM.s` using `hb`. Establish `hmem : pr y' ∈ BM.O l \ bdry BM.s` using `⟨hO y' hy'W, hb'⟩`.

Take `⟨-, hpd⟩` from `BM.G_pos l p.1 _ hmem`. Establish `hs` using `size_abs (hr1 (pr y')) hpd (BM.size l p.1 _ hmem)`. Establish `hm1 : 1 ≤ rW BM.L BM.s (pr y') ^ |BM.Cst|` using `Real.one_le_rpow (hr1 _) (abs_nonneg _)`. Establish `hdiff` using `blockPot_sub_le j p.2 hpd (hHd y' hy'W).2 hm1 hs.1 hs.2`. Rewrite `hdiff` using `[Real.log_rpow (hrpos _)]`.

Establish `e'` using `heq y' hy'W hb'`. Establish `hL` using `hlog (pr y')`. Establish `hsum : stepPh M BM p v R pr y' = (blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')) + u y'`. Simplify using `only [u]`. Combine the linear equalities and inequalities to obtain the conclusion.

Express the relevant statement in the definitionally equal form `|stepPh M BM p v R pr y'| ≤ _ * Real.log (rW BM.L BM.s (pr y'))`. Rewrite using `[hsum]`. Establish `hu' : |u y'| < |u y₀| + 1` using `hy'u`. Establish `hc : |u y₀| + 1 ≤ (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y'))` using `le_mul_of_one_le_right (by positivity) hL`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = _ := by ring`. Establish `hlogr : ∀ x, 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x)` using `fun x => zero_le_one.trans (hlog (pr x))`. Take `⟨C, hC⟩` from `(isCompact_univ (X := R.X)).induction_on (p := fun S => ∃ C : ℝ, ∀ x ∈ S, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) → |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x)) ⟨0, fun x hx => absurd hx (Set.notMem_empty x)⟩ (fun s t hs …`. Take `⟨t, ht, C, hC⟩` from `key y₀`.

Conclude with `⟨t, mem_nhdsWithin_of_mem_nhds ht, C, hC⟩)`. Conclude with `⟨C, fun x hb => hC x (Set.mem_univ x) hb⟩`.
-/
theorem stepPh_le_log : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∃ C₁ : ℝ, ∀ x ∉ bdry (fun x y => BM.s (pr x) (pr y)), |stepPh M BM p v R pr x| ≤ C₁ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hch hpot
  have hr : ∀ x, Real.exp 1 ≤ rW BM.L BM.s x := fun x => by
    have := BM.norm_le x
    simp only [rW]
    linarith
  have hrpos : ∀ x, 0 < rW BM.L BM.s x := fun x => (Real.exp_pos 1).trans_le (hr x)
  have hr1 : ∀ x, 1 ≤ rW BM.L BM.s x := fun x =>
    (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ Real.exp 1).trans (hr x)
  have hlog : ∀ x, 1 ≤ Real.log (rW BM.L BM.s x) := fun x =>
    (Real.le_log_iff_exp_le (hrpos x)).2 (hr x)
  have key : ∀ y₀ : R.X, ∃ t ∈ 𝓝 y₀, ∃ C : ℝ, ∀ x ∈ t, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
    intro y₀
    obtain ⟨W, l, H, D, hW, hy₀, -, hO, hH, hHd, hD, hDne, heq⟩ := hch y₀ y₀ (R.mem_U y₀)
    let u : R.X → ℝ := fun y' => blockPot j p.2 1 (H y') + Real.log ‖D y'‖ -
      Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift y₀ y'))
    have hu : ContinuousAt u y₀ := by
      refine ((continuousAt_blockPot_one j p.2 (fun a b => holoOn_continuousAt R.A (hH a b) hy₀)
        (hHd y₀ hy₀).2).add ?_).sub ?_
      · exact ContinuousAt.log (holoOn_continuousAt R.A hD hy₀).norm (norm_ne_zero_iff.2 (hDne y₀ hy₀))
      · exact smoothOn_continuousAt R.A (R.isOpen_U y₀) (hpot.1 y₀) (R.mem_U y₀)
    refine ⟨W ∩ {y' | |u y'| < |u y₀| + 1}, inter_mem (hW.mem_nhds hy₀)
      (hu.abs.eventually_lt continuousAt_const (lt_add_one _)), (3 / 2) * N * |BM.Cst| + (|u y₀| + 1), ?_⟩
    rintro y' ⟨hy'W, hy'u⟩ hb
    have hb' : pr y' ∉ bdry BM.s := hb
    have hmem : pr y' ∈ BM.O l \ bdry BM.s := ⟨hO y' hy'W, hb'⟩
    obtain ⟨-, hpd⟩ := BM.G_pos l p.1 _ hmem
    have hs := size_abs (hr1 (pr y')) hpd (BM.size l p.1 _ hmem)
    have hm1 : 1 ≤ rW BM.L BM.s (pr y') ^ |BM.Cst| := Real.one_le_rpow (hr1 _) (abs_nonneg _)
    have hdiff := blockPot_sub_le j p.2 hpd (hHd y' hy'W).2 hm1 hs.1 hs.2
    rw [Real.log_rpow (hrpos _)] at hdiff
    have e' := heq y' hy'W hb'
    have hL := hlog (pr y')
    have hsum : stepPh M BM p v R pr y' = (blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')) + u y' := by
      simp only [u]
      linarith
    change |stepPh M BM p v R pr y'| ≤ _ * Real.log (rW BM.L BM.s (pr y'))
    rw [hsum]
    have hu' : |u y'| < |u y₀| + 1 := hy'u
    have hc : |u y₀| + 1 ≤ (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y')) :=
      le_mul_of_one_le_right (by positivity) hL
    calc _ ≤ |blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')| + |u y'| := abs_add_le _ _
      _ ≤ (3 / 2) * N * (|BM.Cst| * Real.log (rW BM.L BM.s (pr y'))) + (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y')) := by
        linarith
      _ = _ := by ring
  have hlogr : ∀ x, 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := fun x =>
    zero_le_one.trans (hlog (pr x))
  obtain ⟨C, hC⟩ := (isCompact_univ (X := R.X)).induction_on
    (p := fun S => ∃ C : ℝ, ∀ x ∈ S, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x))
    ⟨0, fun x hx => absurd hx (Set.notMem_empty x)⟩
    (fun s t hst ⟨C, hC⟩ => ⟨C, fun x hx => hC x (hst hx)⟩)
    (fun s t ⟨C, hC⟩ ⟨C', hC'⟩ => ⟨max C C', fun x hx hb => hx.elim
      (fun h => (hC x h hb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlogr x)))
      (fun h => (hC' x h hb).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hlogr x)))⟩)
    (fun y₀ _ => by
      obtain ⟨t, ht, C, hC⟩ := key y₀
      exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, C, hC⟩)
  exact ⟨C, fun x hb => hC x (Set.mem_univ x) hb⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize
