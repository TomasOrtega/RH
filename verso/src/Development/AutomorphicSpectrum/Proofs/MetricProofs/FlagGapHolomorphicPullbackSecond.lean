import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodChartPotentialLeviFormStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

/- English proof (translation)
Introduce `y hy`. Take `⟨k, hk⟩` from `A.cover y`. Establish `hz : A.chart k y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V` using `⟨(A.chart k).map_source hk, by show (A.chart k).symm (A.chart k y) ∈ V`. Rewrite using `[(A.chart k).left_inv hk]`. Conclude with `hy⟩`.

Establish `h1 : ContinuousAt (g ∘ (A.chart k).symm) (A.chart k y)` using `(h k _ hz).continuousAt`. Establish `h2 : ContinuousAt (A.chart k) y` using `(A.chart k).continuousAt hk`. Establish `h3 : ContinuousAt ((g ∘ (A.chart k).symm) ∘ (A.chart k)) y` using `ContinuousAt.comp h1 h2`. Use `(h3.congr ?_).continuousWithinAt` and prove the remaining obligations. Use `filter_upwards [(A.chart k).open_source.mem_nhds hk] with u hu`.

Simplify using `[(A.chart k).left_inv hu]`.
-/
theorem continuousOn_of_holoOn {V : Set X} (hV : IsOpen V) {g : X → ℂ} (h : A.HoloOn V g) :
    ContinuousOn g V := by
  intro y hy
  obtain ⟨k, hk⟩ := A.cover y
  have hz : A.chart k y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V :=
    ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k y) ∈ V
      rw [(A.chart k).left_inv hk]; exact hy⟩
  have h1 : ContinuousAt (g ∘ (A.chart k).symm) (A.chart k y) := (h k _ hz).continuousAt
  have h2 : ContinuousAt (A.chart k) y := (A.chart k).continuousAt hk
  have h3 : ContinuousAt ((g ∘ (A.chart k).symm) ∘ (A.chart k)) y := ContinuousAt.comp h1 h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with u hu
  simp [(A.chart k).left_inv hu]

/- English proof (translation)
Introduce `c z hz`. Take `⟨k, hk⟩` from `A.cover (h ((B.chart c).symm z))`. Establish `h1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart c).symm) z` using `hh.2 c k z ⟨hz.1, hk⟩`. Establish `h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart c).symm) z)` using `hg k _ ⟨(A.chart k).map_source hk, by show (A.chart k).symm (A.chart k (h ((B.chart c).symm z))) ∈ V`. Rewrite using `[(A.chart k).left_inv hk]`.

Conclude with `hz.2⟩`. Use `(h2.comp h1).congr ?_` and prove the remaining obligations. Establish `hc : ContinuousAt (h ∘ (B.chart c).symm) z` using `hh.1.continuousAt.comp ((B.chart c).continuousAt_symm hz.1)`. Use `filter_upwards [hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with u hu`. Establish `hu' : h ((B.chart c).symm u) ∈ (A.chart k).source` using `hu`.

Simplify using `only [Function.comp]`. Rewrite using `[(A.chart k).left_inv hu']`.
-/
theorem holoOn_comp {e' : ℕ} {Y : Type} [TopologicalSpace Y] {B : FinHolAtlas e' Y} {h : Y → X}
    (hh : HoloMap B A h) {V : Set X} {g : X → ℂ} (hg : A.HoloOn V g) :
    B.HoloOn (h ⁻¹' V) fun y => g (h y) := by
  intro c z hz
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart c).symm z))
  have h1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart c).symm) z := hh.2 c k z ⟨hz.1, hk⟩
  have h2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart c).symm) z) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      show (A.chart k).symm (A.chart k (h ((B.chart c).symm z))) ∈ V
      rw [(A.chart k).left_inv hk]; exact hz.2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (h ∘ (B.chart c).symm) z :=
    hh.1.continuousAt.comp ((B.chart c).continuousAt_symm hz.1)
  filter_upwards [hc.preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)] with u hu
  have hu' : h ((B.chart c).symm u) ∈ (A.chart k).source := hu
  simp only [Function.comp]
  rw [(A.chart k).left_inv hu']

/- English proof (translation)
Introduce `j` and use `(h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))`.
-/
theorem holoOn_mono {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

/- English proof (translation)
Introduce `j z hz` and use `(hf j z hz).mul (hg j z hz)`.
-/
theorem holoOn_mul {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x * g x :=
  fun j z hz => (hf j z hz).mul (hg j z hz)

/- English proof (translation)
Introduce `_ _ _` and use `analyticAt_const`.
-/
theorem holoOn_const (V : Set X) (c : ℂ) : A.HoloOn V fun _ => c := fun _ _ _ => analyticAt_const

/- English proof (translation)
Introduce `k z hz` and use `Finset.analyticAt_fun_sum s fun a _ => h a k z hz`.
-/
theorem holoOn_sum {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∑ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_sum s fun a _ => h a k z hz

/- English proof (translation)
Introduce `k z hz` and use `Finset.analyticAt_fun_prod s fun a _ => h a k z hz`.
-/
theorem holoOn_prod {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∏ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_prod s fun a _ => h a k z hz

/- English proof (translation)
Introduce `k z hz` and use `(h k z hz).inv (h0 _ hz.2)`.
-/
theorem holoOn_inv {V : Set X} {f : X → ℂ} (h : A.HoloOn V f) (h0 : ∀ y ∈ V, f y ≠ 0) :
    A.HoloOn V fun y => (f y)⁻¹ := fun k z hz => (h k z hz).inv (h0 _ hz.2)

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Conclude with `holoOn_sum _ fun s => holoOn_mul (holoOn_const _ _) (holoOn_prod _ fun a => h _ _)`.
-/
theorem holoOn_det {σ : Type} [Fintype σ] [DecidableEq σ] {V : Set X} {m : X → Matrix σ σ ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => (m y).det := by
  simp only [Matrix.det_apply']
  exact holoOn_sum _ fun s => holoOn_mul (holoOn_const _ _) (holoOn_prod _ fun a => h _ _)

/- English proof (translation)
Unfold `minorIJ`. Distinguish the cases in `e : I.card = J.card`. Simplify using `only [dif_pos e]`. Conclude with `holoOn_det fun a b => h _ _`. Simplify using `only [dif_neg e]`.

Conclude with `holoOn_const _ _`.
-/
theorem holoOn_minorIJ {N : ℕ} {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) (I J : Finset (Fin N)) :
    A.HoloOn V fun y => minorIJ (m y) I J := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e]
    exact holoOn_det fun a b => h _ _
  · simp only [dif_neg e]
    exact holoOn_const _ _

/- English proof (translation)
Unfold `detFac`. Use `holoOn_mul ?_ ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `holoOn_minorIJ h _ _`. Conclude with `holoOn_const _ _`.

Use `split_ifs`. Conclude with `holoOn_minorIJ h _ _`. Conclude with `holoOn_const _ _`.
-/
theorem holoOn_detFac {N j : ℕ} (i : Fin N) {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) : A.HoloOn V fun y => detFac j i (m y) := by
  unfold detFac
  refine holoOn_mul ?_ ?_
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _
  · split_ifs
    · exact holoOn_minorIJ h _ _
    · exact holoOn_const _ _

/- English proof (translation)
Use `⟨S ∩ (fun z => f z * (f y)⁻¹) ⁻¹' Complex.slitPlane, ((continuousOn_of_holoOn hS h).mul continuousOn_const).isOpen_inter_preimage hS Complex.isOpen_slitPlane, ⟨hy, ?_⟩, Set.inter_subset_left, fun z => Complex.log (f z * (f y)⁻¹) + Real.log ‖f y‖, fun k u hu => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Simplify using `[mul_inv_cancel₀ h0]`. Conclude with `(AnalyticAt.clog ((h k u ⟨hu.1, hu.2.1⟩).mul analyticAt_const) hu.2.2).add analyticAt_const`. Establish `hz0 : f z ≠ 0` using `left_ne_zero_of_mul (Complex.slitPlane_ne_zero hz.2)`. Rewrite using `[Complex.add_re, Complex.log_re, Complex.ofReal_re, ← div_eq_mul_inv, norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), sub_add_cancel]`.
-/
theorem exists_log {S : Set X} (hS : IsOpen S) {f : X → ℂ} (h : A.HoloOn S f) {y : X} (hy : y ∈ S)
    (h0 : f y ≠ 0) : ∃ W', IsOpen W' ∧ y ∈ W' ∧ W' ⊆ S ∧ ∃ G : X → ℂ, A.HoloOn W' G ∧
      ∀ z ∈ W', (G z).re = Real.log ‖f z‖ := by
  refine ⟨S ∩ (fun z => f z * (f y)⁻¹) ⁻¹' Complex.slitPlane,
    ((continuousOn_of_holoOn hS h).mul continuousOn_const).isOpen_inter_preimage hS Complex.isOpen_slitPlane,
    ⟨hy, ?_⟩, Set.inter_subset_left, fun z => Complex.log (f z * (f y)⁻¹) + Real.log ‖f y‖,
    fun k u hu => ?_, fun z hz => ?_⟩
  · simp [mul_inv_cancel₀ h0]
  · exact (AnalyticAt.clog ((h k u ⟨hu.1, hu.2.1⟩).mul analyticAt_const) hu.2.2).add analyticAt_const
  · have hz0 : f z ≠ 0 := left_ne_zero_of_mul (Complex.slitPlane_ne_zero hz.2)
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, ← div_eq_mul_inv, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 h0), sub_add_cancel]

end Holo

/- English proof (translation)
Unfold `minorIJ`. Rewrite using `[dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]`.
-/
theorem minorIJ_one_self {N : ℕ} (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I I = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

/- English proof (translation)
Establish `hu : IsUnit H.det` using `hd.isUnit`. Establish `h1` using `((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.2.2 H H⁻¹ hb (hb.inv hu)).2`. Rewrite `h1` using `[Matrix.mul_nonsing_inv _ hu]`. Establish `h2 : detFac j i (1 : Matrix (Fin N) (Fin N) ℂ) = 1`. Unfold `detFac`.

Apply the tactic sequence `split_ifs <;> simp [minorIJ_one_self]`. Introduce `h0`. Rewrite `h1` using `[h2, h0, zero_mul]`. Conclude with `one_ne_zero h1`.
-/
theorem detFac_ne_zero' {N j : ℕ} (hj : j ≤ N) (i : Fin N) {H : Matrix (Fin N) (Fin N) ℂ}
    (hb : IsBlockDiag j H) (hd : H.det ≠ 0) : detFac j i H ≠ 0 := by
  have hu : IsUnit H.det := hd.isUnit
  have h1 := ((GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.2.2 H H⁻¹ hb (hb.inv hu)).2
  rw [Matrix.mul_nonsing_inv _ hu] at h1
  have h2 : detFac j i (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    unfold detFac
    split_ifs <;> simp [minorIJ_one_self]
  intro h0
  rw [h2, h0, zero_mul] at h1
  exact one_ne_zero h1

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS x c y₀ hy w`. Take `⟨hyt, hyU, hyb⟩` from `hy`. Establish `hU : (R.A.chart c).symm y₀ ∈ R.U x` using `hyU.1`. Use `set y₁ := (R.A.chart c).symm y₀ with hy₁`. Take `⟨W, l, H, D, hW, hyW, hWU, hWO, hHh, hHd, hDh, hDn, hEq⟩` from `hS x y₁ hU`.

Establish `hb : pr y₁ ∉ bdry BM.s` using `hyb`. Take `⟨V, Pi, hV, hVo, hPh, hPg⟩` from `BM.period l (pr y₁) ⟨hWO y₁ hyW, hb⟩`. Establish `hcl : IsClosed (bdry BM.s)` using `GlobalTheory.T.isClosed_section_boundary _ _ _ _ _ BM.sec`. Set `V' : Set R.X` to `W ∩ pr ⁻¹' (V ∩ (bdry BM.s)ᶜ)`. Establish `hV'o : IsOpen V'` using `hW.inter ((hVo.inter hcl.isOpen_compl).preimage hp.1)`.

Establish `hyV' : y₁ ∈ V'` using `⟨hyW, hV, hb⟩`. Set `g : R.X → Matrix (Fin N) (Fin N) ℂ` to `fun y' => Pi p.1 (pr y') * H y'`. Establish `hVW : V' ⊆ W` using `Set.inter_subset_left`. Establish `hVP : V' ⊆ pr ⁻¹' V` using `fun y' h => h.2.1`. Establish `hPh' : ∀ a b, R.A.HoloOn V' fun y' => Pi p.1 (pr y') a b` using `fun a b => holoOn_mono (holoOn_comp hp (hPh p.1 a b)) hVP`.

Establish `hHh' : ∀ a b, R.A.HoloOn V' fun y' => H y' a b` using `fun a b => holoOn_mono (hHh a b) hVW`. Establish `hgh : ∀ a b, R.A.HoloOn V' fun y' => g y' a b` using `fun a b => by`. Simplify using `only [g, Matrix.mul_apply]`. Conclude with `holoOn_sum _ fun c' => holoOn_mul (hPh' a c') (hHh' c' b)`. Establish `hstep : ∀ (i : Fin N), ∀ y' ∈ V', InFlagDomain N j (g y') ∧ stepPot N j i (g y') = blockPot j i (BM.G l p.1 (pr y')) (H y') + Real.log ‖detFac j i (H y')‖`.

Introduce `i y' hy'`. Establish `hG` using `BM.G_pos l p.1 (pr y') ⟨hWO y' hy'.1, hy'.2.2⟩`. Conclude with `GlobalTheory.T.flag_potential_block_decomposition N j i _ _ _ M.j_le (hPg p.1 _ hy'.2.1) hG.1 hG.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2`. Establish `hdn : ∀ y' ∈ V', detFac j p.2 (H y') ≠ 0` using `fun y' hy' => detFac_ne_zero' M.j_le p.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2`. Set `f : R.X → ℂ` to `fun y' => D y' * (detFac j p.2 (H y'))⁻¹`.

Establish `hfh : R.A.HoloOn V' f` using `holoOn_mul (holoOn_mono hDh hVW) (holoOn_inv (holoOn_detFac p.2 hHh') hdn)`. Establish `hf0 : ∀ y' ∈ V', f y' ≠ 0` using `fun y' hy' => mul_ne_zero (hDn y' hy'.1) (inv_ne_zero (hdn y' hy'))`. Take `⟨V'', hV''o, hyV'', hV''s, Gh, hGh, hGre⟩` from `exists_log hV'o hfh hyV' (hf0 _ hyV')`. Set `Φl : R.X → ℝ` to `(potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)).φ x`. Set `pot : Unit × Fin N → LocPot R.X` to `fun q => LocPot.ofFun (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y'))`.

Establish `hPC : IsPeriodChart R.A j pot y₁ V'' (fun _ => g)`. Use `⟨hV''o, hyV'', fun _ a b => holoOn_mono (hgh a b) hV''s, fun _ y' hy' => (hstep p.2 y' (hV''s hy')).1, fun q => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hq : q.2 = p.2`. Use `⟨Gh, hGh, fun y' hy' => ?_⟩` and prove the remaining obligations. Establish `hy3` using `hV''s hy'`.

Use `show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + (Gh y').re`. Rewrite using `[if_pos hq, hq, hGre y' hy', (hstep p.2 y' hy3).2]`. Establish `hE` using `hEq y' hy3.1 hy3.2.2`. Establish `hl : Real.log ‖f y'‖ = Real.log ‖D y'‖ - Real.log ‖detFac j p.2 (H y')‖`. Simplify using `only [f]`.

Rewrite using `[norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 (hDn y' hy3.1)) (inv_ne_zero (norm_ne_zero_iff.2 (hdn y' hy3))), Real.log_inv, sub_eq_add_neg]`. Rewrite using `[hl]`. Use `show Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' = _`. Rewrite using `[hE]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨fun _ => 0, holoOn_const _ _, fun y' _ => ?_⟩ show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + ((0 : ℂ)).re` and prove the remaining obligations. Rewrite using `[if_neg hq]`. Simplify using the standard rewrite rules. Establish `hsrc : y₁ ∈ (R.A.chart c).source` using `(R.A.chart c).map_target hyt`. Take `⟨Lm, -, hL, -⟩` from `GlobalTheory.T.period_chart_potential_levi_form e R.X R.A Unit N j M.j_le pot y₁ V'' (fun _ => g) hPC c hsrc`.

Establish `hlev` using `hL ((), p.2) w`. Establish `e1 : (R.A.chart c) y₁ = y₀` using `(R.A.chart c).right_inv hyt`. Establish `e2 : (pot ((), p.2)).φ y₁ = Φl` using `by show (if p.2 = p.2 then Φl else fun y' => stepPot N j p.2 (g y')) = Φl`. Rewrite using `[if_pos rfl]`. Rewrite `hlev` using `[e2, e1]`.

Use `show 0 ≤ levi (Φl ∘ (R.A.chart c).symm) y₀ w`. Rewrite using `[hlev]`. Use `Finset.sum_nonneg fun q _ => ?_` and prove the remaining obligations. Use `split_ifs`. Check the signs of the components of the expression.

Conclude with `le_rfl`.
-/
theorem isPshOn_stepPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPshOn R.A (bdry (fun x y => BM.s (pr x) (pr y)))ᶜ (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hS x c y₀ hy w
  obtain ⟨hyt, hyU, hyb⟩ := hy
  have hU : (R.A.chart c).symm y₀ ∈ R.U x := hyU.1
  set y₁ := (R.A.chart c).symm y₀ with hy₁
  obtain ⟨W, l, H, D, hW, hyW, hWU, hWO, hHh, hHd, hDh, hDn, hEq⟩ := hS x y₁ hU
  have hb : pr y₁ ∉ bdry BM.s := hyb
  obtain ⟨V, Pi, hV, hVo, hPh, hPg⟩ := BM.period l (pr y₁) ⟨hWO y₁ hyW, hb⟩
  have hcl : IsClosed (bdry BM.s) := GlobalTheory.T.isClosed_section_boundary _ _ _ _ _ BM.sec
  let V' : Set R.X := W ∩ pr ⁻¹' (V ∩ (bdry BM.s)ᶜ)
  have hV'o : IsOpen V' := hW.inter ((hVo.inter hcl.isOpen_compl).preimage hp.1)
  have hyV' : y₁ ∈ V' := ⟨hyW, hV, hb⟩
  let g : R.X → Matrix (Fin N) (Fin N) ℂ := fun y' => Pi p.1 (pr y') * H y'
  have hVW : V' ⊆ W := Set.inter_subset_left
  have hVP : V' ⊆ pr ⁻¹' V := fun y' h => h.2.1
  have hPh' : ∀ a b, R.A.HoloOn V' fun y' => Pi p.1 (pr y') a b := fun a b =>
    holoOn_mono (holoOn_comp hp (hPh p.1 a b)) hVP
  have hHh' : ∀ a b, R.A.HoloOn V' fun y' => H y' a b := fun a b =>
    holoOn_mono (hHh a b) hVW
  have hgh : ∀ a b, R.A.HoloOn V' fun y' => g y' a b := fun a b => by
    simp only [g, Matrix.mul_apply]
    exact holoOn_sum _ fun c' => holoOn_mul (hPh' a c') (hHh' c' b)
  have hstep : ∀ (i : Fin N), ∀ y' ∈ V', InFlagDomain N j (g y') ∧
      stepPot N j i (g y') = blockPot j i (BM.G l p.1 (pr y')) (H y') + Real.log ‖detFac j i (H y')‖ := by
    intro i y' hy'
    have hG := BM.G_pos l p.1 (pr y') ⟨hWO y' hy'.1, hy'.2.2⟩
    exact GlobalTheory.T.flag_potential_block_decomposition N j i _ _ _ M.j_le (hPg p.1 _ hy'.2.1) hG.1 hG.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  have hdn : ∀ y' ∈ V', detFac j p.2 (H y') ≠ 0 := fun y' hy' =>
    detFac_ne_zero' M.j_le p.2 (hHd y' hy'.1).1 (hHd y' hy'.1).2
  let f : R.X → ℂ := fun y' => D y' * (detFac j p.2 (H y'))⁻¹
  have hfh : R.A.HoloOn V' f :=
    holoOn_mul (holoOn_mono hDh hVW) (holoOn_inv (holoOn_detFac p.2 hHh') hdn)
  have hf0 : ∀ y' ∈ V', f y' ≠ 0 := fun y' hy' =>
    mul_ne_zero (hDn y' hy'.1) (inv_ne_zero (hdn y' hy'))
  obtain ⟨V'', hV''o, hyV'', hV''s, Gh, hGh, hGre⟩ := exists_log hV'o hfh hyV' (hf0 _ hyV')
  let Φl : R.X → ℝ := (potOf R (fsHerm ιk fun k => M.dy p (κ k)) + LocPot.ofFun (stepPh M BM p v R pr)).φ x
  let pot : Unit × Fin N → LocPot R.X := fun q =>
    LocPot.ofFun (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y'))
  have hPC : IsPeriodChart R.A j pot y₁ V'' (fun _ => g) := by
    refine ⟨hV''o, hyV'', fun _ a b => holoOn_mono (hgh a b) hV''s,
      fun _ y' hy' => (hstep p.2 y' (hV''s hy')).1, fun q => ?_⟩
    by_cases hq : q.2 = p.2
    · refine ⟨Gh, hGh, fun y' hy' => ?_⟩
      have hy3 := hV''s hy'
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + (Gh y').re
      rw [if_pos hq, hq, hGre y' hy', (hstep p.2 y' hy3).2]
      have hE := hEq y' hy3.1 hy3.2.2
      have hl : Real.log ‖f y'‖ = Real.log ‖D y'‖ - Real.log ‖detFac j p.2 (H y')‖ := by
        simp only [f]
        rw [norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 (hDn y' hy3.1))
          (inv_ne_zero (norm_ne_zero_iff.2 (hdn y' hy3))), Real.log_inv, sub_eq_add_neg]
      rw [hl]
      show Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x y')) + stepPh M BM p v R pr y' = _
      rw [hE]
      ring
    · refine ⟨fun _ => 0, holoOn_const _ _, fun y' _ => ?_⟩
      show (if q.2 = p.2 then Φl else fun y' => stepPot N j q.2 (g y')) y' = stepPot N j q.2 (g y') + ((0 : ℂ)).re
      rw [if_neg hq]
      simp
  have hsrc : y₁ ∈ (R.A.chart c).source := (R.A.chart c).map_target hyt
  obtain ⟨Lm, -, hL, -⟩ := GlobalTheory.T.period_chart_potential_levi_form e R.X R.A Unit N j M.j_le pot y₁ V'' (fun _ => g) hPC c hsrc
  have hlev := hL ((), p.2) w
  have e1 : (R.A.chart c) y₁ = y₀ := (R.A.chart c).right_inv hyt
  have e2 : (pot ((), p.2)).φ y₁ = Φl := by
    show (if p.2 = p.2 then Φl else fun y' => stepPot N j p.2 (g y')) = Φl
    rw [if_pos rfl]
  rw [e2, e1] at hlev
  show 0 ≤ levi (Φl ∘ (R.A.chart c).symm) y₀ w
  rw [hlev]
  refine Finset.sum_nonneg fun q _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

end GlobalTheory.CompanionTheory.Ar.PB.StepW.PshW
