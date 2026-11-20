import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HasStepCharts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsClosedSectionBoundary
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LinearIndependentMulSelM
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramMatrixSubScalarPosSemidefStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.GradLoc

/- English proof (translation)
Introduce `e n X Y _ _ A B B' pr hp hc i k x₀ hi hk`. Take `⟨j', hj'⟩` from `B.cover (pr x₀)`. Establish `hu₀` using `(A.chart i).map_source hi`. Establish `hsx : (A.chart i).symm (A.chart i x₀) = x₀` using `(A.chart i).left_inv hi`. Establish `h1 : AnalyticAt ℂ (B.chart j' ∘ pr ∘ (A.chart i).symm) (A.chart i x₀)` using `hp.2 i j' _ ⟨hu₀, by show pr ((A.chart i).symm (A.chart i x₀)) ∈ (B.chart j').source; rw [hsx]; exact hj'⟩`.

Establish `h2 : AnalyticAt ℂ (B'.chart k ∘ (B.chart j').symm) (B.chart j' (pr x₀))` using `hc.1 j' k _ ⟨(B.chart j').map_source hj', by show (B.chart j').symm (B.chart j' (pr x₀)) ∈ (B'.chart k).source; rw [(B.chart j').left_inv hj']; exact hk⟩`. Establish `h3` using `AnalyticAt.comp_of_eq h2 h1 (by simp only [Function.comp, hsx])`. Use `h3.congr ?_` and prove the remaining obligations. Establish `hprc : ContinuousAt (fun u => pr ((A.chart i).symm u)) (A.chart i x₀)` using `hp.1.continuousAt.comp ((A.chart i).continuousAt_symm hu₀)`. Establish `hev : ∀ᶠ u in nhds (A.chart i x₀), pr ((A.chart i).symm u) ∈ (B.chart j').source` using `hprc.eventually_mem ((B.chart j').open_source.mem_nhds (by simpa only [hsx] using hj'))`.

Use `filter_upwards [hev] with u hu`. Simplify using `only [Function.comp]`. Rewrite using `[(B.chart j').left_inv hu]`.
-/
theorem patchmap : ∀ (e n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B B' : FinHolAtlas n Y) (pr : X → Y), HoloMap A B pr → B.Compatible B' → ∀ (i : Fin A.n) (k : Fin B'.n) (x₀ : X), x₀ ∈ (A.chart i).source → pr x₀ ∈ (B'.chart k).source → AnalyticAt ℂ (B'.chart k ∘ pr ∘ (A.chart i).symm) (A.chart i x₀) := by
  intro e n X Y _ _ A B B' pr hp hc i k x₀ hi hk
  obtain ⟨j', hj'⟩ := B.cover (pr x₀)
  have hu₀ := (A.chart i).map_source hi
  have hsx : (A.chart i).symm (A.chart i x₀) = x₀ := (A.chart i).left_inv hi
  have h1 : AnalyticAt ℂ (B.chart j' ∘ pr ∘ (A.chart i).symm) (A.chart i x₀) :=
    hp.2 i j' _ ⟨hu₀, by show pr ((A.chart i).symm (A.chart i x₀)) ∈ (B.chart j').source; rw [hsx]; exact hj'⟩
  have h2 : AnalyticAt ℂ (B'.chart k ∘ (B.chart j').symm) (B.chart j' (pr x₀)) :=
    hc.1 j' k _ ⟨(B.chart j').map_source hj', by
      show (B.chart j').symm (B.chart j' (pr x₀)) ∈ (B'.chart k).source; rw [(B.chart j').left_inv hj']; exact hk⟩
  have h3 := AnalyticAt.comp_of_eq h2 h1 (by simp only [Function.comp, hsx])
  refine h3.congr ?_
  have hprc : ContinuousAt (fun u => pr ((A.chart i).symm u)) (A.chart i x₀) :=
    hp.1.continuousAt.comp ((A.chart i).continuousAt_symm hu₀)
  have hev : ∀ᶠ u in nhds (A.chart i x₀), pr ((A.chart i).symm u) ∈ (B.chart j').source :=
    hprc.eventually_mem ((B.chart j').open_source.mem_nhds (by simpa only [hsx] using hj'))
  filter_upwards [hev] with u hu
  simp only [Function.comp]
  rw [(B.chart j').left_inv hu]

/- English proof (translation)
Introduce `n Y _ B B' hc O hO g hg k w hw hwO`. Take `⟨j, hj⟩` from `B.cover ((B'.chart k).symm w)`. Establish `hτ : AnalyticAt ℂ (B.chart j ∘ (B'.chart k).symm) w` using `hc.2 k j w ⟨hw, hj⟩`. Establish `hmem : (B.chart j) ((B'.chart k).symm w) ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' O` using `⟨(B.chart j).map_source hj, by show (B.chart j).symm _ ∈ O; rw [(B.chart j).left_inv hj]; exact hwO⟩`. Establish `hcd` using `(hg j).contDiffAt (((B.chart j).isOpen_inter_preimage_symm hO).mem_nhds hmem)`.

Establish `hd : DifferentiableAt ℝ (g ∘ (B.chart j).symm) ((B.chart j ∘ (B'.chart k).symm) w)` using `hcd.differentiableAt (by simp)`. Establish `hτd : DifferentiableAt ℝ (B.chart j ∘ (B'.chart k).symm) w` using `hτ.differentiableAt.restrictScalars ℝ`. Establish `hcomp` using `hd.comp w hτd`. Use `hcomp.congr_of_eventuallyEq ?_` and prove the remaining obligations. Establish `hev : ∀ᶠ y in nhds w, (B'.chart k).symm y ∈ (B.chart j).source` using `((B'.chart k).continuousAt_symm hw).eventually_mem ((B.chart j).open_source.mem_nhds hj)`.

Use `filter_upwards [hev] with y hy`. Simplify using `only [Function.comp]`. Rewrite using `[(B.chart j).left_inv hy]`.
-/
theorem gdiff : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (B B' : FinHolAtlas n Y), B.Compatible B' → ∀ (O : Set Y), IsOpen O → ∀ g : Y → ℝ, B.SmoothOn O g → ∀ (k : Fin B'.n) (w : Fin n → ℂ), w ∈ (B'.chart k).target → (B'.chart k).symm w ∈ O → DifferentiableAt ℝ (g ∘ (B'.chart k).symm) w := by
  intro n Y _ B B' hc O hO g hg k w hw hwO
  obtain ⟨j, hj⟩ := B.cover ((B'.chart k).symm w)
  have hτ : AnalyticAt ℂ (B.chart j ∘ (B'.chart k).symm) w := hc.2 k j w ⟨hw, hj⟩
  have hmem : (B.chart j) ((B'.chart k).symm w) ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' O :=
    ⟨(B.chart j).map_source hj, by
      show (B.chart j).symm _ ∈ O; rw [(B.chart j).left_inv hj]; exact hwO⟩
  have hcd := (hg j).contDiffAt (((B.chart j).isOpen_inter_preimage_symm hO).mem_nhds hmem)
  have hd : DifferentiableAt ℝ (g ∘ (B.chart j).symm) ((B.chart j ∘ (B'.chart k).symm) w) :=
    hcd.differentiableAt (by simp)
  have hτd : DifferentiableAt ℝ (B.chart j ∘ (B'.chart k).symm) w :=
    hτ.differentiableAt.restrictScalars ℝ
  have hcomp := hd.comp w hτd
  refine hcomp.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ y in nhds w, (B'.chart k).symm y ∈ (B.chart j).source :=
    ((B'.chart k).continuousAt_symm hw).eventually_mem ((B.chart j).open_source.mem_nhds hj)
  filter_upwards [hev] with y hy
  simp only [Function.comp]
  rw [(B.chart j).left_inv hy]

/- English proof (translation)
Introduce `e X _ A i x₀ W D φ hW hx₀ hi hD hDne hφ`. Use `set ψ := A.chart i with hψ`. Establish `hu₀ : ψ x₀ ∈ ψ.target` using `ψ.map_source hi`. Establish `hsx : ψ.symm (ψ x₀) = x₀` using `ψ.left_inv hi`. Establish `hmem : ψ x₀ ∈ ψ.target ∩ ψ.symm ⁻¹' W` using `⟨hu₀, by show ψ.symm (ψ x₀) ∈ W; rw [hsx]; exact hx₀⟩`.

Establish `hDa : AnalyticAt ℂ (fun y => D (ψ.symm y)) (ψ x₀)` using `hD i _ hmem`. Establish `hDc : ContDiffAt ℝ 2 (fun y => D (ψ.symm y)) (ψ x₀)` using `(hDa.contDiffAt (n := 2)).restrict_scalars ℝ`. Establish `hne : D (ψ.symm (ψ x₀)) ≠ 0` using `by rw [hsx]; exact hDne _ hx₀`. Establish `hlog : ContDiffAt ℝ 2 (fun y => Real.log ‖D (ψ.symm y)‖) (ψ x₀)` using `(hDc.norm ℝ hne).log (norm_ne_zero_iff.2 hne)`. Establish `hφc : ContDiffAt ℝ 2 (fun y => φ (ψ.symm y)) (ψ x₀)` using `(((hφ i).contDiffAt ((ψ.isOpen_inter_preimage_symm hW).mem_nhds hmem))).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))`.

Establish `hf` using `hlog.sub hφc`. Establish `hfc : ContinuousAt (fderiv ℝ (fun y => Real.log ‖D (ψ.symm y)‖ - φ (ψ.symm y))) (ψ x₀)` using `(hf.fderiv_right (m := 1) (by norm_num)).continuousAt`. Use `⟨‖fderiv ℝ (fun y => Real.log ‖D (ψ.symm y)‖ - φ (ψ.symm y)) (ψ x₀)‖ + 1, by positivity, ?_⟩` and prove the remaining obligations. Establish `e1` using `hf.eventually (by simp)`. Establish `e2` using `hfc.norm.eventually_lt (continuousAt_const (y := ‖fderiv ℝ (fun y => Real.log ‖D (ψ.symm y)‖ - φ (ψ.symm y)) (ψ x₀)‖ + 1)) (by linarith)`.

Use `filter_upwards [e1, e2] with u h1 h2`. Conclude with `⟨h1.differentiableAt (by simp), h2.le⟩`.
-/
theorem rest : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (i : Fin A.n) (x₀ : X) (W : Set X) (D : X → ℂ) (φ : X → ℝ), IsOpen W → x₀ ∈ W → x₀ ∈ (A.chart i).source → A.HoloOn W D → (∀ y ∈ W, D y ≠ 0) → A.SmoothOn W φ → ∃ c₂ : ℝ, 0 ≤ c₂ ∧ ∀ᶠ u in nhds (A.chart i x₀), DifferentiableAt ℝ (fun y => Real.log ‖D ((A.chart i).symm y)‖ - φ ((A.chart i).symm y)) u ∧ ‖fderiv ℝ (fun y => Real.log ‖D ((A.chart i).symm y)‖ - φ ((A.chart i).symm y)) u‖ ≤ c₂ := by
  intro e X _ A i x₀ W D φ hW hx₀ hi hD hDne hφ
  set ψ := A.chart i with hψ
  have hu₀ : ψ x₀ ∈ ψ.target := ψ.map_source hi
  have hsx : ψ.symm (ψ x₀) = x₀ := ψ.left_inv hi
  have hmem : ψ x₀ ∈ ψ.target ∩ ψ.symm ⁻¹' W := ⟨hu₀, by show ψ.symm (ψ x₀) ∈ W; rw [hsx]; exact hx₀⟩
  have hDa : AnalyticAt ℂ (fun y => D (ψ.symm y)) (ψ x₀) := hD i _ hmem
  have hDc : ContDiffAt ℝ 2 (fun y => D (ψ.symm y)) (ψ x₀) := (hDa.contDiffAt (n := 2)).restrict_scalars ℝ
  have hne : D (ψ.symm (ψ x₀)) ≠ 0 := by rw [hsx]; exact hDne _ hx₀
  have hlog : ContDiffAt ℝ 2 (fun y => Real.log ‖D (ψ.symm y)‖) (ψ x₀) :=
    (hDc.norm ℝ hne).log (norm_ne_zero_iff.2 hne)
  have hφc : ContDiffAt ℝ 2 (fun y => φ (ψ.symm y)) (ψ x₀) :=
    (((hφ i).contDiffAt ((ψ.isOpen_inter_preimage_symm hW).mem_nhds hmem))).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hf := hlog.sub hφc
  have hfc : ContinuousAt (fderiv ℝ (fun y => Real.log ‖D (ψ.symm y)‖ - φ (ψ.symm y))) (ψ x₀) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuousAt
  refine ⟨‖fderiv ℝ (fun y => Real.log ‖D (ψ.symm y)‖ - φ (ψ.symm y)) (ψ x₀)‖ + 1, by positivity, ?_⟩
  have e1 := hf.eventually (by simp)
  have e2 := hfc.norm.eventually_lt (continuousAt_const (y := ‖fderiv ℝ (fun y => Real.log ‖D (ψ.symm y)‖ - φ (ψ.symm y)) (ψ x₀)‖ + 1)) (by linarith)
  filter_upwards [e1, e2] with u h1 h2
  exact ⟨h1.differentiableAt (by simp), h2.le⟩

/- English proof (translation)
Introduce `N G t hG hT p q`. Establish `hd : ∀ a, (G a a).re ≤ t` using `fun a => by`. Establish `h` using `hT.diag_nonneg (i := a)`. Establish `h' : (0 : ℂ) ≤ ((t : ℝ) : ℂ) - G a a`. Simplify `h` using `[Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]`.

Use `(Complex.le_def.1 h').1` as an intermediate fact. Simplify using `using this`. Establish `hdn : ∀ a, (G a a).im = 0 ∧ 0 ≤ (G a a).re` using `fun a => by`. Establish `h` using `Complex.le_def.1 (hG.diag_nonneg (i := a))`. Conclude with `⟨by simpa using h.2.symm, by simpa using h.1⟩`.

Establish `hdet` using `(hG.submatrix ![p, q]).det_nonneg`. Rewrite `hdet` using `[Matrix.det_fin_two]`. Simplify using `only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet`. Establish `hqp : G q p = star (G p q)` using `(hG.1.apply q p).symm`. Rewrite `hdet` using `[hqp]`.

Establish `hre` using `(Complex.le_def.1 hdet).1`. Establish `hmul : G p q * star (G p q) = ((‖G p q‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite `hre` using `[hmul]`. Simplify using `only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.zero_re, (hdn p).1, (hdn q).1] at hre`.

Establish `ht0 : 0 ≤ t` using `(hdn p).2.trans (hd p)`. Establish `hsq : ‖G p q‖ ^ 2 ≤ t ^ 2`. Use `mul_le_mul (hd p) (hd q) (hdn q).2 ht0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) ht0 two_ne_zero).1 hsq`.
-/
theorem entry : ∀ (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ) (t : ℝ), G.PosSemidef → (((t : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef → ∀ p q, ‖G p q‖ ≤ t := by
  intro N G t hG hT p q
  have hd : ∀ a, (G a a).re ≤ t := fun a => by
    have h := hT.diag_nonneg (i := a)
    have h' : (0 : ℂ) ≤ ((t : ℝ) : ℂ) - G a a := by
      simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq] using h
    have := (Complex.le_def.1 h').1
    simpa using this
  have hdn : ∀ a, (G a a).im = 0 ∧ 0 ≤ (G a a).re := fun a => by
    have h := Complex.le_def.1 (hG.diag_nonneg (i := a))
    exact ⟨by simpa using h.2.symm, by simpa using h.1⟩
  have hdet := (hG.submatrix ![p, q]).det_nonneg
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  have hqp : G q p = star (G p q) := (hG.1.apply q p).symm
  rw [hqp] at hdet
  have hre := (Complex.le_def.1 hdet).1
  have hmul : G p q * star (G p q) = ((‖G p q‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hmul] at hre
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.zero_re, (hdn p).1, (hdn q).1] at hre
  have ht0 : 0 ≤ t := (hdn p).2.trans (hd p)
  have hsq : ‖G p q‖ ^ 2 ≤ t ^ 2 := by
    have := mul_le_mul (hd p) (hd q) (hdn q).2 ht0
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) ht0 two_ne_zero).1 hsq

/- English proof (translation)
Introduce `k M a ha h`. Establish `hp : (((a : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosDef` using `Matrix.PosDef.one.smul (by exact_mod_cast ha)`. Establish `e : M = (M - ((a : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)) + ((a : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)`. Simplify using the standard rewrite rules. Establish `hM : M.PosDef` using `by rw [e]; exact hp.posSemidef_add h`.

Conclude with `(Complex.lt_def.1 hM.det_pos).1`.
-/
theorem detpos : ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) ℂ) (a : ℝ), 0 < a → (M - (a : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef → 0 < M.det.re := by
  intro k M a ha h
  have hp : (((a : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast ha)
  have e : M = (M - ((a : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)) + ((a : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ) := by
    simp
  have hM : M.PosDef := by rw [e]; exact hp.posSemidef_add h
  exact (Complex.lt_def.1 hM.det_pos).1

/- English proof (translation)
Introduce `N S G A t a₀ ht hG hA`. Establish `hS : (selM S)ᴴ * selM S = 1`. Establish `h` using `GramPot.selM_conjTranspose_mul_mul (1 : Matrix (Fin N) (Fin N) ℂ) S`. Rewrite `h` using `[Matrix.mul_one]`. Rewrite using `[h]`.

Conclude with `Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective`. Establish `M1` using `hG.conjTranspose_mul_mul_same (A * selM S)`. Establish `M2` using `hA.conjTranspose_mul_mul_same (selM S)`. Establish `h1 : (A * selM S)ᴴ * (((t : ℝ) : ℂ) • G - 1) * (A * selM S) = ((t : ℝ) : ℂ) • ((A * selM S)ᴴ * G * (A * selM S)) - (A * selM S)ᴴ * (A * selM S)`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]`.

Establish `h2 : (selM S)ᴴ * (Aᴴ * A - (a₀ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) * selM S = (A * selM S)ᴴ * (A * selM S) - (a₀ : ℂ) • (1 : Matrix (Fin S.card) (Fin S.card) ℂ)`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hS, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite `M1` using `[h1]`. Rewrite `M2` using `[h2]`.

Establish `hsum` using `(M1.add M2).smul (show (0 : ℂ) ≤ (((t⁻¹ : ℝ)) : ℂ) by exact_mod_cast (inv_pos.2 ht).le)`. Establish `htc : ((t : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast ht.ne'`. Use `hsum using 1` and compare the differences between its conclusion and the goal. Rewrite using `[sub_add_sub_cancel, smul_sub, smul_smul]`. Use `congr 1`.

Rewrite using `[Complex.ofReal_inv, inv_mul_cancel₀ htc, one_smul]`. Rewrite using `[smul_smul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem lower : ∀ (N : ℕ) (S : Finset (Fin N)) (G A : Matrix (Fin N) (Fin N) ℂ) (t a₀ : ℝ), 0 < t → (((t : ℝ) : ℂ) • G - 1).PosSemidef → (Aᴴ * A - (a₀ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef → ((A * selM S)ᴴ * G * (A * selM S) - ((a₀ / t : ℝ) : ℂ) • (1 : Matrix (Fin S.card) (Fin S.card) ℂ)).PosSemidef := by
  intro N S G A t a₀ ht hG hA
  have hS : (selM S)ᴴ * selM S = 1 := by
    have h := GramPot.selM_conjTranspose_mul_mul (1 : Matrix (Fin N) (Fin N) ℂ) S
    rw [Matrix.mul_one] at h
    rw [h]
    exact Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective
  have M1 := hG.conjTranspose_mul_mul_same (A * selM S)
  have M2 := hA.conjTranspose_mul_mul_same (selM S)
  have h1 : (A * selM S)ᴴ * (((t : ℝ) : ℂ) • G - 1) * (A * selM S) =
      ((t : ℝ) : ℂ) • ((A * selM S)ᴴ * G * (A * selM S)) - (A * selM S)ᴴ * (A * selM S) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have h2 : (selM S)ᴴ * (Aᴴ * A - (a₀ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) * selM S =
      (A * selM S)ᴴ * (A * selM S) - (a₀ : ℂ) • (1 : Matrix (Fin S.card) (Fin S.card) ℂ) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hS,
      Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [h1] at M1
  rw [h2] at M2
  have hsum := (M1.add M2).smul (show (0 : ℂ) ≤ (((t⁻¹ : ℝ)) : ℂ) by exact_mod_cast (inv_pos.2 ht).le)
  have htc : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  convert hsum using 1
  rw [sub_add_sub_cancel, smul_sub, smul_smul]
  congr 1
  · rw [Complex.ofReal_inv, inv_mul_cancel₀ htc, one_smul]
  · rw [smul_smul]
    congr 1
    push_cast
    field_simp

/- English proof (translation)
Introduce `n k E _ _ G V x hG hV hne`. Establish `hVc : ∀ p q, DifferentiableAt ℝ (fun y => star (V y p q)) x` using `fun p q => (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp x (hV p q)`. Establish `hM : ∀ a c, DifferentiableAt ℝ (fun y => ((V y)ᴴ * G y * V y) a c) x`. Introduce `a c`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply]`.

Use `DifferentiableAt.fun_sum fun d _ => DifferentiableAt.mul (DifferentiableAt.fun_sum fun f _ => ?_) (hV d c)` and prove the remaining obligations. Conclude with `(hVc f a).mul (hG f d)`. Establish `hprod : ∀ (s : Finset (Fin k)) (σ : Equiv.Perm (Fin k)), DifferentiableAt ℝ (fun y => ∏ i ∈ s, ((V y)ᴴ * G y * V y) (σ i) i) x`. Introduce `s σ`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.prod_insert ha]`. Conclude with `(hM _ _).mul ih`. Establish `hdet : DifferentiableAt ℝ (fun y => ((V y)ᴴ * G y * V y).det) x`.

Simplify using `only [Matrix.det_apply]`. Use `DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_smul ?_ _` and prove the remaining obligations. Conclude with `hprod Finset.univ σ`. Conclude with `(Complex.reCLM.differentiableAt.comp x hdet).log hne`.
-/
theorem diff : ∀ (n k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G : E → Matrix (Fin n) (Fin n) ℂ) (V : E → Matrix (Fin n) (Fin k) ℂ) (x : E), (∀ p q, DifferentiableAt ℝ (fun y => G y p q) x) → (∀ p q, DifferentiableAt ℝ (fun y => V y p q) x) → ((V x)ᴴ * G x * V x).det.re ≠ 0 → DifferentiableAt ℝ (fun y => Real.log ((V y)ᴴ * G y * V y).det.re) x := by
  intro n k E _ _ G V x hG hV hne
  have hVc : ∀ p q, DifferentiableAt ℝ (fun y => star (V y p q)) x := fun p q =>
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp x (hV p q)
  have hM : ∀ a c, DifferentiableAt ℝ (fun y => ((V y)ᴴ * G y * V y) a c) x := by
    intro a c
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    refine DifferentiableAt.fun_sum fun d _ => DifferentiableAt.mul (DifferentiableAt.fun_sum fun f _ => ?_) (hV d c)
    exact (hVc f a).mul (hG f d)
  have hprod : ∀ (s : Finset (Fin k)) (σ : Equiv.Perm (Fin k)),
      DifferentiableAt ℝ (fun y => ∏ i ∈ s, ((V y)ᴴ * G y * V y) (σ i) i) x := by
    intro s σ
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hM _ _).mul ih
  have hdet : DifferentiableAt ℝ (fun y => ((V y)ᴴ * G y * V y).det) x := by
    simp only [Matrix.det_apply]
    refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_smul ?_ _
    exact hprod Finset.univ σ
  exact (Complex.reCLM.differentiableAt.comp x hdet).log hne

/- English proof (translation)
Simplify using `only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`.
-/
theorem star_dot_self {N : ℕ} (v : Fin N → ℂ) : star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/- English proof (translation)
Take `⟨a, ha⟩ : ∃ a : ℝ, a = ((N : ℝ) ^ 2 * b ^ 2 + 1)⁻¹` from `⟨_, rfl⟩`. Rewrite using `[← ha]`. Establish `hD : 0 < (N : ℝ) ^ 2 * b ^ 2 + 1` using `by positivity`. Establish `ha0 : 0 < a` using `ha ▸ inv_pos.2 hD`. Establish `hone : (((a : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef` using `Matrix.PosSemidef.one.smul (by exact_mod_cast ha0.le)`.

Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ((Matrix.isHermitian_conjTranspose_mul_self A).sub hone.1) fun x => ?_` and prove the remaining obligations. Take `⟨w, hw⟩ : ∃ w, w = A *ᵥ x` from `⟨_, rfl⟩`. Establish `hx : x = T *ᵥ w` using `by rw [hw, Matrix.mulVec_mulVec, hTA, Matrix.one_mulVec]`. Establish `e : star x ⬝ᵥ ((Aᴴ * A - ((a : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ x) = star w ⬝ᵥ w - ((a : ℝ) : ℂ) * (star x ⬝ᵥ x)`. Rewrite using `[Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, ← hw, Matrix.dotProduct_mulVec, hw, Matrix.star_mulVec, smul_eq_mul]`.

Rewrite using `[e, star_dot_self, star_dot_self]`. Establish `hle : ∑ i, ‖x i‖ ^ 2 ≤ (N : ℝ) ^ 2 * b ^ 2 * ∑ i, ‖w i‖ ^ 2`. Establish `h1 : ∀ i, ‖x i‖ ^ 2 ≤ (N : ℝ) * b ^ 2 * ∑ c, ‖w c‖ ^ 2` using `fun i => by`. Establish `h2 : ‖x i‖ ≤ b * ∑ c, ‖w c‖`. Rewrite using `[hx, Matrix.mulVec, dotProduct, Finset.mul_sum]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hT _ _) (norm_nonneg _)`. Establish `h3 : (∑ c, ‖w c‖) ^ 2 ≤ (N : ℝ) * ∑ c, ‖w c‖ ^ 2`. Use `sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c => ‖w c‖)` as an intermediate fact.

Simplify using `using this`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hW : 0 ≤ ∑ i, ‖w i‖ ^ 2` using `by positivity`. Establish `hfin : a * ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖w i‖ ^ 2`.

Establish `h4 : ∑ i, ‖x i‖ ^ 2 ≤ ((N : ℝ) ^ 2 * b ^ 2 + 1) * ∑ i, ‖w i‖ ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Establish `: (0 : ℂ) ≤ (((∑ i, ‖w i‖ ^ 2) - a * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ)` using `Complex.zero_le_real.2 (by linarith)`. Simplify using `using this`.
-/
theorem invlow (N : ℕ) (A T : Matrix (Fin N) (Fin N) ℂ) (b : ℝ) (hb : 0 ≤ b) (hTA : T * A = 1)
    (hT : ∀ p q, ‖T p q‖ ≤ b) :
    (Aᴴ * A - ((((N : ℝ) ^ 2 * b ^ 2 + 1)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ((N : ℝ) ^ 2 * b ^ 2 + 1)⁻¹ := ⟨_, rfl⟩
  rw [← ha]
  have hD : 0 < (N : ℝ) ^ 2 * b ^ 2 + 1 := by positivity
  have ha0 : 0 < a := ha ▸ inv_pos.2 hD
  have hone : (((a : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast ha0.le)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_conjTranspose_mul_self A).sub hone.1) fun x => ?_
  obtain ⟨w, hw⟩ : ∃ w, w = A *ᵥ x := ⟨_, rfl⟩
  have hx : x = T *ᵥ w := by rw [hw, Matrix.mulVec_mulVec, hTA, Matrix.one_mulVec]
  have e : star x ⬝ᵥ ((Aᴴ * A - ((a : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) *ᵥ x) =
      star w ⬝ᵥ w - ((a : ℝ) : ℂ) * (star x ⬝ᵥ x) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, ← hw, Matrix.dotProduct_mulVec, hw, Matrix.star_mulVec, smul_eq_mul]
  rw [e, star_dot_self, star_dot_self]
  have hle : ∑ i, ‖x i‖ ^ 2 ≤ (N : ℝ) ^ 2 * b ^ 2 * ∑ i, ‖w i‖ ^ 2 := by
    have h1 : ∀ i, ‖x i‖ ^ 2 ≤ (N : ℝ) * b ^ 2 * ∑ c, ‖w c‖ ^ 2 := fun i => by
      have h2 : ‖x i‖ ≤ b * ∑ c, ‖w c‖ := by
        rw [hx, Matrix.mulVec, dotProduct, Finset.mul_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hT _ _) (norm_nonneg _)
      have h3 : (∑ c, ‖w c‖) ^ 2 ≤ (N : ℝ) * ∑ c, ‖w c‖ ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun c => ‖w c‖)
        simpa using this
      calc ‖x i‖ ^ 2 ≤ (b * ∑ c, ‖w c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = b ^ 2 * (∑ c, ‖w c‖) ^ 2 := by ring
        _ ≤ b ^ 2 * ((N : ℝ) * ∑ c, ‖w c‖ ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = _ := by ring
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin N, (N : ℝ) * b ^ 2 * ∑ c, ‖w c‖ ^ 2 := Finset.sum_le_sum fun i _ => h1 i
      _ = _ := by simp; ring
  have hW : 0 ≤ ∑ i, ‖w i‖ ^ 2 := by positivity
  have hfin : a * ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, ‖w i‖ ^ 2 := by
    have h4 : ∑ i, ‖x i‖ ^ 2 ≤ ((N : ℝ) ^ 2 * b ^ 2 + 1) * ∑ i, ‖w i‖ ^ 2 := by nlinarith
    calc a * ∑ i, ‖x i‖ ^ 2 ≤ a * (((N : ℝ) ^ 2 * b ^ 2 + 1) * ∑ i, ‖w i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h4 ha0.le
      _ = _ := by rw [ha, ← mul_assoc, inv_mul_cancel₀ hD.ne', one_mul]
  have : (0 : ℂ) ≤ (((∑ i, ‖w i‖ ^ 2) - a * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) :=
    Complex.zero_le_real.2 (by linarith)
  simpa using this

/- English proof (translation)
Introduce `N e A u₀ hA hdet`. Establish `hC : ∀ p q, ContDiffAt ℝ 2 (fun y => A y p q) u₀` using `fun p q => ((hA p q).contDiffAt (n := 2)).restrict_scalars ℝ`. Establish `hAc : ContinuousAt A u₀` using `continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => (hA p q).continuousAt`. Establish `hTc : ContinuousAt (fun u => (A u)⁻¹) u₀` using `ContinuousAt.comp (g := fun M : Matrix (Fin N) (Fin N) ℂ => M⁻¹) (continuousAt_matrix_inv (A u₀) (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)) hAc`. Establish `hTe : ∀ p q, ContinuousAt (fun u => (A u)⁻¹ p q) u₀` using `fun p q => (continuous_apply_apply p q).continuousAt.comp hTc`.

Take `⟨b, hbdef⟩ : ∃ b : ℝ, b = 1 + ∑ p, ∑ q, (‖A u₀ p q‖ + ‖fderiv ℝ (fun y => A y p q) u₀‖ + ‖(A u₀)⁻¹ p q‖ + 1)` from `⟨_, rfl⟩`. Establish `hterm : ∀ p q, ‖A u₀ p q‖ + ‖fderiv ℝ (fun y => A y p q) u₀‖ + ‖(A u₀)⁻¹ p q‖ + 1 ≤ b` using `fun p q => by`. Establish `h1` using `Finset.single_le_sum (f := fun q => ‖A u₀ p q‖ + ‖fderiv ℝ (fun y => A y p q) u₀‖ + ‖(A u₀)⁻¹ p q‖ + 1) (fun _ _ => by positivity) (Finset.mem_univ q)`. Establish `h2` using `Finset.single_le_sum (f := fun p => ∑ q, (‖A u₀ p q‖ + ‖fderiv ℝ (fun y => A y p q) u₀‖ + ‖(A u₀)⁻¹ p q‖ + 1)) (fun _ _ => by positivity) (Finset.mem_univ p)`. Rewrite using `[hbdef]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb1 : 1 ≤ b`. Rewrite using `[hbdef]`. Establish `: 0 ≤ ∑ p, ∑ q, (‖A u₀ p q‖ + ‖fderiv ℝ (fun y => A y p q) u₀‖ + ‖(A u₀)⁻¹ p q‖ + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hent : ∀ p q, ∀ᶠ u in nhds u₀, DifferentiableAt ℝ (fun y => A y p q) u ∧ ‖A u p q‖ ≤ b ∧ ‖fderiv ℝ (fun y => A y p q) u‖ ≤ b ∧ ‖(A u)⁻¹ p q‖ ≤ b` using `fun p q => by`. Establish `ht` using `hterm p q`. Establish `n1` using `norm_nonneg (A u₀ p q)`. Establish `n2` using `norm_nonneg (fderiv ℝ (fun y => A y p q) u₀)`. Establish `n3` using `norm_nonneg ((A u₀)⁻¹ p q)`.

Establish `e1` using `(hC p q).eventually (by simp)`. Establish `e2` using `(hA p q).continuousAt.norm.eventually_lt (continuousAt_const (y := b)) (show ‖A u₀ p q‖ < b by linarith)`. Establish `e3` using `((hC p q).fderiv_right (m := 1) (by norm_num)).continuousAt.norm.eventually_lt (continuousAt_const (y := b)) (by linarith)`. Establish `e4` using `(hTe p q).norm.eventually_lt (continuousAt_const (y := b)) (show ‖(A u₀)⁻¹ p q‖ < b by linarith)`. Use `filter_upwards [e1, e2, e3, e4] with u h1 h2 h3 h4`.

Conclude with `⟨h1.differentiableAt (by simp), h2.le, h3.le, h4.le⟩`. Establish `hall : ∀ᶠ u in nhds u₀, ∀ p q, DifferentiableAt ℝ (fun y => A y p q) u ∧ ‖A u p q‖ ≤ b ∧ ‖fderiv ℝ (fun y => A y p q) u‖ ≤ b ∧ ‖(A u)⁻¹ p q‖ ≤ b` using `eventually_all.2 fun p => eventually_all.2 fun q => hent p q`. Establish `hdc : ContinuousAt (fun u => (A u).det) u₀` using `ContinuousAt.comp (g := fun M : Matrix (Fin N) (Fin N) ℂ => M.det) (Continuous.matrix_det continuous_id).continuousAt hAc`. Establish `hdn : ∀ᶠ u in nhds u₀, (A u).det ≠ 0` using `hdc.eventually_ne hdet`. Establish `hD : 1 ≤ (N : ℝ) ^ 2 * b ^ 2 + 1` using `by nlinarith [sq_nonneg ((N : ℝ) * b)]`.

Use `⟨b, ((N : ℝ) ^ 2 * b ^ 2 + 1)⁻¹, hb1, by positivity, inv_le_one_of_one_le₀ hD, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hall, hdn] with u h1 h2`. Use `⟨fun p q => ⟨(h1 p q).1, (h1 p q).2.1, (h1 p q).2.2.1⟩, ?_⟩` and prove the remaining obligations. Conclude with `invlow N (A u) (A u)⁻¹ b (by linarith) (Matrix.nonsing_inv_mul _ h2.isUnit) fun p q => (h1 p q).2.2.2`.
-/
theorem frame : ∀ (N e : ℕ) (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ) (u₀ : Fin e → ℂ), (∀ p q, AnalyticAt ℂ (fun y => A y p q) u₀) → (A u₀).det ≠ 0 → ∃ b a₀ : ℝ, 1 ≤ b ∧ 0 < a₀ ∧ a₀ ≤ 1 ∧ ∀ᶠ u in nhds u₀, (∀ p q, DifferentiableAt ℝ (fun y => A y p q) u ∧ ‖A u p q‖ ≤ b ∧ ‖fderiv ℝ (fun y => A y p q) u‖ ≤ b) ∧ ((A u)ᴴ * A u - (a₀ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by
  intro N e A u₀ hA hdet
  have hC : ∀ p q, ContDiffAt ℝ 2 (fun y => A y p q) u₀ := fun p q =>
    ((hA p q).contDiffAt (n := 2)).restrict_scalars ℝ
  have hAc : ContinuousAt A u₀ :=
    continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => (hA p q).continuousAt
  have hTc : ContinuousAt (fun u => (A u)⁻¹) u₀ :=
    ContinuousAt.comp (g := fun M : Matrix (Fin N) (Fin N) ℂ => M⁻¹) (continuousAt_matrix_inv (A u₀)
      (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)) hAc
  have hTe : ∀ p q, ContinuousAt (fun u => (A u)⁻¹ p q) u₀ := fun p q =>
    (continuous_apply_apply p q).continuousAt.comp hTc
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = 1 + ∑ p, ∑ q, (‖A u₀ p q‖ + ‖fderiv ℝ (fun y => A y p q) u₀‖ + ‖(A u₀)⁻¹ p q‖ + 1) := ⟨_, rfl⟩
  have hterm : ∀ p q, ‖A u₀ p q‖ + ‖fderiv ℝ (fun y => A y p q) u₀‖ + ‖(A u₀)⁻¹ p q‖ + 1 ≤ b := fun p q => by
    have h1 := Finset.single_le_sum (f := fun q => ‖A u₀ p q‖ + ‖fderiv ℝ (fun y => A y p q) u₀‖ + ‖(A u₀)⁻¹ p q‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ q)
    have h2 := Finset.single_le_sum (f := fun p => ∑ q, (‖A u₀ p q‖ + ‖fderiv ℝ (fun y => A y p q) u₀‖ + ‖(A u₀)⁻¹ p q‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ p)
    rw [hbdef]; linarith
  have hb1 : 1 ≤ b := by
    rw [hbdef]
    have : 0 ≤ ∑ p, ∑ q, (‖A u₀ p q‖ + ‖fderiv ℝ (fun y => A y p q) u₀‖ + ‖(A u₀)⁻¹ p q‖ + 1) := by positivity
    linarith
  have hent : ∀ p q, ∀ᶠ u in nhds u₀, DifferentiableAt ℝ (fun y => A y p q) u ∧ ‖A u p q‖ ≤ b ∧
      ‖fderiv ℝ (fun y => A y p q) u‖ ≤ b ∧ ‖(A u)⁻¹ p q‖ ≤ b := fun p q => by
    have ht := hterm p q
    have n1 := norm_nonneg (A u₀ p q)
    have n2 := norm_nonneg (fderiv ℝ (fun y => A y p q) u₀)
    have n3 := norm_nonneg ((A u₀)⁻¹ p q)
    have e1 := (hC p q).eventually (by simp)
    have e2 := (hA p q).continuousAt.norm.eventually_lt (continuousAt_const (y := b)) (show ‖A u₀ p q‖ < b by linarith)
    have e3 := ((hC p q).fderiv_right (m := 1) (by norm_num)).continuousAt.norm.eventually_lt
      (continuousAt_const (y := b)) (by linarith)
    have e4 := (hTe p q).norm.eventually_lt (continuousAt_const (y := b)) (show ‖(A u₀)⁻¹ p q‖ < b by linarith)
    filter_upwards [e1, e2, e3, e4] with u h1 h2 h3 h4
    exact ⟨h1.differentiableAt (by simp), h2.le, h3.le, h4.le⟩
  have hall : ∀ᶠ u in nhds u₀, ∀ p q, DifferentiableAt ℝ (fun y => A y p q) u ∧ ‖A u p q‖ ≤ b ∧
      ‖fderiv ℝ (fun y => A y p q) u‖ ≤ b ∧ ‖(A u)⁻¹ p q‖ ≤ b :=
    eventually_all.2 fun p => eventually_all.2 fun q => hent p q
  have hdc : ContinuousAt (fun u => (A u).det) u₀ :=
    ContinuousAt.comp (g := fun M : Matrix (Fin N) (Fin N) ℂ => M.det) (Continuous.matrix_det continuous_id).continuousAt hAc
  have hdn : ∀ᶠ u in nhds u₀, (A u).det ≠ 0 := hdc.eventually_ne hdet
  have hD : 1 ≤ (N : ℝ) ^ 2 * b ^ 2 + 1 := by nlinarith [sq_nonneg ((N : ℝ) * b)]
  refine ⟨b, ((N : ℝ) ^ 2 * b ^ 2 + 1)⁻¹, hb1, by positivity, inv_le_one_of_one_le₀ hD, ?_⟩
  filter_upwards [hall, hdn] with u h1 h2
  refine ⟨fun p q => ⟨(h1 p q).1, (h1 p q).2.1, (h1 p q).2.2.1⟩, ?_⟩
  exact invlow N (A u) (A u)⁻¹ b (by linarith) (Matrix.nonsing_inv_mul _ h2.isUnit) fun p q => (h1 p q).2.2.2

/- English proof (translation)
Introduce `N S E _ _ G A u b a₀ Cst r hb ha hr hGd hAd hev hs1 hs2 hGb hAb hAa`. Establish `hr0 : 0 < r` using `by linarith`. Take `⟨t, htdef⟩ : ∃ t : ℝ, t = r ^ Cst` from `⟨_, rfl⟩`. Rewrite `hs1`, `hs2` using `[← htdef]`. Establish `ht0 : 0 < t` using `htdef ▸ Real.rpow_pos_of_pos hr0 _`.

Take `⟨R, hRdef⟩ : ∃ R : ℝ, R = r ^ |Cst|` from `⟨_, rfl⟩`. Establish `htR : t ≤ R`. Rewrite using `[htdef, hRdef]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hr (le_abs_self _)`. Establish `hR1 : 1 ≤ R` using `hRdef ▸ Real.one_le_rpow hr (abs_nonneg _)`.

Establish `hR4 : r ^ (4 * |Cst|) = R ^ 4`. Rewrite using `[hRdef, mul_comm, Real.rpow_mul hr0.le]`. Conclude with `Real.rpow_natCast (r ^ |Cst|) 4` after adjusting the coercions. Rewrite using `[hR4]`. Rewrite `hGb` using `[← hRdef]`.

Take `⟨Ex, hEx⟩ : ∃ Ex : ℝ, Ex = Real.exp (r / 2)` from `⟨_, rfl⟩`. Rewrite `hGb`, the goal using `[← hEx]`. Establish `hE1 : 1 ≤ Ex` using `hEx ▸ Real.one_le_exp (by linarith)`. Establish `hGp : (G u).PosDef` using `hev.self_of_nhds.1`. Apply the tactic sequence `have hGe : ∀ p q, ‖G u p q‖ ≤ t := entry N (G u) t hGp.posSemidef hs1`.

Establish `hVa : ∀ y a c, (A y * selM S) a c = A y a (S.orderEmbOfFin rfl c)` using `fun y a c => GramPot.mul_selM_apply _ S a c`. Establish `hVd : ∀ p q, DifferentiableAt ℝ (fun y => (A y * selM S) p q) u` using `fun p q => by`. Simplify using `only [hVa]`. Conclude with `hAd _ _`. Establish `hlow` using `lower N S (G u) (A u) t a₀ ht0 hs2 hAa`.

Establish `ha' : 0 < a₀ / t` using `div_pos ha ht0`. Establish `hdet` using `detpos _ _ _ ha' hlow`. Use `⟨diff N S.card E G (fun y => A y * selM S) u hGd hVd hdet.ne', ?_⟩` and prove the remaining obligations. Establish `hb0 : 0 < b` using `by linarith`. Establish `hP : 0 < b * R` using `by positivity`.

Establish `hPQ : b * R ≤ b * R * Ex` using `le_mul_of_one_le_right hP.le hE1`. Establish `hbR : b ≤ b * R` using `le_mul_of_one_le_right hb0.le hR1`. Establish `hmain` using `GlobalTheory.T.gram_matrix_sub_scalar_posSemidef N S.card E G (fun y => A y * selM S) u (a₀ / t) (b * R) (b * R * Ex) ha' hP hPQ hGd hVd (hev.mono fun y hy => ⟨hy.1, GramPot.linearIndependent_mul_selM hy.2 S⟩) hlow (fun p q => ⟨(hGe p q).trans (htR.trans (le_mul_of_one_le_left (b …`. Rewrite using `[hVa]; exact (hAb _ _).1.trans hbR, by`. Simplify using `only [hVa]`.

Conclude with `(hAb _ _).2.trans (hbR.trans hPQ)⟩)`. Use `hmain.trans ?_` and prove the remaining obligations. Establish `hk : (S.card : ℝ) ≤ N`. Use `S.card_le_univ` as an intermediate fact. Simplify using `only [Fintype.card_fin] at this`.

Conclude with `this` after adjusting the coercions. Establish `hk2 : (S.card : ℝ) ^ 2 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4`. Establish `: (S.card : ℝ) ^ 2 ≤ (N : ℝ) ^ 2` using `pow_le_pow_left₀ (by positivity) hk 2`. Use polynomial arithmetic with `[sq_nonneg ((N : ℝ) ^ 2 )]`. Establish `e1 : 3 * (S.card : ℝ) ^ 2 * (N : ℝ) ^ 2 * (b * R) ^ 2 * (b * R * Ex) / (a₀ / t) = 3 * ((S.card : ℝ) ^ 2 * (N : ℝ) ^ 2) * b ^ 3 * (R ^ 3 * t) * Ex / a₀`.

Clear the denominators using the available nonvanishing facts. Establish `e2 : 3 * (N : ℝ) ^ 4 * b ^ 3 * R ^ 4 * Ex / a₀ = 3 * (N : ℝ) ^ 4 * b ^ 3 * (R ^ 3 * R) * Ex / a₀` using `by ring`. Rewrite using `[e1, e2]`. Use `gcongr`.
-/
theorem gramterm : ∀ (N : ℕ) (S : Finset (Fin N)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (G A : E → Matrix (Fin N) (Fin N) ℂ) (u : E) (b a₀ Cst r : ℝ), 1 ≤ b → 0 < a₀ → 1 ≤ r → (∀ p q, DifferentiableAt ℝ (fun y => G y p q) u) → (∀ p q, DifferentiableAt ℝ (fun y => A y p q) u) → (∀ᶠ y in nhds u, (G y).PosDef ∧ (A y).det ≠ 0) → (((r ^ Cst : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G u).PosSemidef → (((r ^ Cst : ℝ) : ℂ) • G u - 1).PosSemidef → (∀ p q, ‖fderiv ℝ (fun y => G y p q) u‖ ≤ b * r ^ |Cst| * Real.exp (r / 2)) → (∀ p q, ‖A u p q‖ ≤ b ∧ ‖fderiv ℝ (fun y => A y p q) u‖ ≤ b) → ((A u)ᴴ * A u - (a₀ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef → DifferentiableAt ℝ (fun y => Real.log ((A y * selM S)ᴴ * G y * (A y * selM S)).det.re) u ∧ ‖fderiv ℝ (fun y => Real.log ((A y * selM S)ᴴ * G y * (A y * selM S)).det.re) u‖ ≤ 3 * (N : ℝ) ^ 4 * b ^ 3 * r ^ (4 * |Cst|) * Real.exp (r / 2) / a₀ := by
  intro N S E _ _ G A u b a₀ Cst r hb ha hr hGd hAd hev hs1 hs2 hGb hAb hAa
  have hr0 : 0 < r := by linarith
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = r ^ Cst := ⟨_, rfl⟩
  rw [← htdef] at hs1 hs2
  have ht0 : 0 < t := htdef ▸ Real.rpow_pos_of_pos hr0 _
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = r ^ |Cst| := ⟨_, rfl⟩
  have htR : t ≤ R := by
    rw [htdef, hRdef]; exact Real.rpow_le_rpow_of_exponent_le hr (le_abs_self _)
  have hR1 : 1 ≤ R := hRdef ▸ Real.one_le_rpow hr (abs_nonneg _)
  have hR4 : r ^ (4 * |Cst|) = R ^ 4 := by
    rw [hRdef, mul_comm, Real.rpow_mul hr0.le]
    exact_mod_cast Real.rpow_natCast (r ^ |Cst|) 4
  rw [hR4]
  rw [← hRdef] at hGb
  obtain ⟨Ex, hEx⟩ : ∃ Ex : ℝ, Ex = Real.exp (r / 2) := ⟨_, rfl⟩
  rw [← hEx] at hGb ⊢
  have hE1 : 1 ≤ Ex := hEx ▸ Real.one_le_exp (by linarith)
  have hGp : (G u).PosDef := hev.self_of_nhds.1
  have hGe : ∀ p q, ‖G u p q‖ ≤ t := entry N (G u) t hGp.posSemidef hs1
  have hVa : ∀ y a c, (A y * selM S) a c = A y a (S.orderEmbOfFin rfl c) := fun y a c =>
    GramPot.mul_selM_apply _ S a c
  have hVd : ∀ p q, DifferentiableAt ℝ (fun y => (A y * selM S) p q) u := fun p q => by
    simp only [hVa]; exact hAd _ _
  have hlow := lower N S (G u) (A u) t a₀ ht0 hs2 hAa
  have ha' : 0 < a₀ / t := div_pos ha ht0
  have hdet := detpos _ _ _ ha' hlow
  refine ⟨diff N S.card E G (fun y => A y * selM S) u hGd hVd hdet.ne', ?_⟩
  have hb0 : 0 < b := by linarith
  have hP : 0 < b * R := by positivity
  have hPQ : b * R ≤ b * R * Ex := le_mul_of_one_le_right hP.le hE1
  have hbR : b ≤ b * R := le_mul_of_one_le_right hb0.le hR1
  have hmain := GlobalTheory.T.gram_matrix_sub_scalar_posSemidef N S.card E G (fun y => A y * selM S) u (a₀ / t) (b * R) (b * R * Ex) ha' hP hPQ
    hGd hVd (hev.mono fun y hy => ⟨hy.1, GramPot.linearIndependent_mul_selM hy.2 S⟩) hlow
    (fun p q => ⟨(hGe p q).trans (htR.trans (le_mul_of_one_le_left (by linarith) hb)), hGb p q⟩)
    (fun p q => ⟨by
        show ‖(A u * selM S) p q‖ ≤ _
        rw [hVa]; exact (hAb _ _).1.trans hbR, by
        simp only [hVa]
        exact (hAb _ _).2.trans (hbR.trans hPQ)⟩)
  refine hmain.trans ?_
  have hk : (S.card : ℝ) ≤ N := by
    have := S.card_le_univ
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hk2 : (S.card : ℝ) ^ 2 * (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 4 := by
    have : (S.card : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hk 2
    nlinarith [sq_nonneg ((N : ℝ) ^ 2 )]
  have e1 : 3 * (S.card : ℝ) ^ 2 * (N : ℝ) ^ 2 * (b * R) ^ 2 * (b * R * Ex) / (a₀ / t) =
      3 * ((S.card : ℝ) ^ 2 * (N : ℝ) ^ 2) * b ^ 3 * (R ^ 3 * t) * Ex / a₀ := by
    field_simp
  have e2 : 3 * (N : ℝ) ^ 4 * b ^ 3 * R ^ 4 * Ex / a₀ = 3 * (N : ℝ) ^ 4 * b ^ 3 * (R ^ 3 * R) * Ex / a₀ := by ring
  rw [e1, e2]
  gcongr

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j n : ℕ}

/- English proof (translation)
Establish `h` using `BM.norm_le x`. Establish `h1 : (1 : ℝ) ≤ Real.exp 1` using `Real.one_le_exp zero_le_one`. Unfold `rW`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_rW {M : FlagModel y Ψ N j} (BM : BaseMetric M n) (x : BM.Rb.X) :
    1 ≤ rW BM.L BM.s x := by
  have h := BM.norm_le x
  have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  unfold rW
  linarith

/- English proof (translation)
Take `⟨k, hk, hkb⟩` from `BM.adapted.2.2.1 (pr x₀)`. Use `set ψ := A.chart i with hψ`. Use `set φ := BM.Bat.chart k with hφ`. Use `set f : (Fin e → ℂ) → (Fin n → ℂ) := φ ∘ pr ∘ ψ.symm with hfdef`. Establish `hf : AnalyticAt ℂ f (ψ x₀)` using `patchmap e n X BM.Rb.X A BM.Rb.A BM.Bat pr hp BM.adapted.1 i k x₀ hi hk`.

Establish `hu₀ : ψ x₀ ∈ ψ.target` using `ψ.map_source hi`. Establish `hsx : ψ.symm (ψ x₀) = x₀` using `ψ.left_inv hi`. Establish `hf0 : f (ψ x₀) ∈ Metric.ball (0 : Fin n → ℂ) 1`. Simplify `hkb` using `only [hfdef, Function.comp, hsx]`. Establish `hfc : ContinuousAt f (ψ x₀)` using `hf.continuousAt`.

Establish `hfd : ContDiffAt ℝ 2 f (ψ x₀)` using `(hf.contDiffAt (n := 2)).restrict_scalars ℝ`. Establish `hfdc : ContinuousAt (fderiv ℝ f) (ψ x₀)` using `hfd.fderiv_right (m := 1) (by norm_num) |>.continuousAt`. Establish `hprc : ContinuousAt (fun u => pr (ψ.symm u)) (ψ x₀)` using `hp.1.continuousAt.comp (ψ.continuousAt_symm hu₀)`. Establish `e1 : ∀ᶠ u in nhds (ψ x₀), u ∈ ψ.target` using `ψ.open_target.mem_nhds hu₀`. Establish `e2 : ∀ᶠ u in nhds (ψ x₀), pr (ψ.symm u) ∈ φ.source` using `hprc.eventually_mem (φ.open_source.mem_nhds (by simpa only [hsx] using hk))`.

Establish `e3 : ∀ᶠ u in nhds (ψ x₀), f u ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2)` using `hfc.eventually_mem (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by norm_num) hf0))`. Establish `e4 : ∀ᶠ u in nhds (ψ x₀), ‖fderiv ℝ f u‖ < ‖fderiv ℝ f (ψ x₀)‖ + 1` using `hfdc.norm.eventually_lt continuousAt_const (by linarith)`. Establish `e5 : ∀ᶠ u in nhds (ψ x₀), DifferentiableAt ℝ f u` using `hf.eventually_analyticAt.mono fun u hu => hu.differentiableAt.restrictScalars ℝ`. Use `⟨|BM.Cst| * (‖fderiv ℝ f (ψ x₀)‖ + 1), by positivity, ?_⟩` and prove the remaining obligations. Establish `e12` using `e1.and e2`.

Use `filter_upwards [e12.eventually_nhds, e12, e3, e4, e5] with u hnear hu hball hfb hdf l τ a b hz`. Establish `hsymw : φ.symm (f u) = pr (ψ.symm u)` using `φ.left_inv hu.2`. Establish `hw : f u ∈ φ.target` using `φ.map_source hu.2`. Establish `hOo : IsOpen (BM.O l \ bdry BM.s)` using `(BM.O_open l).sdiff (GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection n BM.Rb.X BM.Rb.A BM.L BM.s BM.sec)`. Establish `hz' : φ.symm (f u) ∈ BM.O l \ bdry BM.s` using `by rw [hsymw]; exact hz`.

Establish `hre` using `gdiff n BM.Rb.X BM.Rb.A BM.Bat BM.adapted.1 _ hOo _ (BM.G_smooth l τ a b).1 k (f u) hw hz'`. Establish `him` using `gdiff n BM.Rb.X BM.Rb.A BM.Bat BM.adapted.1 _ hOo _ (BM.G_smooth l τ a b).2 k (f u) hw hz'`. Use `set h : (Fin n → ℂ) → ℂ := fun w' => BM.G l τ (φ.symm w') a b with hh`. Establish `hhd : DifferentiableAt ℝ h (f u)`. Establish `e : h = fun w' => (((BM.G l τ (φ.symm w') a b).re : ℝ) : ℂ) + (((BM.G l τ (φ.symm w') a b).im : ℝ) : ℂ) * Complex.I`.

Use function extensionality and compare the values at `w'`. Conclude with `(Complex.re_add_im _).symm`. Rewrite using `[e]`. Conclude with `((Complex.ofRealCLM.differentiableAt.comp _ hre).add ((Complex.ofRealCLM.differentiableAt.comp _ him).mul_const _))`. Establish `heq : (fun y => BM.G l τ (pr (ψ.symm y)) a b) =ᶠ[nhds u] h ∘ f` using `by filter_upwards [hnear] with y hy show BM.G l τ (pr (ψ.symm y)) a b = BM.G l τ (φ.symm (φ (pr (ψ.symm y)))) a b`.

Rewrite using `[φ.left_inv hy.2]`. Establish `hcomp : HasFDerivAt (h ∘ f) ((fderiv ℝ h (f u)).comp (fderiv ℝ f u)) u` using `hhd.hasFDerivAt.comp u hdf.hasFDerivAt`. Use `⟨(hcomp.differentiableAt).congr_of_eventuallyEq heq, ?_⟩` and prove the remaining obligations. Rewrite using `[heq.fderiv_eq, hcomp.fderiv]`. Use `set r := rW BM.L BM.s (pr (ψ.symm u)) with hr`.

Establish `hr1 : 1 ≤ r` using `one_le_rW BM _`. Establish `hg : ‖fderiv ℝ h (f u)‖ ≤ BM.Cst * r ^ BM.Cst * Real.exp (r / 2)`. Use `BM.grad l τ a b k (f u) hball hz'` as an intermediate fact. Rewrite `this` using `[← hφ, hsymw]`. Conclude with `this`.

Establish `hpow : r ^ BM.Cst ≤ r ^ |BM.Cst|` using `Real.rpow_le_rpow_of_exponent_le hr1 (le_abs_self _)`. Establish `hr0 : 0 < r` using `by linarith`. Establish `hg' : ‖fderiv ℝ h (f u)‖ ≤ |BM.Cst| * r ^ |BM.Cst| * Real.exp (r / 2)`. Use `hg.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)` and prove the remaining obligations. Conclude with `mul_le_mul (le_abs_self _) hpow (Real.rpow_nonneg hr0.le _) (abs_nonneg _)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem base_grad {M : FlagModel y Ψ N j} (BM : BaseMetric M n) {e : ℕ} {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (pr : X → BM.Rb.X) (hp : HoloMap A BM.Rb.A pr) (i : Fin A.n) (x₀ : X)
    (hi : x₀ ∈ (A.chart i).source) :
    ∃ c₁ : ℝ, 0 ≤ c₁ ∧ ∀ᶠ u in nhds (A.chart i x₀), ∀ (l : Fin BM.q) (τ : Ψ) (a b : Fin N),
      pr ((A.chart i).symm u) ∈ BM.O l \ bdry BM.s →
      DifferentiableAt ℝ (fun y => BM.G l τ (pr ((A.chart i).symm y)) a b) u ∧
      ‖fderiv ℝ (fun y => BM.G l τ (pr ((A.chart i).symm y)) a b) u‖ ≤
        c₁ * rW BM.L BM.s (pr ((A.chart i).symm u)) ^ |BM.Cst| *
          Real.exp (rW BM.L BM.s (pr ((A.chart i).symm u)) / 2) := by
  obtain ⟨k, hk, hkb⟩ := BM.adapted.2.2.1 (pr x₀)
  set ψ := A.chart i with hψ
  set φ := BM.Bat.chart k with hφ
  set f : (Fin e → ℂ) → (Fin n → ℂ) := φ ∘ pr ∘ ψ.symm with hfdef
  have hf : AnalyticAt ℂ f (ψ x₀) := patchmap e n X BM.Rb.X A BM.Rb.A BM.Bat pr hp BM.adapted.1 i k x₀ hi hk
  have hu₀ : ψ x₀ ∈ ψ.target := ψ.map_source hi
  have hsx : ψ.symm (ψ x₀) = x₀ := ψ.left_inv hi
  have hf0 : f (ψ x₀) ∈ Metric.ball (0 : Fin n → ℂ) 1 := by
    simpa only [hfdef, Function.comp, hsx] using hkb
  have hfc : ContinuousAt f (ψ x₀) := hf.continuousAt
  have hfd : ContDiffAt ℝ 2 f (ψ x₀) := (hf.contDiffAt (n := 2)).restrict_scalars ℝ
  have hfdc : ContinuousAt (fderiv ℝ f) (ψ x₀) := hfd.fderiv_right (m := 1) (by norm_num) |>.continuousAt
  have hprc : ContinuousAt (fun u => pr (ψ.symm u)) (ψ x₀) :=
    hp.1.continuousAt.comp (ψ.continuousAt_symm hu₀)
  have e1 : ∀ᶠ u in nhds (ψ x₀), u ∈ ψ.target := ψ.open_target.mem_nhds hu₀
  have e2 : ∀ᶠ u in nhds (ψ x₀), pr (ψ.symm u) ∈ φ.source :=
    hprc.eventually_mem (φ.open_source.mem_nhds (by simpa only [hsx] using hk))
  have e3 : ∀ᶠ u in nhds (ψ x₀), f u ∈ Metric.ball (0 : Fin n → ℂ) (3 / 2) :=
    hfc.eventually_mem (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball (by norm_num) hf0))
  have e4 : ∀ᶠ u in nhds (ψ x₀), ‖fderiv ℝ f u‖ < ‖fderiv ℝ f (ψ x₀)‖ + 1 :=
    hfdc.norm.eventually_lt continuousAt_const (by linarith)
  have e5 : ∀ᶠ u in nhds (ψ x₀), DifferentiableAt ℝ f u :=
    hf.eventually_analyticAt.mono fun u hu => hu.differentiableAt.restrictScalars ℝ
  refine ⟨|BM.Cst| * (‖fderiv ℝ f (ψ x₀)‖ + 1), by positivity, ?_⟩
  have e12 := e1.and e2
  filter_upwards [e12.eventually_nhds, e12, e3, e4, e5] with u hnear hu hball hfb hdf l τ a b hz
  have hsymw : φ.symm (f u) = pr (ψ.symm u) := φ.left_inv hu.2
  have hw : f u ∈ φ.target := φ.map_source hu.2
  have hOo : IsOpen (BM.O l \ bdry BM.s) :=
    (BM.O_open l).sdiff (GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection n BM.Rb.X BM.Rb.A BM.L BM.s BM.sec)
  have hz' : φ.symm (f u) ∈ BM.O l \ bdry BM.s := by rw [hsymw]; exact hz
  have hre := gdiff n BM.Rb.X BM.Rb.A BM.Bat BM.adapted.1 _ hOo _ (BM.G_smooth l τ a b).1 k (f u) hw hz'
  have him := gdiff n BM.Rb.X BM.Rb.A BM.Bat BM.adapted.1 _ hOo _ (BM.G_smooth l τ a b).2 k (f u) hw hz'
  set h : (Fin n → ℂ) → ℂ := fun w' => BM.G l τ (φ.symm w') a b with hh
  have hhd : DifferentiableAt ℝ h (f u) := by
    have e : h = fun w' => (((BM.G l τ (φ.symm w') a b).re : ℝ) : ℂ) + (((BM.G l τ (φ.symm w') a b).im : ℝ) : ℂ) * Complex.I := by
      funext w'
      exact (Complex.re_add_im _).symm
    rw [e]
    exact ((Complex.ofRealCLM.differentiableAt.comp _ hre).add
      ((Complex.ofRealCLM.differentiableAt.comp _ him).mul_const _))
  have heq : (fun y => BM.G l τ (pr (ψ.symm y)) a b) =ᶠ[nhds u] h ∘ f := by
    filter_upwards [hnear] with y hy
    show BM.G l τ (pr (ψ.symm y)) a b = BM.G l τ (φ.symm (φ (pr (ψ.symm y)))) a b
    rw [φ.left_inv hy.2]
  have hcomp : HasFDerivAt (h ∘ f) ((fderiv ℝ h (f u)).comp (fderiv ℝ f u)) u :=
    hhd.hasFDerivAt.comp u hdf.hasFDerivAt
  refine ⟨(hcomp.differentiableAt).congr_of_eventuallyEq heq, ?_⟩
  rw [heq.fderiv_eq, hcomp.fderiv]
  set r := rW BM.L BM.s (pr (ψ.symm u)) with hr
  have hr1 : 1 ≤ r := one_le_rW BM _
  have hg : ‖fderiv ℝ h (f u)‖ ≤ BM.Cst * r ^ BM.Cst * Real.exp (r / 2) := by
    have := BM.grad l τ a b k (f u) hball hz'
    rw [← hφ, hsymw] at this
    exact this
  have hpow : r ^ BM.Cst ≤ r ^ |BM.Cst| := Real.rpow_le_rpow_of_exponent_le hr1 (le_abs_self _)
  have hr0 : 0 < r := by linarith
  have hg' : ‖fderiv ℝ h (f u)‖ ≤ |BM.Cst| * r ^ |BM.Cst| * Real.exp (r / 2) := by
    refine hg.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
    exact mul_le_mul (le_abs_self _) hpow (Real.rpow_nonneg hr0.le _) (abs_nonneg _)
  calc ‖(fderiv ℝ h (f u)).comp (fderiv ℝ f u)‖ ≤ ‖fderiv ℝ h (f u)‖ * ‖fderiv ℝ f u‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (|BM.Cst| * r ^ |BM.Cst| * Real.exp (r / 2)) * (‖fderiv ℝ f (ψ x₀)‖ + 1) :=
        mul_le_mul hg' hfb.le (norm_nonneg _) (by positivity)
    _ = _ := by ring

/- English proof (translation)
Use `set c := T + c₂ + 4 * C with hcdef`. Establish `h1 : r ^ (4 * C) ≤ r ^ c` using `Real.rpow_le_rpow_of_exponent_le hr (by rw [hcdef]; linarith)`. Establish `h2 : 1 ≤ r ^ c` using `Real.one_le_rpow hr (by rw [hcdef]; positivity)`. Establish `hP : 0 ≤ r ^ c` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.

Establish `a1 : T * r ^ (4 * C) * E ≤ T * r ^ c * E` using `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hT) (by linarith)`. Establish `a2 : c₂ * 1 ≤ c₂ * (r ^ c * E)` using `mul_le_mul_of_nonneg_left (by nlinarith) hc`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ ≤ c * r ^ c * E := by`. Establish `: 0 ≤ 4 * C * (r ^ c * E)` using `by positivity`.

Rewrite `this`, the goal using `[hcdef]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem final_arith (T c₂ C r E : ℝ) (hT : 0 ≤ T) (hc : 0 ≤ c₂) (hC : 0 ≤ C) (hr : 1 ≤ r) (hE : 1 ≤ E) :
    T * r ^ (4 * C) * E + c₂ ≤ (T + c₂ + 4 * C) * r ^ (T + c₂ + 4 * C) * E := by
  set c := T + c₂ + 4 * C with hcdef
  have h1 : r ^ (4 * C) ≤ r ^ c := Real.rpow_le_rpow_of_exponent_le hr (by rw [hcdef]; linarith)
  have h2 : 1 ≤ r ^ c := Real.one_le_rpow hr (by rw [hcdef]; positivity)
  have hP : 0 ≤ r ^ c := by linarith
  calc T * r ^ (4 * C) * E + c₂ ≤ T * r ^ c * E + c₂ * (r ^ c * E) := by
        have a1 : T * r ^ (4 * C) * E ≤ T * r ^ c * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hT) (by linarith)
        have a2 : c₂ * 1 ≤ c₂ * (r ^ c * E) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hc
        linarith
    _ ≤ c * r ^ c * E := by
        have : 0 ≤ 4 * C * (r ^ c * E) := by positivity
        rw [hcdef] at this ⊢
        nlinarith

/- English proof (translation)
Establish `hs` using `((h₁.1.hasFDerivAt.add h₂.1.hasFDerivAt).add h₃.1.hasFDerivAt).const_mul (1 / 2 : ℝ)`. Establish `hd` using `(hs.add h₄.1.hasFDerivAt).fderiv`. Establish `hT : 0 ≤ T` using `(norm_nonneg _).trans h₁.2`. Establish `e : (fun y => (1 / 2) * (t₁ y + t₂ y + t₃ y) + B y) = (fun y => (1 / 2 : ℝ) * ((t₁ + t₂ + t₃) y)) + B` using `rfl`. Rewrite using `[e, hd]`.

Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Establish `n1 : ‖(1 / 2 : ℝ) • (fderiv ℝ t₁ u + fderiv ℝ t₂ u + fderiv ℝ t₃ u)‖ ≤ 2 * T`. Rewrite using `[norm_smul]`. Use `norm_add₃_le (a := fderiv ℝ t₁ u) (b := fderiv ℝ t₂ u) (c := fderiv ℝ t₃ u)` as an intermediate fact. Establish `h' : ‖(1 / 2 : ℝ)‖ = 1 / 2` using `by norm_num`.

Rewrite using `[h']`. Combine the linear relations using `[h₁.2, h₂.2, h₃.2]`. Combine the linear relations using `[h₄.2]`.
-/
theorem norm_fderiv_comb {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (t₁ t₂ t₃ B : E → ℝ) (u : E)
    (T c : ℝ) (h₁ : DifferentiableAt ℝ t₁ u ∧ ‖fderiv ℝ t₁ u‖ ≤ T)
    (h₂ : DifferentiableAt ℝ t₂ u ∧ ‖fderiv ℝ t₂ u‖ ≤ T)
    (h₃ : DifferentiableAt ℝ t₃ u ∧ ‖fderiv ℝ t₃ u‖ ≤ T)
    (h₄ : DifferentiableAt ℝ B u ∧ ‖fderiv ℝ B u‖ ≤ c) :
    ‖fderiv ℝ (fun y => (1 / 2) * (t₁ y + t₂ y + t₃ y) + B y) u‖ ≤ 2 * T + c := by
  have hs := ((h₁.1.hasFDerivAt.add h₂.1.hasFDerivAt).add h₃.1.hasFDerivAt).const_mul (1 / 2 : ℝ)
  have hd := (hs.add h₄.1.hasFDerivAt).fderiv
  have hT : 0 ≤ T := (norm_nonneg _).trans h₁.2
  have e : (fun y => (1 / 2) * (t₁ y + t₂ y + t₃ y) + B y) =
      (fun y => (1 / 2 : ℝ) * ((t₁ + t₂ + t₃) y)) + B := rfl
  rw [e, hd]
  refine (norm_add_le _ _).trans ?_
  have n1 : ‖(1 / 2 : ℝ) • (fderiv ℝ t₁ u + fderiv ℝ t₂ u + fderiv ℝ t₃ u)‖ ≤ 2 * T := by
    rw [norm_smul]
    have := norm_add₃_le (a := fderiv ℝ t₁ u) (b := fderiv ℝ t₂ u) (c := fderiv ℝ t₃ u)
    have h' : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [h']
    linarith [h₁.2, h₂.2, h₃.2]
  linarith [h₄.2]

/- English proof (translation)
Distinguish the cases in `hc : c`. Simplify `h hc` using `only [if_pos hc]`. Simplify using `only [if_neg hc]`. Conclude with `⟨differentiableAt_const _, by simpa using hT⟩`.
-/
theorem ite_term {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : Prop) [Decidable c] (t : E → ℝ)
    (u : E) (T : ℝ) (hT : 0 ≤ T) (h : c → DifferentiableAt ℝ t u ∧ ‖fderiv ℝ t u‖ ≤ T) :
    DifferentiableAt ℝ (fun y => if c then t y else 0) u ∧
      ‖fderiv ℝ (fun y => if c then t y else 0) u‖ ≤ T := by
  by_cases hc : c
  · simpa only [if_pos hc] using h hc
  · simp only [if_neg hc]
    exact ⟨differentiableAt_const _, by simpa using hT⟩

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hSC hPot x₀`. Take `⟨W, l, H, D, hW, hx₀W, hWU, hWO, hH, hHd, hD, hDne, hform⟩` from `hSC x₀ x₀ (R.mem_U x₀)`. Take `⟨i, hi⟩` from `R.A.cover x₀`. Use `set ψ := R.A.chart i with hψ`. Establish `hu₀ : ψ x₀ ∈ ψ.target` using `ψ.map_source hi`.

Establish `hsx : ψ.symm (ψ x₀) = x₀` using `ψ.left_inv hi`. Establish `hWm : ∀ᶠ u in nhds (ψ x₀), u ∈ ψ.target ∧ ψ.symm u ∈ W`. Establish `h1` using `ψ.open_target.mem_nhds hu₀`. Establish `h2 : ∀ᶠ u in nhds (ψ x₀), ψ.symm u ∈ W` using `(ψ.continuousAt_symm hu₀).eventually_mem (hW.mem_nhds (by rw [hsx]; exact hx₀W))`. Conclude with `Filter.Eventually.and h1 h2`.

Establish `hHan : ∀ a b, AnalyticAt ℂ (fun u => H (ψ.symm u) a b) (ψ x₀)` using `fun a b => hH a b i (ψ x₀) ⟨hu₀, by show ψ.symm (ψ x₀) ∈ W; rw [hsx]; exact hx₀W⟩`. Take `⟨b, a₀, hb, ha₀, ha₁, hfr⟩` from `frame N e (fun u => H (ψ.symm u)) (ψ x₀) hHan (by simpa only [hsx] using (hHd x₀ hx₀W).2)`. Take `⟨c₁, hc₁, hbase⟩` from `base_grad BM R.A pr hp i x₀ hi`. Take `⟨c₂, hc₂, hrest⟩` from `rest e R.X R.A i x₀ W D (fun y' => Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x₀ y'))) hW hx₀W hi hD hDne (fun j' => ((hPot.1 x₀) j').mono (fun w hw => ⟨hw.1, hWU hw.2⟩))`. Establish `hall` using `hWm.and (hfr.and (hbase.and hrest))`.

Take `⟨t, ht, htO, hut⟩` from `eventually_nhds_iff.1 hall`. Establish `hclosed : IsClosed (bdry BM.s)` using `GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection n BM.Rb.X BM.Rb.A BM.L BM.s BM.sec`. Use `set b' := b + c₁ with hb'`. Establish `hb'1 : 1 ≤ b'` using `by rw [hb']; linarith`. Use `set Tc : ℝ := 3 * (N : ℝ) ^ 4 * b' ^ 3 / a₀ with hTc`.

Establish `hTc0 : 0 ≤ Tc` using `by rw [hTc]; positivity`. Use `⟨ψ, ψ.source ∩ ψ ⁻¹' t, 2 * Tc + c₂ + 4 * |BM.Cst|, fun j' => ⟨R.A.holo j' i, R.A.holo i j'⟩, ψ.isOpen_inter_preimage htO, ⟨hi, hut⟩, Set.inter_subset_left, ?_⟩` and prove the remaining obligations. Introduce and unpack `x' ⟨hx's, hx't⟩ hbd`. Establish `hxs : ψ.symm (ψ x') = x'` using `ψ.left_inv hx's`. Establish `hprb : pr x' ∉ bdry BM.s` using `hbd`.

Use `set u := ψ x' with hu`. Establish `hut'` using `ht u hx't`. Establish `hprc : ContinuousAt (fun y => pr (ψ.symm y)) u` using `hp.1.continuousAt.comp (ψ.continuousAt_symm hut'.1.1)`. Establish `hnb : ∀ᶠ y in nhds u, pr (ψ.symm y) ∉ bdry BM.s` using `hprc.eventually_mem (hclosed.isOpen_compl.mem_nhds (by show pr (ψ.symm u) ∉ bdry BM.s`. Rewrite using `[hxs]`.

Conclude with `hprb))`. Establish `hnt : ∀ᶠ y in nhds u, y ∈ t` using `htO.mem_nhds hx't`. Establish `hxW : x' ∈ W` using `by simpa only [hxs] using hut'.1.2`. Establish `hxO : pr x' ∈ BM.O l \ bdry BM.s` using `⟨hWO _ hxW, hprb⟩`. Establish `hxO' : pr (ψ.symm u) ∈ BM.O l \ bdry BM.s` using `by rw [hxs]; exact hxO`.

Use `set r := rW BM.L BM.s (pr x') with hr`. Establish `hr1 : 1 ≤ r` using `one_le_rW BM _`. Establish `hexp : 1 ≤ Real.exp (r / 2)` using `Real.one_le_exp (by linarith)`. Use `set Gt : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun y => BM.G l p.1 (pr (ψ.symm y)) with hGt`. Establish `hGu : Gt u = BM.G l p.1 (pr x')` using `by simp only [hGt, hxs]`.

Establish `hGd : ∀ a c, DifferentiableAt ℝ (fun y => Gt y a c) u` using `fun a c => (hut'.2.2.1 l p.1 a c hxO').1`. Establish `hGb : ∀ a c, ‖fderiv ℝ (fun y => Gt y a c) u‖ ≤ b' * r ^ |BM.Cst| * Real.exp (r / 2)` using `fun a c => by`. Establish `h` using `(hut'.2.2.1 l p.1 a c hxO').2`. Rewrite `h` using `[hxs]`. Use `h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) (Real.exp_pos _).le)` and prove the remaining obligations.

Rewrite using `[hb']`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Real.rpow_nonneg (by linarith) _`. Establish `hpos : ∀ᶠ y in nhds u, (Gt y).PosDef ∧ pr (ψ.symm y) ∉ bdry BM.s ∧ y ∈ t` using `by filter_upwards [hnb, hnt] with y hy hyt`. Conclude with `⟨(BM.G_pos l p.1 _ ⟨hWO _ (ht y hyt).1.2, hy⟩).2, hy, hyt⟩`.

Establish `hsz` using `BM.size l p.1 (pr x') hxO`. Establish `hterm : ∀ (S : Finset (Fin N)) (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), (∀ a c, DifferentiableAt ℝ (fun y => A y a c) u) → (∀ᶠ y in nhds u, (A y).det ≠ 0) → (∀ a c, ‖A u a c‖ ≤ b' ∧ ‖fderiv ℝ (fun y => A y a c) u‖ ≤ b') → ((A u)ᴴ * A u - (a₀ : ℂ) • (1 : Matrix (Fin N) (Fin N …`. Introduce `S A h1 h2 h3 h4`. Use `gramterm N S (Fin e → ℂ) Gt A u b' a₀ BM.Cst r hb'1 ha₀ hr1 hGd h1 (hpos.and h2 |>.mono fun y hy => ⟨hy.1.1, hy.2⟩) (by rw [hGu]; exact hsz.1) (by rw [hGu]; exact hsz.2) hGb h3 h4` as an intermediate fact. Use `⟨this.1, this.2.trans (le_of_eq ?_)⟩` and prove the remaining obligations.

Rewrite using `[hTc]`. Expand and normalize the polynomial expressions, which then agree. Use `set T := Tc * r ^ (4 * |BM.Cst|) * Real.exp (r / 2) with hT`. Establish `hT0 : 0 ≤ T` using `by rw [hT]; have : 0 ≤ r ^ (4 * |BM.Cst|) := Real.rpow_nonneg (by linarith) _; positivity`. Establish `hone : ∀ S : Finset (Fin N), DifferentiableAt ℝ (fun y => Real.log ((selM S)ᴴ * Gt y * selM S).det.re) u ∧ ‖fderiv ℝ (fun y => Real.log ((selM S)ᴴ * Gt y * selM S).det.re) u‖ ≤ T`.

Introduce `S`. Establish `h` using `hterm S (fun _ => 1) (fun a c => differentiableAt_const _) (by simp) (fun a c => ⟨?_, by simpa using (by linarith : (0 : ℝ) ≤ b')⟩) ?_`. Simplify `h` using `only [Matrix.one_mul]`. Apply the tactic sequence `rw [Matrix.one_apply] split_ifs <;> simp <;> linarith`. Establish `e1 : ((1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * 1 - (a₀ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) = ((1 - a₀ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)`.

Simplify using `[sub_smul]`. Rewrite using `[e1]`. Conclude with `Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.2 ha₁)`. Establish `hHt` using `hterm (stepCols N j p.2) (fun y => H (ψ.symm y)) (fun a c => (hut'.2.1.1 a c).1) (by filter_upwards [hnt] with y hy using (hHd _ (ht y hy).1.2).2) (fun a c => ⟨(hut'.2.1.1 a c).2.1.trans (by rw [hb']; linarith), (hut'.2.1.1 a c).2.2.trans (by rw [hb']; linarith)⟩) hut'.2.1.2`. Establish `t₁` using `ite_term (j ≤ (p.2 : ℕ) + 1) _ u T hT0 (fun _ => hone (wIdx N j))`.

Establish `t₂` using `ite_term ((p.2 : ℕ) + 1 = N) _ u T hT0 (fun _ => hone (omIdx N j))`. Establish `t₃` using `ite_term (IsProperStep N j p.2) _ u T hT0 (fun _ => hHt)`. Establish `hB` using `hut'.2.2.2`. Establish `heq : (stepPh M BM p v R pr ∘ ψ.symm) =ᶠ[nhds u] fun y => (1 / 2) * ((if j ≤ (p.2 : ℕ) + 1 then Real.log ((selM (wIdx N j))ᴴ * Gt y * selM (wIdx N j)).det.re else 0) + (if (p.2 : ℕ) + 1 = N then Real.log ((selM (omIdx N j))ᴴ * Gt y * selM (omIdx N j)).det.re else 0) + (if IsPrope …` using `by filter_upwards [hpos] with y hy`. Establish `hf` using `hform (ψ.symm y) (ht y hy.2.2).1.2 hy.2.1`.

Establish `hg` using `(GramPot.blockPot_eq_gram N j p.2 (BM.G l p.1 (pr (ψ.symm y))) (H (ψ.symm y))).2.2 hy.1`. Rewrite `hf` using `[hg]`. Use `show stepPh M BM p v R pr (ψ.symm y) = _`. Simplify using `only [hGt]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[heq.fderiv_eq]`. Use `(norm_fderiv_comb _ _ _ _ u T c₂ t₁ t₂ t₃ hB).trans ?_` and prove the remaining obligations. Establish `hfin` using `final_arith (2 * Tc) c₂ |BM.Cst| r (Real.exp (r / 2)) (by positivity) hc₂ (abs_nonneg _) hr1 hexp`. Establish `e2 : 2 * T = 2 * Tc * r ^ (4 * |BM.Cst|) * Real.exp (r / 2)` using `by rw [hT]; ring`. Rewrite using `[e2]`.

Conclude with `hfin`.
-/
theorem stepPh_grad_local : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (V : Set R.X) (c : ℝ), IsCompatChart R.A ψ ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ ∀ x' ∈ V, x' ∉ bdry (fun x y => BM.s (pr x) (pr y)) → ‖fderiv ℝ (stepPh M BM p v R pr ∘ ψ.symm) (ψ x')‖ ≤ c * rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x' ^ c * Real.exp (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x' / 2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hSC hPot x₀
  obtain ⟨W, l, H, D, hW, hx₀W, hWU, hWO, hH, hHd, hD, hDne, hform⟩ := hSC x₀ x₀ (R.mem_U x₀)
  obtain ⟨i, hi⟩ := R.A.cover x₀
  set ψ := R.A.chart i with hψ
  have hu₀ : ψ x₀ ∈ ψ.target := ψ.map_source hi
  have hsx : ψ.symm (ψ x₀) = x₀ := ψ.left_inv hi
  have hWm : ∀ᶠ u in nhds (ψ x₀), u ∈ ψ.target ∧ ψ.symm u ∈ W := by
    have h1 := ψ.open_target.mem_nhds hu₀
    have h2 : ∀ᶠ u in nhds (ψ x₀), ψ.symm u ∈ W :=
      (ψ.continuousAt_symm hu₀).eventually_mem (hW.mem_nhds (by rw [hsx]; exact hx₀W))
    exact Filter.Eventually.and h1 h2
  have hHan : ∀ a b, AnalyticAt ℂ (fun u => H (ψ.symm u) a b) (ψ x₀) := fun a b =>
    hH a b i (ψ x₀) ⟨hu₀, by show ψ.symm (ψ x₀) ∈ W; rw [hsx]; exact hx₀W⟩
  obtain ⟨b, a₀, hb, ha₀, ha₁, hfr⟩ := frame N e (fun u => H (ψ.symm u)) (ψ x₀) hHan
    (by simpa only [hsx] using (hHd x₀ hx₀W).2)
  obtain ⟨c₁, hc₁, hbase⟩ := base_grad BM R.A pr hp i x₀ hi
  obtain ⟨c₂, hc₂, hrest⟩ := rest e R.X R.A i x₀ W D
    (fun y' => Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x₀ y'))) hW hx₀W hi hD hDne
    (fun j' => ((hPot.1 x₀) j').mono (fun w hw => ⟨hw.1, hWU hw.2⟩))
  have hall := hWm.and (hfr.and (hbase.and hrest))
  obtain ⟨t, ht, htO, hut⟩ := eventually_nhds_iff.1 hall
  have hclosed : IsClosed (bdry BM.s) :=
    GlobalTheory.CompanionTheory.Ar.PB.CWeight.isClosed_bdry_of_isSection n BM.Rb.X BM.Rb.A BM.L BM.s BM.sec
  set b' := b + c₁ with hb'
  have hb'1 : 1 ≤ b' := by rw [hb']; linarith
  set Tc : ℝ := 3 * (N : ℝ) ^ 4 * b' ^ 3 / a₀ with hTc
  have hTc0 : 0 ≤ Tc := by rw [hTc]; positivity
  refine ⟨ψ, ψ.source ∩ ψ ⁻¹' t, 2 * Tc + c₂ + 4 * |BM.Cst|, fun j' => ⟨R.A.holo j' i, R.A.holo i j'⟩,
    ψ.isOpen_inter_preimage htO, ⟨hi, hut⟩, Set.inter_subset_left, ?_⟩
  rintro x' ⟨hx's, hx't⟩ hbd
  have hxs : ψ.symm (ψ x') = x' := ψ.left_inv hx's
  have hprb : pr x' ∉ bdry BM.s := hbd
  set u := ψ x' with hu
  have hut' := ht u hx't
  have hprc : ContinuousAt (fun y => pr (ψ.symm y)) u :=
    hp.1.continuousAt.comp (ψ.continuousAt_symm hut'.1.1)
  have hnb : ∀ᶠ y in nhds u, pr (ψ.symm y) ∉ bdry BM.s :=
    hprc.eventually_mem (hclosed.isOpen_compl.mem_nhds (by
      show pr (ψ.symm u) ∉ bdry BM.s
      rw [hxs]; exact hprb))
  have hnt : ∀ᶠ y in nhds u, y ∈ t := htO.mem_nhds hx't
  have hxW : x' ∈ W := by simpa only [hxs] using hut'.1.2
  have hxO : pr x' ∈ BM.O l \ bdry BM.s := ⟨hWO _ hxW, hprb⟩
  have hxO' : pr (ψ.symm u) ∈ BM.O l \ bdry BM.s := by rw [hxs]; exact hxO
  set r := rW BM.L BM.s (pr x') with hr
  have hr1 : 1 ≤ r := one_le_rW BM _
  have hexp : 1 ≤ Real.exp (r / 2) := Real.one_le_exp (by linarith)
  set Gt : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun y => BM.G l p.1 (pr (ψ.symm y)) with hGt
  have hGu : Gt u = BM.G l p.1 (pr x') := by simp only [hGt, hxs]
  have hGd : ∀ a c, DifferentiableAt ℝ (fun y => Gt y a c) u := fun a c =>
    (hut'.2.2.1 l p.1 a c hxO').1
  have hGb : ∀ a c, ‖fderiv ℝ (fun y => Gt y a c) u‖ ≤ b' * r ^ |BM.Cst| * Real.exp (r / 2) := fun a c => by
    have h := (hut'.2.2.1 l p.1 a c hxO').2
    rw [hxs] at h
    refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ ?_) (Real.exp_pos _).le)
    · rw [hb']; linarith
    · exact Real.rpow_nonneg (by linarith) _
  have hpos : ∀ᶠ y in nhds u, (Gt y).PosDef ∧ pr (ψ.symm y) ∉ bdry BM.s ∧ y ∈ t := by
    filter_upwards [hnb, hnt] with y hy hyt
    exact ⟨(BM.G_pos l p.1 _ ⟨hWO _ (ht y hyt).1.2, hy⟩).2, hy, hyt⟩
  have hsz := BM.size l p.1 (pr x') hxO

  have hterm : ∀ (S : Finset (Fin N)) (A : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ),
      (∀ a c, DifferentiableAt ℝ (fun y => A y a c) u) → (∀ᶠ y in nhds u, (A y).det ≠ 0) →
      (∀ a c, ‖A u a c‖ ≤ b' ∧ ‖fderiv ℝ (fun y => A y a c) u‖ ≤ b') →
      ((A u)ᴴ * A u - (a₀ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef →
      DifferentiableAt ℝ (fun y => Real.log ((A y * selM S)ᴴ * Gt y * (A y * selM S)).det.re) u ∧
      ‖fderiv ℝ (fun y => Real.log ((A y * selM S)ᴴ * Gt y * (A y * selM S)).det.re) u‖ ≤
        Tc * r ^ (4 * |BM.Cst|) * Real.exp (r / 2) := by
    intro S A h1 h2 h3 h4
    have := gramterm N S (Fin e → ℂ) Gt A u b' a₀ BM.Cst r hb'1 ha₀ hr1 hGd h1
      (hpos.and h2 |>.mono fun y hy => ⟨hy.1.1, hy.2⟩) (by rw [hGu]; exact hsz.1) (by rw [hGu]; exact hsz.2)
      hGb h3 h4
    refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
    rw [hTc]; ring
  set T := Tc * r ^ (4 * |BM.Cst|) * Real.exp (r / 2) with hT
  have hT0 : 0 ≤ T := by rw [hT]; have : 0 ≤ r ^ (4 * |BM.Cst|) := Real.rpow_nonneg (by linarith) _; positivity
  have hone : ∀ S : Finset (Fin N), DifferentiableAt ℝ (fun y => Real.log ((selM S)ᴴ * Gt y * selM S).det.re) u ∧
      ‖fderiv ℝ (fun y => Real.log ((selM S)ᴴ * Gt y * selM S).det.re) u‖ ≤ T := by
    intro S
    have h := hterm S (fun _ => 1) (fun a c => differentiableAt_const _) (by simp)
      (fun a c => ⟨?_, by simpa using (by linarith : (0 : ℝ) ≤ b')⟩) ?_
    · simpa only [Matrix.one_mul] using h
    · rw [Matrix.one_apply]
      split_ifs <;> simp <;> linarith
    · have e1 : ((1 : Matrix (Fin N) (Fin N) ℂ)ᴴ * 1 - (a₀ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) =
          ((1 - a₀ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := by
        simp [sub_smul]
      rw [e1]
      exact Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.2 ha₁)
  have hHt := hterm (stepCols N j p.2) (fun y => H (ψ.symm y))
    (fun a c => (hut'.2.1.1 a c).1)
    (by filter_upwards [hnt] with y hy using (hHd _ (ht y hy).1.2).2)
    (fun a c => ⟨(hut'.2.1.1 a c).2.1.trans (by rw [hb']; linarith),
      (hut'.2.1.1 a c).2.2.trans (by rw [hb']; linarith)⟩)
    hut'.2.1.2
  have t₁ := ite_term (j ≤ (p.2 : ℕ) + 1) _ u T hT0 (fun _ => hone (wIdx N j))
  have t₂ := ite_term ((p.2 : ℕ) + 1 = N) _ u T hT0 (fun _ => hone (omIdx N j))
  have t₃ := ite_term (IsProperStep N j p.2) _ u T hT0 (fun _ => hHt)
  have hB := hut'.2.2.2
  have heq : (stepPh M BM p v R pr ∘ ψ.symm) =ᶠ[nhds u] fun y =>
      (1 / 2) * ((if j ≤ (p.2 : ℕ) + 1 then Real.log ((selM (wIdx N j))ᴴ * Gt y * selM (wIdx N j)).det.re else 0) +
        (if (p.2 : ℕ) + 1 = N then Real.log ((selM (omIdx N j))ᴴ * Gt y * selM (omIdx N j)).det.re else 0) +
        (if IsProperStep N j p.2 then Real.log ((H (ψ.symm y) * selM (stepCols N j p.2))ᴴ * Gt y * (H (ψ.symm y) * selM (stepCols N j p.2))).det.re else 0)) +
      (Real.log ‖D (ψ.symm y)‖ - Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift x₀ (ψ.symm y)))) := by
    filter_upwards [hpos] with y hy
    have hf := hform (ψ.symm y) (ht y hy.2.2).1.2 hy.2.1
    have hg := (GramPot.blockPot_eq_gram N j p.2 (BM.G l p.1 (pr (ψ.symm y))) (H (ψ.symm y))).2.2 hy.1
    rw [hg] at hf
    show stepPh M BM p v R pr (ψ.symm y) = _
    simp only [hGt]
    linarith
  rw [heq.fderiv_eq]
  refine (norm_fderiv_comb _ _ _ _ u T c₂ t₁ t₂ t₃ hB).trans ?_
  have hfin := final_arith (2 * Tc) c₂ |BM.Cst| r (Real.exp (r / 2)) (by positivity) hc₂ (abs_nonneg _) hr1 hexp
  have e2 : 2 * T = 2 * Tc * r ^ (4 * |BM.Cst|) * Real.exp (r / 2) := by rw [hT]; ring
  rw [e2]
  exact hfin

end GlobalTheory.CompanionTheory.Ar.PB.StepW.GradLoc
