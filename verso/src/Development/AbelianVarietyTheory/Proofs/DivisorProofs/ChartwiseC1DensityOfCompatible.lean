import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDensityOfTransitionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMeasureDensityExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityGlueingUnderTransitionStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveStokes

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

/- English proof (translation)
Establish `hC : ∀ x ∈ (Set.univ : Set (CxPts p σ)), CInfAt χ x` using `fun x _ => by`. Take `⟨l, hl⟩` from `A.cover x`. Establish `h` using `hχ l`. Rewrite `h`, `hl` using `[hA.chart_eq l]`. Conclude with `cInfAt_of_chart isOpen_univ _ ((AlgChart.contDiffOn_finChart_iff _ _ _ _).1 h) hl trivial`.

Establish `h` using `contDiffOn_chart hC c`. Establish `hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' Set.univ` using `⟨c.e.map_source hy, trivial⟩`. Establish `hn : c.e.target ∩ c.e.symm ⁻¹' Set.univ ∈ 𝓝 (c.e y)`. Rewrite using `[Set.preimage_univ, Set.inter_univ]`. Conclude with `c.e.open_target.mem_nhds (c.e.map_source hy)`.

Conclude with `((h.contDiffAt hn).of_le (by norm_num))`.
-/
theorem contDiffAt_chart_of_smooth {A : ReciprocityTheory.AnForm.M.FinHolAtlas 1 (CxPts p σ)} (hA : IsAlgAtlas A)
    {χ : CxPts p σ → ℝ} (hχ : A.Smooth χ) (c : AlgChart p σ 1) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ContDiffAt ℝ 1 (fun v => χ (c.e.symm v)) (c.e y) := by
  have hC : ∀ x ∈ (Set.univ : Set (CxPts p σ)), CInfAt χ x := fun x _ => by
    obtain ⟨l, hl⟩ := A.cover x
    have h := hχ l
    rw [hA.chart_eq l] at h hl
    exact cInfAt_of_chart isOpen_univ _ ((AlgChart.contDiffOn_finChart_iff _ _ _ _).1 h) hl trivial
  have h := contDiffOn_chart hC c
  have hm : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' Set.univ := ⟨c.e.map_source hy, trivial⟩
  have hn : c.e.target ∩ c.e.symm ⁻¹' Set.univ ∈ 𝓝 (c.e y) := by
    rw [Set.preimage_univ, Set.inter_univ]; exact c.e.open_target.mem_nhds (c.e.map_source hy)
  exact ((h.contDiffAt hn).of_le (by norm_num))

end GlobalTheory.CurveStokes

namespace GlobalTheory

open GlobalTheory.CurveStokes in

/- English proof (translation)
Introduce `k _ X p σ _ _ _ hR m hm hglue`. Take `⟨R⟩` from `hR`. Use `set A := R.finAtlas`. Establish `hA : IsAlgAtlas A` using `R.isAlgAtlas_finAtlas`. Take `⟨P⟩` from `ReciprocityTheory.AnForm.M.existsPartition A`.

Use `set mj : Fin A.n → AlgChart p σ 1 → CxPts p σ → ℂ := fun j c y => (P.χ j y : ℂ) * m c y with hmj`. Establish `hχ : ∀ j (c : AlgChart p σ 1), ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => ((P.χ j (c.e.symm v) : ℝ) : ℂ)) (c.e y)` using `fun j c y hy => Complex.ofRealCLM.contDiff.contDiffAt.comp _ (contDiffAt_chart_of_smooth hA (P.smooth j) c hy)`. Establish `hmj1 : ∀ j (c : AlgChart p σ 1), ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => mj j c (c.e.symm v)) (c.e y)` using `fun j c y hy => (hχ j c y hy).mul (hm c y hy)`. Establish `hmj2 : ∀ j (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → mj j c y = ChartGlue.transDet c.e c'.e y * mj j c' y` using `fun j c c' y hy hy' => by`. Simplify using `only [hmj, hglue c c' y hy hy']`.

Expand and normalize the polynomial expressions, which then agree. Use `set ρ : AlgChart p σ 1 → CxPts p σ → ℝ := fun c y => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρ`. Use `set ρj : Fin A.n → AlgChart p σ 1 → CxPts p σ → ℝ := fun j c y => (dbar (fun v => mj j c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρj`. Establish `hzero : ∀ j, total (ρj j) = 0` using `fun j => by`. Take `⟨c₀, hc₀⟩` from `hA j`.

Use `GlobalTheory.T.total_re_dbar_eq_zero_of_compact_support_in_chart k X p σ (mj j) (hmj1 j) (hmj2 j) c₀ (tsupport (P.χ j)) (isClosed_tsupport _).isCompact ?_ ?_` and prove the remaining obligations. Use `P.tsupport_subset j` as an intermediate fact. Rewrite `this` using `[hc₀, AlgChart.finChart_source]`. Then use the resulting hypothesis. Introduce `c y _ hy`. Simplify using `[hmj, image_eq_zero_of_notMem_tsupport hy]`.

Establish `hsum : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = ∑ j, ρj j c y` using `fun c y hy => by`. Establish `e : (fun v => m c (c.e.symm v)) = fun v => ∑ j, mj j c (c.e.symm v)` using `funext fun v => by`. Simplify using `only [hmj, ← Finset.sum_mul, ← Complex.ofReal_sum, P.sum_eq_one, Complex.ofReal_one, one_mul]`. Simplify using `only [hρ, hρj, e]`. Rewrite using `[dbar_sum fun j _ => ((hmj1 j c y hy).differentiableAt one_ne_zero)]`.

Simplify using `[Complex.re_sum]`. Take `⟨ν, w, hfin, -, hdens, htot⟩` from `GlobalTheory.T.finite_measure_density_exists k X p σ ⟨R⟩`. Establish `hd : ∀ j, IsDens (ρj j)` using `fun j => GlobalTheory.T.dbar_density_of_transition k X p σ (mj j) (hmj1 j) (hmj2 j)`. Use `choose g hgc hgw using fun j => hdens _ (hd j)`. Establish `hint : ∀ j, Integrable (g j) ν` using `fun j => (hgc j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.

Establish `h0 : ∀ j, ∫ y, g j y ∂ν = 0` using `fun j => by`. Rewrite using `[← (htot _ _ (hgc j) (hgw j)).2, hzero j]`. Establish `hG : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = (∑ j, g j y) * w c y` using `fun c y hy => by`. Rewrite using `[hsum c y hy, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => hgw j c y hy`.

Rewrite using `[(htot ρ _ (continuous_finsetSum _ fun j _ => hgc j) hG).2, integral_finsetSum _ fun j _ => hint j]`. Simplify using `[h0]`.
-/
theorem stokes_curve : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (m : AlgChart p σ 1 → CxPts p σ → ℂ), (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) → (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → m c y = ChartGlue.transDet c.e c'.e y * m c' y) → total (fun (c : AlgChart p σ 1) (y : CxPts p σ) => (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) = 0 := by
  intro k _ X p σ _ _ _ hR m hm hglue
  obtain ⟨R⟩ := hR
  set A := R.finAtlas
  have hA : IsAlgAtlas A := R.isAlgAtlas_finAtlas
  obtain ⟨P⟩ := ReciprocityTheory.AnForm.M.existsPartition A

  set mj : Fin A.n → AlgChart p σ 1 → CxPts p σ → ℂ := fun j c y => (P.χ j y : ℂ) * m c y with hmj
  have hχ : ∀ j (c : AlgChart p σ 1), ∀ y ∈ c.e.source,
      ContDiffAt ℝ 1 (fun v => ((P.χ j (c.e.symm v) : ℝ) : ℂ)) (c.e y) := fun j c y hy =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (contDiffAt_chart_of_smooth hA (P.smooth j) c hy)
  have hmj1 : ∀ j (c : AlgChart p σ 1), ∀ y ∈ c.e.source,
      ContDiffAt ℝ 1 (fun v => mj j c (c.e.symm v)) (c.e y) := fun j c y hy =>
    (hχ j c y hy).mul (hm c y hy)
  have hmj2 : ∀ j (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
      mj j c y = ChartGlue.transDet c.e c'.e y * mj j c' y := fun j c c' y hy hy' => by
    simp only [hmj, hglue c c' y hy hy']; ring
  set ρ : AlgChart p σ 1 → CxPts p σ → ℝ := fun c y =>
    (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρ
  set ρj : Fin A.n → AlgChart p σ 1 → CxPts p σ → ℝ := fun j c y =>
    (dbar (fun v => mj j c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re with hρj

  have hzero : ∀ j, total (ρj j) = 0 := fun j => by
    obtain ⟨c₀, hc₀⟩ := hA j
    refine GlobalTheory.T.total_re_dbar_eq_zero_of_compact_support_in_chart k X p σ (mj j) (hmj1 j) (hmj2 j) c₀ (tsupport (P.χ j))
      (isClosed_tsupport _).isCompact ?_ ?_
    · have := P.tsupport_subset j
      rwa [hc₀, AlgChart.finChart_source] at this
    · intro c y _ hy
      simp [hmj, image_eq_zero_of_notMem_tsupport hy]

  have hsum : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = ∑ j, ρj j c y := fun c y hy => by
    have e : (fun v => m c (c.e.symm v)) = fun v => ∑ j, mj j c (c.e.symm v) := funext fun v => by
      simp only [hmj, ← Finset.sum_mul, ← Complex.ofReal_sum, P.sum_eq_one, Complex.ofReal_one, one_mul]
    simp only [hρ, hρj, e]
    rw [dbar_sum fun j _ => ((hmj1 j c y hy).differentiableAt one_ne_zero)]
    simp [Complex.re_sum]

  obtain ⟨ν, w, hfin, -, hdens, htot⟩ := GlobalTheory.T.finite_measure_density_exists k X p σ ⟨R⟩
  have hd : ∀ j, IsDens (ρj j) := fun j => GlobalTheory.T.dbar_density_of_transition k X p σ (mj j) (hmj1 j) (hmj2 j)
  choose g hgc hgw using fun j => hdens _ (hd j)
  have hint : ∀ j, Integrable (g j) ν := fun j =>
    (hgc j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : ∀ j, ∫ y, g j y ∂ν = 0 := fun j => by
    rw [← (htot _ _ (hgc j) (hgw j)).2, hzero j]
  have hG : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = (∑ j, g j y) * w c y := fun c y hy => by
    rw [hsum c y hy, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => hgw j c y hy
  rw [(htot ρ _ (continuous_finsetSum _ fun j _ => hgc j) hG).2, integral_finsetSum _ fun j _ => hint j]
  simp [h0]

end GlobalTheory
