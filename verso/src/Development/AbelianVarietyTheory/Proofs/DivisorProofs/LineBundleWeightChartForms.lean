import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVarietyPartitionDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFormTransitionCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFormChartTransitionStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens

open GlobalTheory.Cartier in

/- English proof (translation)
Establish `hC : ∀ x ∈ (Set.univ : Set (CxPts p σ)), CInfAt χ x` using `fun x _ => by`. Take `⟨l, hl⟩` from `A.cover x`. Establish `h` using `hχ l`. Rewrite `h`, `hl` using `[hA.chart_eq l]`. Conclude with `cInfAt_of_chart isOpen_univ _ ((AlgChart.contDiffOn_finChart_iff _ _ _ _).1 h) hl trivial`.

Establish `h` using `contDiffOn_chart hC c`. Establish `hn : c.e.target ∩ c.e.symm ⁻¹' Set.univ ∈ 𝓝 (c.e y)`. Rewrite using `[Set.preimage_univ, Set.inter_univ]`. Conclude with `c.e.open_target.mem_nhds (c.e.map_source hy)`. Conclude with `((h.contDiffAt hn).of_le (by norm_num))`.
-/
theorem contDiffAt_chart_of_atlas_smooth {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {A : ReciprocityTheory.AnForm.M.FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A)
    {χ : CxPts p σ → ℝ} (hχ : A.Smooth χ) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ContDiffAt ℝ 1 (fun v => χ (c.e.symm v)) (c.e y) := by
  have hC : ∀ x ∈ (Set.univ : Set (CxPts p σ)), CInfAt χ x := fun x _ => by
    obtain ⟨l, hl⟩ := A.cover x
    have h := hχ l
    rw [hA.chart_eq l] at h hl
    exact cInfAt_of_chart isOpen_univ _ ((AlgChart.contDiffOn_finChart_iff _ _ _ _).1 h) hl trivial
  have h := contDiffOn_chart hC c
  have hn : c.e.target ∩ c.e.symm ⁻¹' Set.univ ∈ 𝓝 (c.e y) := by
    rw [Set.preimage_univ, Set.inter_univ]; exact c.e.open_target.mem_nhds (c.e.map_source hy)
  exact ((h.contDiffAt hn).of_le (by norm_num))

open GlobalTheory.Cartier in

/- English proof (translation)
Introduce `k _ X p σ d _ _ _ hR B φ hφ m hm hglue`. Take `⟨R⟩` from `hR`. Use `set A := R.finAtlas`. Establish `hA : IsAlgAtlas A` using `R.isAlgAtlas_finAtlas`. Take `⟨P⟩` from `ReciprocityTheory.AnForm.M.existsPartition A`.

Use `set mi : Fin A.n → AlgChart p σ (d + 1) → CxPts p σ → Fin (d + 1) → ℂ := fun i c y j => (P.χ i y : ℂ) * m c y j with hmi`. Establish `hχ : ∀ i (c : AlgChart p σ (d + 1)), ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => ((P.χ i (c.e.symm v) : ℝ) : ℂ)) (c.e y)` using `fun i c y hy => Complex.ofRealCLM.contDiff.contDiffAt.comp _ (contDiffAt_chart_of_atlas_smooth hA (P.smooth i) c hy)`. Establish `hmi1 : ∀ i (c : AlgChart p σ (d + 1)), ∀ y ∈ c.e.source, ∀ j, ContDiffAt ℝ 1 (fun v => mi i c (c.e.symm v) j) (c.e y)` using `fun i c y hy j => (hχ i c y hy).mul (hm c y hy j)`. Establish `hmi2 : ∀ i (c c' : AlgChart p σ (d + 1)) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → ∀ j, mi i c y j = ∑ a, transMat c c' y a j * mi i c' y a` using `fun i c c' y hy hy' j => by`. Simplify using `only [hmi, hglue c c' y hy hy' j, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun a _ => by ring`. Use `set ρ : AlgChart p σ (d + 1) → CxPts p σ → ℝ := fun c y => mix d (chernMat φ c y) (Matrix.of fun j l => dbar (fun v => m c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1)) with hρ`. Use `set ρi : Fin A.n → AlgChart p σ (d + 1) → CxPts p σ → ℝ := fun i c y => mix d (chernMat φ c y) (Matrix.of fun j l => dbar (fun v => mi i c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1)) with hρi`. Establish `hzero : ∀ i, total (ρi i) = 0` using `fun i => by`. Take `⟨c₀, hc₀⟩` from `hA i`.

Use `GlobalTheory.T.weighted_form_chart_transition k X p σ d B φ hφ (mi i) (hmi1 i) (hmi2 i) c₀ (tsupport (P.χ i)) (isClosed_tsupport _).isCompact ?_ ?_` and prove the remaining obligations. Use `P.tsupport_subset i` as an intermediate fact. Rewrite `this` using `[hc₀, AlgChart.finChart_source]`. Then use the resulting hypothesis. Introduce `c y _ hy j`. Simplify using `[hmi, image_eq_zero_of_notMem_tsupport hy]`.

Establish `hsum : ∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, ρ c y = ∑ i, ρi i c y` using `fun c y hy => by`. Establish `e : ∀ j, (fun v => m c (c.e.symm v) j) = fun v => ∑ i, mi i c (c.e.symm v) j` using `fun j => funext fun v => by`. Simplify using `only [hmi, ← Finset.sum_mul, ← Complex.ofReal_sum, P.sum_eq_one, Complex.ofReal_one, one_mul]`. Simplify using `only [hρ, hρi]`. Rewrite using `[← mix_sum]`.

Use `congr 1`. Use extensionality with `j l`. Rewrite using `[Matrix.sum_apply, Matrix.of_apply, e j, dbar_sum fun i _ => ((hmi1 i c y hy j).differentiableAt one_ne_zero)]`. Simplify using the standard rewrite rules. Take `⟨ν, w, hfin, -, -, -, hdens, htot⟩` from `exists_refMeasure k X p σ (d + 1) ⟨R⟩`.

Establish `hd : ∀ i, IsDens (ρi i)` using `fun i => isDens_mix_dbar k X p σ d _ (mi i) (chernMat_isForm k X p σ (d + 1) B φ hφ) (hmi1 i) (hmi2 i)`. Use `choose g hgc hgw using fun i => hdens _ (hd i)`. Establish `hint : ∀ i, Integrable (g i) ν` using `fun i => (hgc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `h0 : ∀ i, ∫ y, g i y ∂ν = 0` using `fun i => by`. Rewrite using `[← (htot _ _ (hgc i) (hgw i)).2, hzero i]`.

Establish `hG : ∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, ρ c y = (∑ i, g i y) * w c y` using `fun c y hy => by`. Rewrite using `[hsum c y hy, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => hgw i c y hy`. Rewrite using `[(htot ρ _ (continuous_finsetSum _ fun i _ => hgc i) hG).2, integral_finsetSum _ fun i _ => hint i]`. Simplify using `[h0]`.
-/
theorem total_dbar_eq_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ (d + 1)) → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ (α : AlgChart p σ (d + 1) → CxPts p σ → Fin (d + 1) → ℂ), (∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, ∀ j, ContDiffAt ℝ 1 (fun v => α c (c.e.symm v) j) (c.e y)) → (∀ (c c' : AlgChart p σ (d + 1)) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source → ∀ j, α c y j = ∑ a, transMat c c' y a j * α c' y a) → total (fun (c : AlgChart p σ (d + 1)) y => mix d (chernMat φ c y) (Matrix.of fun j l => dbar (fun v => α c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1))) = 0 := by
  intro k _ X p σ d _ _ _ hR B φ hφ m hm hglue
  obtain ⟨R⟩ := hR
  set A := R.finAtlas
  have hA : IsAlgAtlas A := R.isAlgAtlas_finAtlas
  obtain ⟨P⟩ := ReciprocityTheory.AnForm.M.existsPartition A

  set mi : Fin A.n → AlgChart p σ (d + 1) → CxPts p σ → Fin (d + 1) → ℂ :=
    fun i c y j => (P.χ i y : ℂ) * m c y j with hmi
  have hχ : ∀ i (c : AlgChart p σ (d + 1)), ∀ y ∈ c.e.source,
      ContDiffAt ℝ 1 (fun v => ((P.χ i (c.e.symm v) : ℝ) : ℂ)) (c.e y) := fun i c y hy =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (contDiffAt_chart_of_atlas_smooth hA (P.smooth i) c hy)
  have hmi1 : ∀ i (c : AlgChart p σ (d + 1)), ∀ y ∈ c.e.source, ∀ j,
      ContDiffAt ℝ 1 (fun v => mi i c (c.e.symm v) j) (c.e y) := fun i c y hy j =>
    (hχ i c y hy).mul (hm c y hy j)
  have hmi2 : ∀ i (c c' : AlgChart p σ (d + 1)) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
      ∀ j, mi i c y j = ∑ a, transMat c c' y a j * mi i c' y a := fun i c c' y hy hy' j => by
    simp only [hmi, hglue c c' y hy hy' j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  set ρ : AlgChart p σ (d + 1) → CxPts p σ → ℝ := fun c y => mix d (chernMat φ c y)
    (Matrix.of fun j l => dbar (fun v => m c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1)) with hρ
  set ρi : Fin A.n → AlgChart p σ (d + 1) → CxPts p σ → ℝ := fun i c y => mix d (chernMat φ c y)
    (Matrix.of fun j l => dbar (fun v => mi i c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1)) with hρi

  have hzero : ∀ i, total (ρi i) = 0 := fun i => by
    obtain ⟨c₀, hc₀⟩ := hA i
    refine GlobalTheory.T.weighted_form_chart_transition k X p σ d B φ hφ (mi i) (hmi1 i) (hmi2 i) c₀ (tsupport (P.χ i))
      (isClosed_tsupport _).isCompact ?_ ?_
    · have := P.tsupport_subset i
      rwa [hc₀, AlgChart.finChart_source] at this
    · intro c y _ hy j
      simp [hmi, image_eq_zero_of_notMem_tsupport hy]

  have hsum : ∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, ρ c y = ∑ i, ρi i c y := fun c y hy => by
    have e : ∀ j, (fun v => m c (c.e.symm v) j) = fun v => ∑ i, mi i c (c.e.symm v) j := fun j => funext fun v => by
      simp only [hmi, ← Finset.sum_mul, ← Complex.ofReal_sum, P.sum_eq_one, Complex.ofReal_one, one_mul]
    simp only [hρ, hρi]
    rw [← mix_sum]
    congr 1
    ext j l
    rw [Matrix.sum_apply, Matrix.of_apply, e j,
      dbar_sum fun i _ => ((hmi1 i c y hy j).differentiableAt one_ne_zero)]
    simp

  obtain ⟨ν, w, hfin, -, -, -, hdens, htot⟩ := exists_refMeasure k X p σ (d + 1) ⟨R⟩
  have hd : ∀ i, IsDens (ρi i) := fun i =>
    isDens_mix_dbar k X p σ d _ (mi i) (chernMat_isForm k X p σ (d + 1) B φ hφ) (hmi1 i) (hmi2 i)
  choose g hgc hgw using fun i => hdens _ (hd i)
  have hint : ∀ i, Integrable (g i) ν := fun i =>
    (hgc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h0 : ∀ i, ∫ y, g i y ∂ν = 0 := fun i => by
    rw [← (htot _ _ (hgc i) (hgw i)).2, hzero i]
  have hG : ∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, ρ c y = (∑ i, g i y) * w c y := fun c y hy => by
    rw [hsum c y hy, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => hgw i c y hy
  rw [(htot ρ _ (continuous_finsetSum _ fun i _ => hgc i) hG).2, integral_finsetSum _ fun i _ => hint i]
  simp [h0]

end GlobalTheory.MixDens
