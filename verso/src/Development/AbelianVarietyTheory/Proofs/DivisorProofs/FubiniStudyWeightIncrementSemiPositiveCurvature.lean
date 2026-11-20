import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairNormIndependentOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionLocalFunctionContinuousOnHolomorphicChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionPropertiesStatement
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace GlobalTheory.HSAmp

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

/- English proof (translation)
Introduce `k _ X _ p D _ P e x hx n u hn hu σ i c y hy ξ`. Use `set j := pick (P.A.φ σ).isLB y`. Establish `hj : y ∈ ptsIn p σ (P.A.B.U j)` using `mem_pick (P.A.φ σ).isLB y`. Use `set O := ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j) with hOdef`. Establish `hO : IsOpen O` using `(isOpen_ptsIn _).inter (isOpen_ptsIn _)`.

Establish `he : (0 : ℝ) < e` using `by exact_mod_cast hx.pos`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hen : (0 : ℝ) < (e : ℝ) * n` using `mul_pos he hn'`. Establish `key : ∀ z ∈ O, 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) ∧ (P.L.φ σ).φ i z + u.u σ z = ((e : ℝ) * n)⁻¹ * Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n))`. Introduce `z hz`.

Establish `hnu : ∀ l, P.nu e 0 σ z (x l) ^ (2 * n) = Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z)`. Introduce `l`. Rewrite using `[GlobalTheory.VolBr.nu_eq k X p P e 0 (x l) (hx.mem l) σ z i j hz.1 hz.2, Complex.normSq_eq_norm_sq, norm_pow, mul_pow, ← pow_mul, ← Real.exp_nat_mul]`. Use `congr 2`. Put the polynomial expressions in normal form.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum : ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) = (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z)`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun l _ => hnu l`.

Establish `hpos : 0 < ∑ l, P.nu e 0 σ z (x l) ^ (2 * n)`. Take `⟨l, hl⟩` from `hx.cover (under z)`. Establish `h1` using `((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ z hl).2`. Conclude with `Finset.sum_pos' (fun l' _ => pow_nonneg (by unfold Pair.nu; positivity) _) ⟨l, Finset.mem_univ _, pow_pos h1 _⟩`. Establish `hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)`.

Rewrite `hpos` using `[hsum]`. Conclude with `pos_of_mul_pos_left hpos (Real.exp_pos _).le`. Use `⟨hS, ?_⟩` and prove the remaining obligations. Rewrite using `[hu σ z, hsum, Real.log_mul hS.ne' (Real.exp_pos _).ne', Real.log_exp]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hyO : y ∈ O` using `⟨hy.2, hj⟩`. Establish `hW : IsOpen (c.e.target ∩ c.e.symm ⁻¹' O)` using `GlobalTheory.ChartGlue.isOpen_over c.e hO`. Establish `hyW : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' O` using `GlobalTheory.ChartGlue.mem_over c.e hy.1 hyO`. Establish `hG : ∀ l, ContDiffAt ℂ 2 (fun v => ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n) (c.e y)` using `fun l => contDiffAt_two_of_holo hW (((GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P e 0 σ (x l) (hx.mem l) i j).2 D c).pow n) hyW`.

Establish `hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm (c.e y)) ^ n)` using `(key _ hyW.2).1`. Establish `hf : ContDiffAt ℝ 2 (fun v => Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n))) (c.e y)` using `(ContDiffAt.sum fun l _ => contDiffAt_normSq_comp (hG l)).log hS.ne'`. Establish `heq : (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)] fun v => ((((e : ℝ) * n)⁻¹ * Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)) + 0 : ℝ) : ℂ)` using `eventually_of_mem (hW.mem_nhds hyW) fun v hv => by dsimp only`. Rewrite using `[add_zero, ← (key _ hv.2).2]`. Both sides reduce to the same expression.

Express the relevant statement in the definitionally equal form `0 ≤ (leviV D (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) (c.e y) ξ).re`. Rewrite using `[leviV_congr heq, leviV_const_mul hf _ 0, Complex.re_ofReal_mul]`. Conclude with `mul_nonneg (inv_nonneg.2 hen.le) (leviV_log_sum_nonneg (fun l => contDiffAt_normSq_comp (hG l)) (fun l => logPshAt_normSq (hG l)) hS ξ)`.
-/
theorem semiPos_up_of_isCan : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x →
    ∀ (n : ℕ) (u : SmFn p), 1 ≤ n → IsCan P e n x u → (up P.L u).SemiPos D := by
  intro k _ X _ p D _ P e x hx n u hn hu σ i c y hy ξ
  set j := pick (P.A.φ σ).isLB y
  have hj : y ∈ ptsIn p σ (P.A.B.U j) := mem_pick (P.A.φ σ).isLB y
  set O := ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j) with hOdef
  have hO : IsOpen O := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have he : (0 : ℝ) < e := by exact_mod_cast hx.pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hen : (0 : ℝ) < (e : ℝ) * n := mul_pos he hn'

  have key : ∀ z ∈ O, 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) ∧
      (P.L.φ σ).φ i z + u.u σ z =
        ((e : ℝ) * n)⁻¹ * Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) := by
    intro z hz
    have hnu : ∀ l, P.nu e 0 σ z (x l) ^ (2 * n) =
        Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z) := by
      intro l
      rw [GlobalTheory.VolBr.nu_eq k X p P e 0 (x l) (hx.mem l) σ z i j hz.1 hz.2, Complex.normSq_eq_norm_sq, norm_pow,
        mul_pow, ← pow_mul, ← Real.exp_nat_mul]
      congr 2
      · ring_nf
      · push_cast; ring
    have hsum : ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) =
        (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n)) * Real.exp (-((e : ℝ) * n) * (P.L.φ σ).φ i z) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => hnu l
    have hpos : 0 < ∑ l, P.nu e 0 σ z (x l) ^ (2 * n) := by
      obtain ⟨l, hl⟩ := hx.cover (under z)
      have h1 := ((GlobalTheory.T.regularNonvanishingLocusSection_properties k X p P e 0 (x l) (hx.mem l)).2.2.2.2 (x l) (hx.mem l) σ z hl).2
      exact Finset.sum_pos' (fun l' _ => pow_nonneg (by unfold Pair.nu; positivity) _)
        ⟨l, Finset.mem_univ _, pow_pos h1 _⟩
    have hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) z ^ n) := by
      rw [hsum] at hpos
      exact pos_of_mul_pos_left hpos (Real.exp_pos _).le
    refine ⟨hS, ?_⟩
    rw [hu σ z, hsum, Real.log_mul hS.ne' (Real.exp_pos _).ne', Real.log_exp]
    field_simp
    ring
  have hyO : y ∈ O := ⟨hy.2, hj⟩
  have hW : IsOpen (c.e.target ∩ c.e.symm ⁻¹' O) := GlobalTheory.ChartGlue.isOpen_over c.e hO
  have hyW : c.e y ∈ c.e.target ∩ c.e.symm ⁻¹' O := GlobalTheory.ChartGlue.mem_over c.e hy.1 hyO
  have hG : ∀ l, ContDiffAt ℂ 2 (fun v => ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n) (c.e y) := fun l =>
    contDiffAt_two_of_holo hW (((GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P e 0 σ (x l) (hx.mem l) i j).2 D c).pow n) hyW
  have hS : 0 < ∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm (c.e y)) ^ n) :=
    (key _ hyW.2).1
  have hf : ContDiffAt ℝ 2 (fun v => Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)))
      (c.e y) :=
    (ContDiffAt.sum fun l _ => contDiffAt_normSq_comp (hG l)).log hS.ne'
  have heq : (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => ((((e : ℝ) * n)⁻¹ *
        Real.log (∑ l, Complex.normSq (ratVal (P.loc e 0 (x l) i j) (c.e.symm v) ^ n)) + 0 : ℝ) : ℂ) :=
    eventually_of_mem (hW.mem_nhds hyW) fun v hv => by
      dsimp only
      rw [add_zero, ← (key _ hv.2).2]
      rfl
  change 0 ≤ (leviV D (fun v => ((((P.L.φ σ).addFn (u.u σ)).φ i (c.e.symm v) : ℝ) : ℂ)) (c.e y) ξ).re
  rw [leviV_congr heq, leviV_const_mul hf _ 0, Complex.re_ofReal_mul]
  exact mul_nonneg (inv_nonneg.2 hen.le) (leviV_log_sum_nonneg (fun l => contDiffAt_normSq_comp (hG l))
    (fun l => logPshAt_normSq (hG l)) hS ξ)

end GlobalTheory.HSAmp
