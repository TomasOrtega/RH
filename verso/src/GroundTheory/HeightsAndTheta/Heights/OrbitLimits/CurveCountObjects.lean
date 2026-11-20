import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.NatCardEqPowLength
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsPointVertRSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def curveChartMono (c : ∀ k, ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

def chartUnit (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * a k)

def chartIndexLog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : ℝ :=
  Real.log (genIndex (chartLat y a τ) (curveMul y (chartUnit y c a τ)))

def chartRadius (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (t : (Σ k, ι k) → ℂ) : ℝ :=
  A.h t / ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k

end Objects

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in
open Classical in

/- English proof (translation)
Distinguish the cases in `h : k' = k`. Substitute `h` using the available equality. Simplify using `[Finsupp.single_apply]`. Rewrite using `[if_neg h]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `he`. Conclude with `h (Sigma.mk.inj_iff.mp he).1`.
-/
theorem sum_single_chart_apply (k' : K) (j : ι k') (b : ℕ) (k : K) :
    ∑ i, (Finsupp.single (⟨k', j⟩ : Σ k, ι k) b) ⟨k, i⟩ = if k' = k then b else 0 := by
  classical
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro he
    exact h (Sigma.mk.inj_iff.mp he).1

/- English proof (translation)
Establish `h : curveChartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)`. Rewrite using `[curveChartMono, monomial_sum_one]`. Conclude with `Finset.prod_congr rfl fun k _ => X_pow_eq_monomial`. Establish `hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d`. Use function extensionality and compare the values at `k`.

Simplify using `only [Finsupp.finsetSum_apply]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [sum_single_chart_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[h]`. Establish `hm` using `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial (ι := ι) (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)`.

Rewrite `hm` using `[hd]`. Conclude with `hm`.
-/
theorem isMultiHomog_curveChartMono (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (curveChartMono c d) d := by
  classical
  have h : curveChartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
    rw [curveChartMono, monomial_sum_one]
    exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
  have hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d := by
    funext k
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_chart_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  have hm := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial (ι := ι)
    (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)
  rw [hd] at hm
  exact hm

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Simplify using `[curveChartMono, chartUnit, map_prod]`.
-/
theorem aeval_curveChartMono (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (curveChartMono c d) = chartUnit y c (fun k => (d k : ℤ)) 1 := by
  simp [curveChartMono, chartUnit, map_prod]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `h0`. Apply `hp` to reduce the goal to its premises. Use `show X p ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]`.
-/
theorem ne_zero_of_X_notMem {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply hp
  show X p ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `h`. Establish `h' : mConeMap y (curveChartMono c d) = 0` using `h`. Rewrite `h'` using `[curveChartMono, map_prod]`. Take `⟨k, -, hk⟩` from `Finset.prod_eq_zero_iff.mp h'`. Rewrite `hk` using `[map_pow, mConeMap, aeval_X]`.

Conclude with `mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _) (pow_eq_zero_iff'.mp hk).1`.
-/
theorem curveChartMono_notMem {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    curveChartMono c d ∉ mCoordIdeal y := by
  intro h
  have h' : mConeMap y (curveChartMono c d) = 0 := h
  rw [curveChartMono, map_prod] at h'
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h'
  rw [map_pow, mConeMap, aeval_X] at hk
  exact mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _) (pow_eq_zero_iff'.mp hk).1

/- English proof (translation)
Use `choose c hc using hP.2.1.2.2`. Conclude with `⟨c, hc, fun k => ne_zero_of_X_notMem (hc k)⟩`.
-/
theorem exists_chart {y : (Σ k, ι k) → Ω} {n : ℕ} (hP : IsArithVar (mCoordIdeal y) n) :
    ∃ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal y) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hP.2.1.2.2
  exact ⟨c, hc, fun k => ne_zero_of_X_notMem (hc k)⟩

end Lemmas

section Examples

/- English proof (translation)
Simplify using `[chartUnit]`.
-/
example (a : Unit → ℤ) (τ : ℕ) :
    chartUnit (fun _ : (Σ _ : Unit, Fin 1) => (1 : ℚ)) (fun _ => 0) a τ = 1 := by
  simp [chartUnit]

/- English proof (translation)
Simplify using `[chartRadius, ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight]`.
-/
example : chartRadius (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine (ι := fun _ : Unit => Fin 1) (-1)) (fun _ => 0)
    (fun _ => 1) = Real.exp 1 := by
  simp [chartRadius, ReciprocityTheory.ChartRestriction.G.AI.I2.constLine, HermLine.ofWeight]

/- English proof (translation)
Simplify using `[curveChartMono, X_ne_zero]`.
-/
example : curveChartMono (ι := fun _ : Unit => Fin 1) (fun _ => 0) (fun _ => 2) ≠ 0 := by
  simp [curveChartMono, X_ne_zero]

end Examples

end

end GroundTheory.Heights₂.Heights.Targets
