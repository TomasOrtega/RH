import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourIndep
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourBasic

namespace ReciprocityTheory.ChartRestriction.G.FD.TubeSummability

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexConjugate

/- English proof (translation)
Establish `hgeo : Summable (fun m : ℕ => Real.exp (-c) ^ m)` using `summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using Real.exp_lt_exp.2 (by linarith : -c < 0))`. Establish `h1 : Summable (fun m : ℤ => Real.exp (-c * |(m : ℝ)|))`. Apply `Summable.of_nat_of_neg` to reduce the goal to its premises. Use `hgeo.congr fun m => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, Int.cast_natCast, Nat.abs_cast]`.

Rewrite using `[← Real.exp_nat_mul]`. Put the polynomial expressions in normal form. Use `hgeo.congr fun m => ?_` and prove the remaining obligations. Simplify using `only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]`. Rewrite using `[← Real.exp_nat_mul]`.

Put the polynomial expressions in normal form. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact Summable.of_finite`. Consider the case `succ n ih`.

Rewrite using `[← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]`. Use `h1.mul_of_nonneg ih (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `[Fin.consEquiv, Fin.sum_univ_succ, mul_add, Real.exp_add]`.
-/
lemma summable_exp_abs (c : ℝ) (hc : 0 < c) :
    ∀ n : ℕ, Summable (fun k : Fin n → ℤ => Real.exp (-c * ∑ j, |(k j : ℝ)|)) := by
  have hgeo : Summable (fun m : ℕ => Real.exp (-c) ^ m) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (by simpa using Real.exp_lt_exp.2 (by linarith : -c < 0))
  have h1 : Summable (fun m : ℤ => Real.exp (-c * |(m : ℝ)|)) := by
    apply Summable.of_nat_of_neg
    · refine hgeo.congr fun m => ?_
      simp only [Function.comp, Int.cast_natCast, Nat.abs_cast]
      rw [← Real.exp_nat_mul]
      ring_nf
    · refine hgeo.congr fun m => ?_
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
      rw [← Real.exp_nat_mul]
      ring_nf
  intro n
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).summable_iff]
    convert h1.mul_of_nonneg ih (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) using 1
    funext p
    simp [Fin.consEquiv, Fin.sum_univ_succ, mul_add, Real.exp_add]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section line

variable (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r)
  {n : ℕ} (ω : Fin n → X.Ψ → ℝ)

def Lc (t : Fin n → ℂ) : X.Ψ → ℂ := fun τ => ∑ j, t j * (ω j τ : ℂ)

noncomputable def hline (t : Fin n → ℂ) : ℂ := P (X.flow ξ (Lc X ω t) x)

def Om : Set (Fin n → ℝ) := (Fintype.linearCombination ℝ ω) ⁻¹' admissibleImaginary X ξ x

/- English proof (translation)
Simplify using `[Fintype.linearCombination_apply, Finset.sum_apply]`.
-/
lemma lincomb_apply (y : Fin n → ℝ) (τ : X.Ψ) :
    Fintype.linearCombination ℝ ω y τ = ∑ j, y j * ω j τ := by
  simp [Fintype.linearCombination_apply, Finset.sum_apply]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Rewrite using `[lincomb_apply]`. Simplify using `[Lc, Complex.im_sum]`.
-/
lemma Lc_im (t : Fin n → ℂ) :
    (fun τ => (Lc X ω t τ).im) = Fintype.linearCombination ℝ ω (fun j => (t j).im) := by
  funext τ
  rw [lincomb_apply]
  simp [Lc, Complex.im_sum]

variable {X ξ x}

/- English proof (translation)
Rewrite using `[flow_mem_dom_iff (X := X) hξ x hx, Lc_im]`. Both sides reduce to the same expression.
-/
lemma flow_Lc_mem_dom (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) (t : Fin n → ℂ) :
    X.flow ξ (Lc X ω t) x ∈ X.dom ↔ t ∈ tube n (Om X ξ x ω) := by
  rw [flow_mem_dom_iff (X := X) hξ x hx, Lc_im]
  rfl

/- English proof (translation)
Establish `hc : Continuous (Fintype.linearCombination ℝ ω)` using `LinearMap.continuous_of_finiteDimensional _`. Take `⟨ho, hcv⟩` from `admissibleImaginary_open_convex (X := X) (ξ := ξ) x hx`. Conclude with `⟨ho.preimage hc, hcv.linear_preimage _⟩`.
-/
lemma Om_open_convex (hx : x ∈ X.dom) : IsOpen (Om X ξ x ω) ∧ Convex ℝ (Om X ξ x ω) := by
  have hc : Continuous (Fintype.linearCombination ℝ ω) := LinearMap.continuous_of_finiteDimensional _
  obtain ⟨ho, hcv⟩ := admissibleImaginary_open_convex (X := X) (ξ := ξ) x hx
  exact ⟨ho.preimage hc, hcv.linear_preimage _⟩

/- English proof (translation)
Establish `h0` using `(flow_mem_dom_iff (X := X) hξ x hx 0).1 (by rw [flow_zero]; exact hx)`. Use `show Fintype.linearCombination ℝ ω 0 ∈ admissibleImaginary X ξ x`. Rewrite using `[map_zero]`. Simplify using `only [Pi.zero_apply, Complex.zero_im] at h0`. Conclude with `h0`.
-/
lemma zero_mem_Om (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) : (0 : Fin n → ℝ) ∈ Om X ξ x ω := by
  have h0 := (flow_mem_dom_iff (X := X) hξ x hx 0).1 (by rw [flow_zero]; exact hx)
  show Fintype.linearCombination ℝ ω 0 ∈ admissibleImaginary X ξ x
  rw [map_zero]
  simp only [Pi.zero_apply, Complex.zero_im] at h0
  exact h0

variable (X ξ x)

/- English proof (translation)
Introduce `t ht`. Establish `hmem : X.flow ξ (Lc X ω t) x ∈ X.dom` using `(flow_Lc_mem_dom ω hξ hx t).2 ht`. Establish `hLc : Differentiable ℂ (fun t : Fin n → ℂ => Lc X ω t)` using `differentiable_pi.2 fun τ => Differentiable.fun_sum fun j _ => (differentiable_apply j).mul_const _`. Establish `hd1 : DifferentiableAt ℂ (fun t => X.flow ξ (Lc X ω t) x) t` using `(flow_differentiable X ξ x).differentiableAt.comp t (hLc t)`. Conclude with `(hP.1 _ hmem).comp t hd1.differentiableWithinAt (fun t' ht' => (flow_Lc_mem_dom ω hξ hx t').2 ht')`.
-/
lemma hline_diff (hP : X.IsSec la P) (hξ : herm X.Gm ξ ξ = 0) (hx : x ∈ X.dom) :
    DifferentiableOn ℂ (hline X P ξ x ω) (tube n (Om X ξ x ω)) := by
  intro t ht
  have hmem : X.flow ξ (Lc X ω t) x ∈ X.dom := (flow_Lc_mem_dom ω hξ hx t).2 ht
  have hLc : Differentiable ℂ (fun t : Fin n → ℂ => Lc X ω t) :=
    differentiable_pi.2 fun τ => Differentiable.fun_sum fun j _ =>
      (differentiable_apply j).mul_const _
  have hd1 : DifferentiableAt ℂ (fun t => X.flow ξ (Lc X ω t) x) t :=
    (flow_differentiable X ξ x).differentiableAt.comp t (hLc t)
  exact (hP.1 _ hmem).comp t hd1.differentiableWithinAt
    (fun t' ht' => (flow_Lc_mem_dom ω hξ hx t').2 ht')

/- English proof (translation)
Introduce `t ht m`. Establish `hmem : X.flow ξ (Lc X ω t) x ∈ X.dom` using `(flow_Lc_mem_dom ω hξ hx t).2 ht`. Establish `hp : (∑ j, (m j : ℝ) • ω j) ∈ X.periods la` using `sum_mem fun j _ => by`. Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `zsmul_mem (hωp j) _`.

Establish `hLc : Lc X ω (t + fun j => (m j : ℂ)) = cR X (∑ j, (m j : ℝ) • ω j) + Lc X ω t`. Use function extensionality and compare the values at `τ`. Simplify using `[Lc, cR, add_mul, Finset.sum_add_distrib, Finset.sum_apply, add_comm]`. Simplify using `only [hline]`. Rewrite using `[hLc, ← flow_flow X hξ]`.

Conclude with `sec_periodic X la P hP hξΛ hξ hp _ hmem`.
-/
lemma hline_periodic (hP : X.IsSec la P) (hξΛ : ξ ∈ X.Λ) (hξ : herm X.Gm ξ ξ = 0)
    (hx : x ∈ X.dom) (hωp : ∀ j, ω j ∈ X.periods la) :
    ∀ t ∈ tube n (Om X ξ x ω), ∀ m : Fin n → ℤ,
      hline X P ξ x ω (t + fun j => (m j : ℂ)) = hline X P ξ x ω t := by
  intro t ht m
  have hmem : X.flow ξ (Lc X ω t) x ∈ X.dom := (flow_Lc_mem_dom ω hξ hx t).2 ht
  have hp : (∑ j, (m j : ℝ) • ω j) ∈ X.periods la :=
    sum_mem fun j _ => by
      rw [Int.cast_smul_eq_zsmul]
      exact zsmul_mem (hωp j) _
  have hLc : Lc X ω (t + fun j => (m j : ℂ)) = cR X (∑ j, (m j : ℝ) • ω j) + Lc X ω t := by
    funext τ
    simp [Lc, cR, add_mul, Finset.sum_add_distrib, Finset.sum_apply, add_comm]
  simp only [hline]
  rw [hLc, ← flow_flow X hξ]
  exact sec_periodic X la P hP hξΛ hξ hp _ hmem

end line

end ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
