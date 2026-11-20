import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow

namespace ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `r X u hu huΛ la P hP hchi ν`. Establish `hiso : X.IsIso (u 0)` using `⟨huΛ 0, hu.1 0 0, hu.2.ne_zero 0⟩`. Use `⟨CuspCoefficientFlow.fj_diffOn X.toData la P hP.1 hiso ν, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx b hb`. Establish `hfl : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b) = rmul (X.flow (u 0) (fun τ => (s τ : ℂ)) x) b` using `fun s => by`.

Use function extensionality and compare the values at `τ`. Use `show X.flowMat (u 0) τ (s τ : ℂ) * (mat x τ * mat b τ) = (X.flowMat (u 0) τ (s τ : ℂ) * mat x τ) * mat b τ`. Rewrite using `[Matrix.mul_assoc]`. Establish `hPb : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b)) = bchar la b * P (X.flow (u 0) (fun τ => (s τ : ℂ)) x)` using `fun s => by`. Rewrite using `[hfl]`.

Conclude with `hP.1.1.2.1 _ (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1 b hb`. Unfold `Data.fj`. Use `split_ifs with h1 h2`. Repeatedly rewrite using `[hPb, mul_assoc]`. Rewrite using `[integral_const_mul]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Introduce `b hb x hx`. Set `a0 : X.Ψ → Fin 2 → ℂ` to `fun _ => ![1, 0]`.

Establish `hemb : X.embV (u 0) = X.uvec u a0`. Use function extensionality and compare the values at `τ`. Simplify using `[Data.uvec, a0, Fin.sum_univ_two, Data.embV]`. Establish `hfl : ∀ (s : X.Ψ → ℝ) y, X.flow (u 0) (fun τ => (s τ : ℂ)) y = X.Zb u (fun τ i k => (s τ : ℂ) * a0 τ i * conj (a0 τ k)) y` using `fun s y => by`. Rewrite using `[show X.flow (u 0) (fun τ => (s τ : ℂ)) y = X.flowV (X.embV (u 0)) (fun τ => (s τ : ℂ)) y from rfl, hemb, Data.flowV_uvec]`.

Establish `hZ : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x) = X.Zb u b (X.flow (u 0) (fun τ => (s τ : ℂ)) x)` using `fun s => by`. Rewrite using `[hfl, hfl, Data.Zb_Zb X.toData u hu.1, Data.Zb_Zb X.toData u hu.1, add_comm]`. Establish `hPZ : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x)) = P (X.flow (u 0) (fun τ => (s τ : ℂ)) x)` using `fun s => by`. Rewrite using `[hZ]`. Conclude with `(hL2 r X u hu huΛ).2.1 la P hP.1.1 hchi b hb _ (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1`.

Unfold `Data.fj`. Repeatedly rewrite using `[hPZ]`.
-/
theorem cusp_coefficient_bound_of_unipotent_lattice_lift (hL2 : UnipotentLatticeLift (E := E)) : CuspCoefficientBound (E := E) := by
  intro r X u hu huΛ la P hP hchi ν
  have hiso : X.IsIso (u 0) := ⟨huΛ 0, hu.1 0 0, hu.2.ne_zero 0⟩
  refine ⟨CuspCoefficientFlow.fj_diffOn X.toData la P hP.1 hiso ν, ?_, ?_⟩
  · intro x hx b hb
    have hfl : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b) =
        rmul (X.flow (u 0) (fun τ => (s τ : ℂ)) x) b := fun s => by
      funext τ
      show X.flowMat (u 0) τ (s τ : ℂ) * (mat x τ * mat b τ) =
        (X.flowMat (u 0) τ (s τ : ℂ) * mat x τ) * mat b τ
      rw [Matrix.mul_assoc]
    have hPb : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (rmul x b)) =
        bchar la b * P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl]
      exact hP.1.1.2.1 _ (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1 b hb
    unfold Data.fj
    split_ifs with h1 h2
    · simp_rw [hPb, mul_assoc]
      rw [integral_const_mul]
      ring
    · simp
    · simp
  · intro b hb x hx
    let a0 : X.Ψ → Fin 2 → ℂ := fun _ => ![1, 0]
    have hemb : X.embV (u 0) = X.uvec u a0 := by
      funext τ
      simp [Data.uvec, a0, Fin.sum_univ_two, Data.embV]
    have hfl : ∀ (s : X.Ψ → ℝ) y, X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.Zb u (fun τ i k => (s τ : ℂ) * a0 τ i * conj (a0 τ k)) y := fun s y => by
      rw [show X.flow (u 0) (fun τ => (s τ : ℂ)) y =
        X.flowV (X.embV (u 0)) (fun τ => (s τ : ℂ)) y from rfl, hemb, Data.flowV_uvec]
    have hZ : ∀ s : X.Ψ → ℝ, X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x) =
        X.Zb u b (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hfl, hfl, Data.Zb_Zb X.toData u hu.1, Data.Zb_Zb X.toData u hu.1, add_comm]
    have hPZ : ∀ s : X.Ψ → ℝ, P (X.flow (u 0) (fun τ => (s τ : ℂ)) (X.Zb u b x)) =
        P (X.flow (u 0) (fun τ => (s τ : ℂ)) x) := fun s => by
      rw [hZ]
      exact (hL2 r X u hu huΛ).2.1 la P hP.1.1 hchi b hb _
        (FlowCoefficientBounds.flow_real X.toData hiso hx s la).1
    unfold Data.fj
    simp_rw [hPZ]

end ReciprocityTheory.ChartRestriction.G.FD.CuspCoefficientQuantitative
