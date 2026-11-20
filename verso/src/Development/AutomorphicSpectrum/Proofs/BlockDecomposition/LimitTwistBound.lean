import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceEopEqOfHasInfCharGL

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.TotalTrace

/- English proof (translation)
Establish `h0 : HasDerivAt (fun v : ℝ => c * (v : ℂ)) c 0`. Simplify using `using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul c`. Establish `h1` using `h0.cexp`. Establish `h2 : (fun t : ℝ => Complex.exp (c * t)) = fun _ => 1` using `funext h`. Rewrite `h1` using `[h2]`.

Establish `h3` using `h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))`. Simplify using `using h3`.
-/
theorem eq_zero_of_exp_mul_eq_one {c : ℂ} (h : ∀ t : ℝ, Complex.exp (c * t) = 1) : c = 0 := by
  have h0 : HasDerivAt (fun v : ℝ => c * (v : ℂ)) c 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul c
  have h1 := h0.cexp
  have h2 : (fun t : ℝ => Complex.exp (c * t)) = fun _ => 1 := funext h
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using h3

/- English proof (translation)
Take `⟨φ, hφ, hφ0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hφ0 (Subtype.ext (funext hcon))`.

Establish `hlie : lie E N (oneL E N) φ = (∑ τ, (m τ).sum) • φ`. Rewrite using `[GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]`. Conclude with `Finset.sum_congr rfl fun τ _ => GlobalTheory.CompanionTheory.CentEig.trace_Eop_eq_of_hasInfCharGL (hm τ) φ hφ`. Use `eq_zero_of_exp_mul_eq_one fun t => ?_` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre E N φ _ hlie t g`.

Rewrite `h1` using `[(hV.sqInt φ hφ).1 t g]`. Establish `h2 : Complex.exp ((∑ τ, (m τ).sum) * t) * φ.1 g = 1 * φ.1 g` using `by rw [one_mul]; exact h1.symm`. Conclude with `mul_right_cancel₀ hg h2`.
-/
theorem total_trace_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} {m : (E →+* ℂ) → Multiset ℂ} (hV : IsDiscrete V)
    (hm : ∀ τ, HasInfCharGL V τ (m τ)) : ∑ τ, (m τ).sum = 0 := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hφ0 (Subtype.ext (funext hcon))
  have hlie : lie E N (oneL E N) φ = (∑ τ, (m τ).sum) • φ := by
    rw [GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
    exact Finset.sum_congr rfl fun τ _ => GlobalTheory.CompanionTheory.CentEig.trace_Eop_eq_of_hasInfCharGL (hm τ) φ hφ
  refine eq_zero_of_exp_mul_eq_one fun t => ?_
  have h1 := GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre E N φ _ hlie t g
  rw [(hV.sqInt φ hφ).1 t g] at h1
  have h2 : Complex.exp ((∑ τ, (m τ).sum) * t) * φ.1 g = 1 * φ.1 g := by rw [one_mul]; exact h1.symm
  exact mul_right_cancel₀ hg h2

/- English proof (translation)
Introduce `E _ _ _ N`. Use `⟨0, fun V m hV hm => ?_⟩` and prove the remaining obligations. Rewrite using `[total_trace_eq_zero hV hm, norm_zero]`.
-/
theorem twBound : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.TwBound := by
  intro E _ _ _ N
  refine ⟨0, fun V m hV hm => ?_⟩
  rw [total_trace_eq_zero hV hm, norm_zero]

end GlobalTheory.CompanionTheory.TotalTrace

end
