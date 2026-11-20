import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

/- English proof (translation)
Establish `hp' : AnalyticOnNhd ℂ p Set.univ` using `fun z _ => hp.analyticAt z`. Establish `hq' : AnalyticOnNhd ℂ q Set.univ` using `fun z _ => hq.analyticAt z`. Use `AnalyticOnNhd.eq_of_frequently_eq (z₀ := ((0 : ℝ) : ℂ)) hp' hq' ?_` and prove the remaining obligations. Establish `ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin ((0 : ℝ) : ℂ) {((0 : ℝ) : ℂ)}ᶜ)`. Use `tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `(Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with y hy`. Introduce `h0`. Conclude with `hy (Complex.ofReal_injective h0)`. Conclude with `ht.frequently (Filter.Frequently.of_forall h)`.
-/
theorem entire_eq_of_eq_on_reals {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (p q : ℂ → E) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (h : ∀ y : ℝ, p y = q y) : p = q := by
  have hp' : AnalyticOnNhd ℂ p Set.univ := fun z _ => hp.analyticAt z
  have hq' : AnalyticOnNhd ℂ q Set.univ := fun z _ => hq.analyticAt z
  refine AnalyticOnNhd.eq_of_frequently_eq (z₀ := ((0 : ℝ) : ℂ)) hp' hq' ?_
  have ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (nhdsWithin 0 {0}ᶜ)
      (nhdsWithin ((0 : ℝ) : ℂ) {((0 : ℝ) : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      intro h0
      exact hy (Complex.ofReal_injective h0)
  exact ht.frequently (Filter.Frequently.of_forall h)

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ lam f hf hR Y g hg`. Establish `: CompleteSpace Wp` using `FiniteDimensional.complete ℂ Wp`. Establish `hs : Q.SmoothLev k r 0 Set.univ f`. Introduce `g₀ hg₀`. Take `⟨U, f', hU, hgU, hf', hff⟩` from `hf g₀ hg₀.1.1`.

Conclude with `⟨U, f', hU, hgU, hf', fun g hg hgl => hff g hg hgl.1⟩`. Establish `hg0 : g ∈ Q.Glev k r 0` using `⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩`. Establish `h0 : Formalism.QuantumDeterminants.inWb k r 0`. Unfold `Formalism.QuantumDeterminants.inWb`. Simplify using the standard rewrite rules.

Take `⟨A, hA⟩` from `Formalism.FourierDecayAlt.P.leading_term_alt (Wq →L[ℂ] Wp) k r 0 0 0 h0 h0`. Establish `hpoly : (fun Y : ℂ => Q.CV k r Y f g) = fun Y : ℂ => Y ^ Q.mdim k r 0 • f g + ∑ j ∈ Finset.range (Q.mdim k r 0), Y ^ j • A 0 0 j f g`. Use function extensionality and compare the values at `Y`. Conclude with `(hA Set.univ f isOpen_univ hs g ⟨hg0, trivial⟩ Y).1`. Establish `key` using `entire_eq_of_eq_on_reals (fun Y : ℂ => Q.CV k r Y f g) (fun Y : ℂ => (∏ s, (Y + (lam s : ℂ))) • f g) (by rw [hpoly]; fun_prop) (by`.

Use `Differentiable.smul_const ?_ _` and prove the remaining obligations. Conclude with `Differentiable.fun_finsetProd fun s _ => by fun_prop)`. Use the proof step `(fun y => by show Q.CV k r (y : ℂ) f g = _`. Rewrite using `[hR y g hg]`. Use `push_cast`.

Use the proof step `rfl)`. Conclude with `congrFun key Y`.
-/
theorem capelli_eigen_real_to_complex :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) f → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∀ Y : ℂ, ∀ g ∈ B.GV k r, Q.CV k r Y f g = (∏ s, (Y + (lam s : ℂ))) • f g := by
  intro k r Wp Wq _ _ _ _ _ _ lam f hf hR Y g hg
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hs : Q.SmoothLev k r 0 Set.univ f := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀.1.1
    exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hff g hg hgl.1⟩
  have hg0 : g ∈ Q.Glev k r 0 := ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  have h0 : Formalism.QuantumDeterminants.inWb k r 0 := by
    unfold Formalism.QuantumDeterminants.inWb
    simp
  obtain ⟨A, hA⟩ := Formalism.FourierDecayAlt.P.leading_term_alt (Wq →L[ℂ] Wp) k r 0 0 0 h0 h0
  have hpoly : (fun Y : ℂ => Q.CV k r Y f g) = fun Y : ℂ => Y ^ Q.mdim k r 0 • f g +
      ∑ j ∈ Finset.range (Q.mdim k r 0), Y ^ j • A 0 0 j f g := by
    funext Y
    exact (hA Set.univ f isOpen_univ hs g ⟨hg0, trivial⟩ Y).1
  have key := entire_eq_of_eq_on_reals (fun Y : ℂ => Q.CV k r Y f g)
    (fun Y : ℂ => (∏ s, (Y + (lam s : ℂ))) • f g) (by rw [hpoly]; fun_prop)
    (by
      refine Differentiable.smul_const ?_ _
      exact Differentiable.fun_finsetProd fun s _ => by fun_prop)
    (fun y => by
      show Q.CV k r (y : ℂ) f g = _
      rw [hR y g hg]; push_cast; rfl)
  exact congrFun key Y

end GlobalTheory
