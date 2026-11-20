import Formalism.HermitianCurvature.StatementLE

namespace Formalism.FourierDecayAlt.P.LEx2.A3
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section

/- English proof (translation)
Use function extensionality and compare the values at `ω a`. Simplify using `[mulF]`.
-/
theorem mulF_one' (B : Base) {A : Type} (u : Fn B A) : mulF B (fun x => x ^ (0:ℝ)) u = u := by
  funext ω a; simp [mulF]

/- English proof (translation)
Use function extensionality and compare the values at `ω a`. Establish `h : mulF B (fun _ : ℝ => (1:ℝ)) u = u` using `by funext ω a; simp [mulF]`. Simplify using `[dS, conjS, h]`.
-/
theorem dS_zero (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) : dS B T u 0 = T u := by
  funext ω a
  have h : mulF B (fun _ : ℝ => (1:ℝ)) u = u := by funext ω a; simp [mulF]
  simp [dS, conjS, h]

/- English proof (translation)
The claim follows from `dS_zero B _ _`.
-/
theorem ds_zero {B : Base} (S : Step B) (Y : ℝ) : S.ds Y 0 = S.gX Y := dS_zero B _ _

def DsMeas : Prop := ∀ (B : Base) (S : Step B), S.Meas → S.I4 → ∀ Y ∈ S.J, ∀ (p : ℕ) k, Measurable fun ω => S.ds Y p ω k

/- English proof (translation)
Introduce `p`. Proceed by induction on `p with`. Consider the case `zero => intro s`. Simplify using `using hm s`. Consider the case `succ p ih`.

Introduce `s`. Establish `hlim : ∀ ω, Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ • (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) atTop (𝓝 (iteratedDeriv (p + 1) (fun s => F s ω) s))`. Introduce `ω`. Establish `hd : Differentiable ℝ (iteratedDeriv p (fun s => F s ω))` using `(hsm ω).differentiable_iteratedDeriv p (by exact_mod_cast WithTop.coe_lt_top _)`. Establish `h1` using `(hd s).hasDerivAt.tendsto_slope_zero`.

Rewrite using `[iteratedDeriv_succ]`. Use `h1.comp ?_` and prove the remaining obligations. Use `tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩` and prove the remaining obligations. Conclude with `Filter.Eventually.of_forall (fun n => by`. Establish `: (0:ℝ) < 1 / ((n : ℝ) + 1)` using `by positivity`.

Conclude with `this.ne')`. Use `measurable_of_tendsto_metrizable (f := fun (n : ℕ) ω => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ • (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) ?_ ?_` and prove the remaining obligations. Introduce `n`. Conclude with `((ih _).sub (ih _)).const_smul (((1 : ℝ) / ((n : ℝ) + 1))⁻¹)`. Conclude with `tendsto_pi_nhds.2 hlim`.
-/
theorem meas_iterDeriv {Ω : Type} [MeasurableSpace Ω] (F : ℝ → Ω → ℂ)
    (hsm : ∀ ω, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s => F s ω)) (hm : ∀ s, Measurable (F s)) :
    ∀ (p : ℕ) (s : ℝ), Measurable (fun ω => iteratedDeriv p (fun s => F s ω) s) := by
  intro p
  induction p with
  | zero => intro s; simpa using hm s
  | succ p ih =>
    intro s
    have hlim : ∀ ω, Tendsto (fun n : ℕ => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) atTop
        (𝓝 (iteratedDeriv (p + 1) (fun s => F s ω) s)) := by
      intro ω
      have hd : Differentiable ℝ (iteratedDeriv p (fun s => F s ω)) :=
        (hsm ω).differentiable_iteratedDeriv p (by exact_mod_cast WithTop.coe_lt_top _)
      have h1 := (hd s).hasDerivAt.tendsto_slope_zero
      rw [iteratedDeriv_succ]
      refine h1.comp ?_
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Filter.Eventually.of_forall (fun n => by
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact this.ne')
    refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) ω => ((1 : ℝ) / ((n : ℝ) + 1))⁻¹ •
        (iteratedDeriv p (fun s => F s ω) (s + 1 / ((n : ℝ) + 1)) - iteratedDeriv p (fun s => F s ω) s)) ?_ ?_
    · intro n
      exact ((ih _).sub (ih _)).const_smul (((1 : ℝ) / ((n : ℝ) + 1))⁻¹)
    · exact tendsto_pi_nhds.2 hlim

/- English proof (translation)
Introduce `B S hMeas hI4 Y hY p k`. Take `⟨c, hc⟩` from `hI4 Y hY`. Use `meas_iterDeriv (fun s ω => S.gs Y s ω k) (fun ω => by` as an intermediate fact. Establish `: (fun s : ℝ => S.gs Y s ω k) = fun s : ℝ => ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * c q ω k`. Use function extensionality and compare the values at `s`.

Conclude with `hc s ω k`. Rewrite using `[this]`. Apply `ContDiff.sum` to reduce the goal to its premises. Introduce `q _`. Conclude with `(Complex.ofRealCLM.contDiff.pow q).mul contDiff_const)`.

Use the proof step `(fun s => (hMeas.2.2 Y hY).2 s k) p 0`. Conclude with `this`.
-/
theorem dsMeas : DsMeas := by
  intro B S hMeas hI4 Y hY p k
  obtain ⟨c, hc⟩ := hI4 Y hY
  have := meas_iterDeriv (fun s ω => S.gs Y s ω k) (fun ω => by
      have : (fun s : ℝ => S.gs Y s ω k) = fun s : ℝ => ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * c q ω k := by
        funext s; exact hc s ω k
      rw [this]
      apply ContDiff.sum
      intro q _
      exact (Complex.ofRealCLM.contDiff.pow q).mul contDiff_const)
    (fun s => (hMeas.2.2 Y hY).2 s k) p 0
  exact this

end
end Formalism.FourierDecayAlt.P.LEx2.A3
