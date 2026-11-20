import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

noncomputable section

def llShift (c t : ℝ) : ℝ :=
  Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) * (t + c) +
    (1 - Real.smoothTransition ((t + 3 * c / 4) / (c / 4)))

/- English proof (translation)
Unfold `llShift`. Establish `h1 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition ((t + 3 * c / 4) / (c / 4)))` using `Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)`. Conclude with `(h1.mul (contDiff_id.add contDiff_const)).add (contDiff_const.sub h1)`.
-/
theorem llShift_contDiff (c : ℝ) : ContDiff ℝ ∞ (llShift c) := by
  unfold llShift
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => Real.smoothTransition ((t + 3 * c / 4) / (c / 4))) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const _)
  exact (h1.mul (contDiff_id.add contDiff_const)).add (contDiff_const.sub h1)

/- English proof (translation)
Unfold `llShift`. Use `set s := Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) with hs`. Establish `h0 : 0 ≤ s` using `Real.smoothTransition.nonneg _`. Establish `h1 : s ≤ 1` using `Real.smoothTransition.le_one _`. Break down `eq_or_lt_of_le h0 with h | h` into its components or cases.

Rewrite using `[← h]`. Evaluate the numerical expressions. Establish `ht : 0 < (t + 3 * c / 4) / (c / 4)`. Assume the negation of the conclusion as `hn`. Use `Real.smoothTransition.zero_of_nonpos (not_lt.mp hn)` as an intermediate fact.

Rewrite `this` using `[← hs]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht' : 0 < t + 3 * c / 4`. Use `(div_pos_iff.mp ht)` as an intermediate fact. Break down `this with h2 | h2` into its components or cases.

Conclude with `h2.1`. Combine the linear relations using `[h2.2]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem llShift_pos {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 < llShift c t := by
  unfold llShift
  set s := Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) with hs
  have h0 : 0 ≤ s := Real.smoothTransition.nonneg _
  have h1 : s ≤ 1 := Real.smoothTransition.le_one _
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; norm_num
  · have ht : 0 < (t + 3 * c / 4) / (c / 4) := by
      by_contra hn
      have := Real.smoothTransition.zero_of_nonpos (not_lt.mp hn)
      rw [← hs] at this; linarith
    have ht' : 0 < t + 3 * c / 4 := by
      have := (div_pos_iff.mp ht)
      rcases this with h2 | h2
      · exact h2.1
      · linarith [h2.2]
    nlinarith

/- English proof (translation)
Unfold `llShift`. Establish `: Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) = 1`. Apply `Real.smoothTransition.one_of_one_le` to reduce the goal to its premises. Rewrite using `[le_div_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem llShift_eq {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 ≤ t) : llShift c t = t + c := by
  unfold llShift
  have : Real.smoothTransition ((t + 3 * c / 4) / (c / 4)) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [this]; ring

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => show Smooth n z (fun x => ((∑ i ∈ (∅ : Finset ι), f i x : ℝ) : ℂ))`. Simplify using `using Smooth.const n z (0 : ℂ)`. Consider the case `insert a s ha ih`. Establish `h1` using `SmoothR.add n z (f a) (fun x => ∑ i ∈ s, f i x) (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`.

Simplify `h1` using `[Finset.sum_insert ha]`.
-/
theorem llSmoothR_sum {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℝ) (hf : ∀ i ∈ s, SmoothR n z (f i)) :
    SmoothR n z (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    show Smooth n z (fun x => ((∑ i ∈ (∅ : Finset ι), f i x : ℝ) : ℂ))
    simpa using Smooth.const n z (0 : ℂ)
  | insert a s ha ih =>
    have h1 := SmoothR.add n z (f a) (fun x => ∑ i ∈ s, f i x)
      (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1

/- English proof (translation)
Establish `h1 : SmoothR n z (fun x => ∑ i, ‖g i x‖ ^ 2)` using `llSmoothR_sum n z Finset.univ (fun i x => ‖g i x‖ ^ 2) (fun i _ => Smooth.normSq n z (g i) (Holo.smooth n z (g i) (hg i)))`. Establish `h2 : SmoothR n z (fun x => Real.exp (-ph x))` using `SmoothR.comp n z (fun t => Real.exp (-t)) (Real.contDiff_exp.comp contDiff_neg) ph hph`. Establish `h3 : SmoothR n z (fun _ : M => (r ^ 2)⁻¹)` using `Smooth.const n z (((r ^ 2)⁻¹ : ℝ) : ℂ)`. Establish `h4` using `SmoothR.mul n z _ _ (SmoothR.mul n z _ _ h1 h2) h3`. Establish `he : ev n g ph r = fun x => (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) * (r ^ 2)⁻¹`.

Use function extensionality and compare the values at `x`. Simplify using `[ev, div_eq_mul_inv]`. Rewrite using `[he]`. Conclude with `h4`.
-/
theorem llSmoothR_ev {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) :
    SmoothR n z (ev n g ph r) := by
  have h1 : SmoothR n z (fun x => ∑ i, ‖g i x‖ ^ 2) :=
    llSmoothR_sum n z Finset.univ (fun i x => ‖g i x‖ ^ 2)
      (fun i _ => Smooth.normSq n z (g i) (Holo.smooth n z (g i) (hg i)))
  have h2 : SmoothR n z (fun x => Real.exp (-ph x)) :=
    SmoothR.comp n z (fun t => Real.exp (-t)) (Real.contDiff_exp.comp contDiff_neg) ph hph
  have h3 : SmoothR n z (fun _ : M => (r ^ 2)⁻¹) := Smooth.const n z (((r ^ 2)⁻¹ : ℝ) : ℂ)
  have h4 := SmoothR.mul n z _ _ (SmoothR.mul n z _ _ h1 h2) h3
  have he : ev n g ph r = fun x => (∑ i, ‖g i x‖ ^ 2) * Real.exp (-ph x) * (r ^ 2)⁻¹ := by
    funext x; simp [ev, div_eq_mul_inv]
  rw [he]; exact h4

/- English proof (translation)
Unfold `ev`. Conclude with `div_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)`.
-/
theorem llEv_nonneg {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) :
    0 ≤ ev n g ph r x := by
  unfold ev
  exact div_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Real.exp_pos _).le)
    (sq_nonneg _)

def llLog (c t : ℝ) : ℝ := Real.log (llShift c t)

/- English proof (translation)
The claim follows from `(llShift_contDiff c).log fun t => (llShift_pos hc t).ne'`.
-/
theorem llLog_contDiff {c : ℝ} (hc : 0 < c) : ContDiff ℝ ∞ (llLog c) :=
  (llShift_contDiff c).log fun t => (llShift_pos hc t).ne'

/- English proof (translation)
Use `filter_upwards [lt_mem_nhds ht] with s hs`. Simplify using `[llLog, llShift_eq hc hs.le]`.
-/
theorem llLog_eventually {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 < t) :
    llLog c =ᶠ[𝓝 t] fun s => Real.log (s + c) := by
  filter_upwards [lt_mem_nhds ht] with s hs
  simp [llLog, llShift_eq hc hs.le]

/- English proof (translation)
Rewrite using `[(llLog_eventually hc ht).deriv_eq]`. Establish `hpos : t + c ≠ 0` using `by linarith`. Use `((hasDerivAt_id t).add_const c).log hpos` as an intermediate fact. Simplify using `using this.deriv`.
-/
theorem llLog_deriv {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 < t) :
    deriv (llLog c) t = (t + c)⁻¹ := by
  rw [(llLog_eventually hc ht).deriv_eq]
  have hpos : t + c ≠ 0 := by linarith
  have := ((hasDerivAt_id t).add_const c).log hpos
  simpa using this.deriv

/- English proof (translation)
Establish `hev : deriv (llLog c) =ᶠ[𝓝 t] fun s => (s + c)⁻¹` using `by filter_upwards [lt_mem_nhds ht] with s hs`. Conclude with `llLog_deriv hc hs`. Rewrite using `[hev.deriv_eq]`. Establish `hpos : t + c ≠ 0` using `by linarith`. Establish `h1` using `((hasDerivAt_id t).add_const c).inv hpos`.

Establish `h2 : HasDerivAt (fun s => (s + c)⁻¹) (-((t + c) ^ 2)⁻¹) t`. Apply the tactic sequence `convert h1 using 1 <;> first | rfl | (simp [div_eq_mul_inv])`. Conclude with `h2.deriv`.
-/
theorem llLog_deriv2 {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : -c / 2 < t) :
    deriv (deriv (llLog c)) t = -((t + c) ^ 2)⁻¹ := by
  have hev : deriv (llLog c) =ᶠ[𝓝 t] fun s => (s + c)⁻¹ := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact llLog_deriv hc hs
  rw [hev.deriv_eq]
  have hpos : t + c ≠ 0 := by linarith
  have h1 := ((hasDerivAt_id t).add_const c).inv hpos
  have h2 : HasDerivAt (fun s => (s + c)⁻¹) (-((t + c) ^ 2)⁻¹) t := by
    convert h1 using 1 <;> first | rfl | (simp [div_eq_mul_inv])
  exact h2.deriv

end

end ReciprocityTheory.L2DbarEstimates.I
