import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

/- English proof (translation)
Establish `hc : Continuous (fun x => (f x : ℂ))`. Use `continuous_iff_continuousAt.mpr fun x => ?_` and prove the remaining obligations. Take `⟨e, hxe, rfl⟩` from `hz x`. Establish `hch : IsChart n (⇑e) e` using `fun _ _ => rfl`. Establish `h1` using `(hf e hch).continuousOn`.

Establish `h2 : ContinuousOn (fun y => (f y : ℂ)) e.source`. Use `(h1.comp e.continuousOn (fun y hy => e.map_source hy)).congr fun y hy => ?_` and prove the remaining obligations. Simplify using `[Function.comp, e.left_inv hy]`. Conclude with `h2.continuousAt (e.open_source.mem_nhds hxe)`. Conclude with `(Complex.continuous_re.comp hc).congr fun x => by simp`.
-/
theorem smoothReal_continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  have hc : Continuous (fun x => (f x : ℂ)) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    obtain ⟨e, hxe, rfl⟩ := hz x
    have hch : IsChart n (⇑e) e := fun _ _ => rfl
    have h1 := (hf e hch).continuousOn
    have h2 : ContinuousOn (fun y => (f y : ℂ)) e.source := by
      refine (h1.comp e.continuousOn (fun y hy => e.map_source hy)).congr fun y hy => ?_
      simp [Function.comp, e.left_inv hy]
    exact h2.continuousAt (e.open_source.mem_nhds hxe)
  exact (Complex.continuous_re.comp hc).congr fun x => by simp

/- English proof (translation)
Use `Real.sSup_le ?_ (le_max_right _ _)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(hB x hx).trans (le_max_left _ _)`.
-/
theorem sSup_image_le_max {M : Type*} (g : M → ℝ) (s : Set M) (B : ℝ)
    (hB : ∀ x ∈ s, g x ≤ B) : sSup (g '' s) ≤ max B 0 := by
  refine Real.sSup_le ?_ (le_max_right _ _)
  rintro _ ⟨x, hx, rfl⟩
  exact (hB x hx).trans (le_max_left _ _)

/- English proof (translation)
Introduce `X ph v C ε hph hv hC hε`. Establish `hz` using `X.isLocalHomeomorph`. Establish `hE : SmoothR n X.z (fun y => X.e y + ‖X.z y‖ ^ 2)` using `SmoothR.add n X.z _ _ X.smooth_e (hLZ X.z hz).1`. Establish `hEc : Continuous (fun y => X.e y + ‖X.z y‖ ^ 2)` using `smoothReal_continuous n X.z hz _ hE`. Establish `hExh : ∀ b : ℝ, IsCompact {x | X.e x + ‖X.z x‖ ^ 2 ≤ b}`.

Introduce `b`. Use `(X.isCompact_le b).of_isClosed_subset (isClosed_le hEc continuous_const) ?_` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [mem_ofPred_eq] at hx ⊢`. Use polynomial arithmetic with `[sq_nonneg ‖X.z x‖]`.

Establish `hLeviE : ∀ x ξ, (∑ j, ‖ξ j‖ ^ 2) ≤ (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re`. Introduce `x ξ`. Rewrite using `[levi_add n X.z X.e (fun y => ‖X.z y‖ ^ 2) (SmoothR.ckR n X.z 2 _ X.smooth_e) (SmoothR.ckR n X.z 2 _ (hLZ X.z hz).1) x ξ, (hLZ X.z hz).2 x ξ, Complex.add_re, Complex.ofReal_re]`. Combine the linear relations using `[X.levi_e x ξ]`. Take `⟨b0, hb0⟩` from `hC.bddAbove_image hEc.continuousOn`.

Use `set a : ℝ := b0 + 1 with ha`. Establish `hCa : ∀ x ∈ C, X.e x + ‖X.z x‖ ^ 2 < a`. Introduce `x hx`. Use `hb0 ⟨x, hx, rfl⟩` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨ψ, hψ, hψ0, hcut⟩` from `hPsi X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) a hE hExh`. Establish `hψc : Continuous ψ` using `smoothReal_continuous n X.z hz _ hψ`. Establish `hdc : Continuous (fun x => dSqR n X.z ψ x)`. Unfold `dSqR`. Use `continuous_finsetSum _ (fun j _ => ?_)` and prove the remaining obligations.

Conclude with `((Smooth.continuous n X.z hz _ (Smooth.d n X.z j _ hψ)).norm).pow 2`. Take `⟨R1, hR1, hR1χ⟩` from `hShell X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) ph ψ v a hEc hExh (smoothReal_continuous n X.z hz _ hph) hψc hv`. Use `set g : M → ℝ := fun x => max (2 * ψ x) ((1 + 1 / ε) * dSqR n X.z ψ x) with hg`. Establish `hgc : Continuous g` using `(continuous_const.mul hψc).max (continuous_const.mul hdc)`. Use `set R : ℝ → ℝ := fun t => max (R1 t) (sSup (g '' {x | X.e x + ‖X.z x‖ ^ 2 ≤ t})) with hR`.

Establish `hRb : ∀ b : ℝ, BddAbove (R '' Iic b)`. Introduce `b`. Take `⟨B1, hB1⟩` from `hR1 b`. Take `⟨B, hB⟩` from `(hExh b).bddAbove_image hgc.continuousOn`. Use `⟨max B1 (max B 0), ?_⟩` and prove the remaining obligations.

Introduce and unpack `y ⟨t, ht, rfl⟩`. Use `max_le_max (hB1 ⟨t, ht, rfl⟩) (sSup_image_le_max g _ B ?_)` and prove the remaining obligations. Introduce `x hx`. Conclude with `hB ⟨x, (show X.e x + ‖X.z x‖ ^ 2 ≤ b from le_trans hx ht), rfl⟩`. Establish `hgR : ∀ x, g x ≤ R (X.e x + ‖X.z x‖ ^ 2)`.

Introduce `x`. Use `le_max_of_le_right (le_csSup ((hExh _).bddAbove_image hgc.continuousOn) ⟨x, ?_, rfl⟩)` and prove the remaining obligations. Conclude with `(le_refl (X.e x + ‖X.z x‖ ^ 2))`. Take `⟨χ, hχ, hχa, hχ0, hχ1, hχ2, hχR⟩` from `hChi a R hRb`. Establish `hχs : SmoothR n X.z (fun y => χ (X.e y + ‖X.z y‖ ^ 2))` using `SmoothR.comp n X.z χ hχ _ hE`.

Use `⟨fun x => ph x + χ (X.e x + ‖X.z x‖ ^ 2), ψ, fun y => X.e y + ‖X.z y‖ ^ 2, {x | X.e x + ‖X.z x‖ ^ 2 < a}, SmoothR.add n X.z _ _ hph hχs, hψ, hEc, hcut, isOpen_lt hEc continuous_const, hCa, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [mem_ofPred_eq] at hx`. Use `⟨?_, (hψ0 x (by linarith)).1⟩` and prove the remaining obligations. Use `show ph x + χ (X.e x + ‖X.z x‖ ^ 2) = ph x`.

Rewrite using `[hχa _ hx.le, add_zero]`. Introduce `x`. Establish `: 2 * ψ x ≤ χ (X.e x + ‖X.z x‖ ^ 2)`. Distinguish the cases in `h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1`. Rewrite using `[(hψ0 x h).1, mul_zero]`.

Conclude with `hχ0 _`. Use `push Not at h`. Conclude with `((le_max_left _ _).trans (hgR x)).trans (hχR _ h.le).1`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x ξ`.

Establish `hχ2' : ContDiff ℝ 2 χ` using `hχ.of_le (by norm_cast)`. Rewrite using `[levi_add n X.z ph (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) (SmoothR.ckR n X.z 2 _ hph) (SmoothR.ckR n X.z 2 _ hχs) x ξ, Complex.add_re, hChain X.z hz χ (fun y => X.e y + ‖X.z y‖ ^ 2) hχ2' hE x ξ, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re]`. Establish `hs : 0 ≤ ∑ j, ‖ξ j‖ ^ 2` using `Finset.sum_nonneg (fun j _ => sq_nonneg _)`. Establish `h1 : (1 + 1 / ε) * dSqR n X.z ψ x * ∑ j, ‖ξ j‖ ^ 2 ≤ deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2`. Distinguish the cases in `h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1`.

Rewrite using `[(hψ0 x h).2, mul_zero, zero_mul]`. Conclude with `mul_nonneg (hχ1 _) hs`. Use `push Not at h`. Conclude with `mul_le_mul_of_nonneg_right (((le_max_right _ _).trans (hgR x)).trans (hχR _ h.le).2) hs`. Establish `h2 : deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 ≤ deriv χ (X.e x + ‖X.z x‖ ^ 2) * (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re` using `mul_le_mul_of_nonneg_left (hLeviE x ξ) (hχ1 _)`.

Establish `h3 : 0 ≤ deriv (deriv χ) (X.e x + ‖X.z x‖ ^ 2) * ‖dDot n X.z (fun y => ((X.e y + ‖X.z y‖ ^ 2 : ℝ) : ℂ)) x ξ‖ ^ 2` using `mul_nonneg (hχ2 _) (sq_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hv.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Conclude with `hR1χ χ hχ0 (fun t ht => (hχR t ht).1.trans' (le_max_left _ _))`.
-/
theorem choice (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hChi : ChiStatement) (hPsi : PsiStatement n M)
    (hShell : ShellStatement n M) (hLZ : LeviNormSqStatement n M) (hChain : ChainStatement n M) :
    ChoiceStatement n M := by
  intro X ph v C ε hph hv hC hε
  have hz := X.isLocalHomeomorph

  have hE : SmoothR n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) :=
    SmoothR.add n X.z _ _ X.smooth_e (hLZ X.z hz).1
  have hEc : Continuous (fun y => X.e y + ‖X.z y‖ ^ 2) := smoothReal_continuous n X.z hz _ hE
  have hExh : ∀ b : ℝ, IsCompact {x | X.e x + ‖X.z x‖ ^ 2 ≤ b} := by
    intro b
    refine (X.isCompact_le b).of_isClosed_subset (isClosed_le hEc continuous_const) ?_
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    nlinarith [sq_nonneg ‖X.z x‖]
  have hLeviE : ∀ x ξ, (∑ j, ‖ξ j‖ ^ 2) ≤ (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re := by
    intro x ξ
    rw [levi_add n X.z X.e (fun y => ‖X.z y‖ ^ 2) (SmoothR.ckR n X.z 2 _ X.smooth_e)
      (SmoothR.ckR n X.z 2 _ (hLZ X.z hz).1) x ξ, (hLZ X.z hz).2 x ξ, Complex.add_re,
      Complex.ofReal_re]
    linarith [X.levi_e x ξ]

  obtain ⟨b0, hb0⟩ := hC.bddAbove_image hEc.continuousOn
  set a : ℝ := b0 + 1 with ha
  have hCa : ∀ x ∈ C, X.e x + ‖X.z x‖ ^ 2 < a := by
    intro x hx
    have := hb0 ⟨x, hx, rfl⟩
    linarith

  obtain ⟨ψ, hψ, hψ0, hcut⟩ := hPsi X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) a hE hExh
  have hψc : Continuous ψ := smoothReal_continuous n X.z hz _ hψ
  have hdc : Continuous (fun x => dSqR n X.z ψ x) := by
    unfold dSqR
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact ((Smooth.continuous n X.z hz _ (Smooth.d n X.z j _ hψ)).norm).pow 2

  obtain ⟨R1, hR1, hR1χ⟩ := hShell X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) ph ψ v a hEc hExh
    (smoothReal_continuous n X.z hz _ hph) hψc hv
  set g : M → ℝ := fun x => max (2 * ψ x) ((1 + 1 / ε) * dSqR n X.z ψ x) with hg
  have hgc : Continuous g := (continuous_const.mul hψc).max (continuous_const.mul hdc)
  set R : ℝ → ℝ := fun t => max (R1 t) (sSup (g '' {x | X.e x + ‖X.z x‖ ^ 2 ≤ t})) with hR
  have hRb : ∀ b : ℝ, BddAbove (R '' Iic b) := by
    intro b
    obtain ⟨B1, hB1⟩ := hR1 b
    obtain ⟨B, hB⟩ := (hExh b).bddAbove_image hgc.continuousOn
    refine ⟨max B1 (max B 0), ?_⟩
    rintro y ⟨t, ht, rfl⟩
    refine max_le_max (hB1 ⟨t, ht, rfl⟩) (sSup_image_le_max g _ B ?_)
    intro x hx
    exact hB ⟨x, (show X.e x + ‖X.z x‖ ^ 2 ≤ b from le_trans hx ht), rfl⟩
  have hgR : ∀ x, g x ≤ R (X.e x + ‖X.z x‖ ^ 2) := by
    intro x
    refine le_max_of_le_right (le_csSup ((hExh _).bddAbove_image hgc.continuousOn) ⟨x, ?_, rfl⟩)
    exact (le_refl (X.e x + ‖X.z x‖ ^ 2))

  obtain ⟨χ, hχ, hχa, hχ0, hχ1, hχ2, hχR⟩ := hChi a R hRb
  have hχs : SmoothR n X.z (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) := SmoothR.comp n X.z χ hχ _ hE
  refine ⟨fun x => ph x + χ (X.e x + ‖X.z x‖ ^ 2), ψ, fun y => X.e y + ‖X.z y‖ ^ 2,
    {x | X.e x + ‖X.z x‖ ^ 2 < a}, SmoothR.add n X.z _ _ hph hχs, hψ, hEc, hcut,
    isOpen_lt hEc continuous_const, hCa, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_ofPred_eq] at hx
    refine ⟨?_, (hψ0 x (by linarith)).1⟩
    show ph x + χ (X.e x + ‖X.z x‖ ^ 2) = ph x
    rw [hχa _ hx.le, add_zero]
  · intro x
    have : 2 * ψ x ≤ χ (X.e x + ‖X.z x‖ ^ 2) := by
      by_cases h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1
      · rw [(hψ0 x h).1, mul_zero]; exact hχ0 _
      · push Not at h
        exact ((le_max_left _ _).trans (hgR x)).trans (hχR _ h.le).1
    linarith
  · intro x ξ
    have hχ2' : ContDiff ℝ 2 χ := hχ.of_le (by norm_cast)
    rw [levi_add n X.z ph (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) (SmoothR.ckR n X.z 2 _ hph)
      (SmoothR.ckR n X.z 2 _ hχs) x ξ, Complex.add_re,
      hChain X.z hz χ (fun y => X.e y + ‖X.z y‖ ^ 2) hχ2' hE x ξ, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re]
    have hs : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have h1 : (1 + 1 / ε) * dSqR n X.z ψ x * ∑ j, ‖ξ j‖ ^ 2 ≤
        deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
      by_cases h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1
      · rw [(hψ0 x h).2, mul_zero, zero_mul]
        exact mul_nonneg (hχ1 _) hs
      · push Not at h
        exact mul_le_mul_of_nonneg_right
          (((le_max_right _ _).trans (hgR x)).trans (hχR _ h.le).2) hs
    have h2 : deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 ≤
        deriv χ (X.e x + ‖X.z x‖ ^ 2) *
          (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re :=
      mul_le_mul_of_nonneg_left (hLeviE x ξ) (hχ1 _)
    have h3 : 0 ≤ deriv (deriv χ) (X.e x + ‖X.z x‖ ^ 2) *
        ‖dDot n X.z (fun y => ((X.e y + ‖X.z y‖ ^ 2 : ℝ) : ℂ)) x ξ‖ ^ 2 :=
      mul_nonneg (hχ2 _) (sq_nonneg _)
    linarith
  · refine ⟨hv.aestronglyMeasurable, ?_⟩
    exact hR1χ χ hχ0 (fun t ht => (hχR t ht).1.trans' (le_max_left _ _))

end

end ReciprocityTheory.L2DbarEstimates.F
