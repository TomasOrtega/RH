import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

namespace PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts

open ReciprocityTheory.AnForm Filter Topology Set Metric Complex

/- English proof (translation)
Establish `hUo : IsOpen (ball c r)` using `isOpen_ball`. Set `J : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ)` to `Complex.I • ContinuousLinearMap.id ℝ (Fin e → ℂ)`. Set `P : ((Fin e → ℂ) →L[ℝ] ℝ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ)` to `(ContinuousLinearMap.compL ℝ (Fin e → ℂ) (Fin e → ℂ) ℝ).flip J`. Establish `hP : ∀ (L : (Fin e → ℂ) →L[ℝ] ℝ) (w : Fin e → ℂ), P L w = L (Complex.I • w)` using `fun L w => rfl`. Set `ω : (Fin e → ℂ) → (Fin e → ℂ) →L[ℝ] ℝ` to `fun z => -P (fderiv ℝ d z)`.

Establish `hC : ∀ a ∈ ball c r, ContDiffAt ℝ 2 d a` using `fun a ha => hd.contDiffAt (hUo.mem_nhds ha)`. Establish `hω : ∀ a ∈ ball c r, HasFDerivAt ω (-(P.comp (fderiv ℝ (fderiv ℝ d) a))) a`. Introduce `a ha`. Establish `h1 : HasFDerivAt (fderiv ℝ d) (fderiv ℝ (fderiv ℝ d) a) a` using `(((hC a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt`. Conclude with `(P.hasFDerivAt.comp a h1).neg`.

Establish `hωd : DifferentiableOn ℝ ω (ball c r)` using `fun a ha => (hω a ha).differentiableAt.differentiableWithinAt`. Establish `hsymm : ∀ a ∈ ball c r, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x`. Introduce `a ha x y`. Rewrite using `[(hω a ha).fderiv]`. Establish `hS : IsSymmSndFDerivAt ℝ d a` using `(hC a ha).isSymmSndFDerivAt (by simp)`.

Establish `hL : ∀ w, fderiv ℝ (fderiv ℝ d) a w w + fderiv ℝ (fderiv ℝ d) a (Complex.I • w) (Complex.I • w) = 0`. Introduce `w`. Establish `h` using `h0 a ha w`. Simplify using `only [levi] at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hB : ∀ u v, fderiv ℝ (fderiv ℝ d) a u v + fderiv ℝ (fderiv ℝ d) a (Complex.I • u) (Complex.I • v) = 0`. Introduce `u v`. Establish `h1` using `hL (u + v)`. Establish `h2` using `hL u`. Establish `h3` using `hL v`.

Simplify using `only [smul_add, map_add, ContinuousLinearMap.add_apply] at h1`. Establish `e1` using `hS u v`. Establish `e2` using `hS (Complex.I • u) (Complex.I • v)`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, hP]`.

Establish `k1` using `hB x (Complex.I • y)`. Rewrite `k1` using `[smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]`. Establish `k2` using `hS (Complex.I • x) y`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨v, hv⟩` from `(convex_ball c r).exists_forall_hasFDerivAt_of_fderiv_symmetric hUo hωd hsymm`.

Use `⟨fun z => (d z : ℂ) + (v z : ℂ) * Complex.I, ?_, ?_⟩` and prove the remaining obligations. Establish `hO` using `ReciprocityTheory.AnForm.Osgood.osgood`. Unfold `ReciprocityTheory.AnForm.Osgood.OsgoodStatement at hO`. Apply `hO e _ _ hUo` to reduce the goal to its premises. Introduce `z hz`.

Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Establish `hdz : HasFDerivAt d (fderiv ℝ d z) z` using `((hC z hz).differentiableAt (by norm_num)).hasFDerivAt`. Establish `hG : HasFDerivAt (fun z => (d z : ℂ) + (v z : ℂ) * Complex.I) (Complex.ofRealCLM.comp (fderiv ℝ d z) + Complex.I • Complex.ofRealCLM.comp (ω z)) z` using `(Complex.ofRealCLM.hasFDerivAt.comp z hdz).add ((Complex.ofRealCLM.hasFDerivAt.comp z (hv z hz)).mul_const Complex.I)`. Rewrite using `[differentiableAt_iff_restrictScalars ℝ hG.differentiableAt]`. Use `⟨StrongDual.extendRCLike (fderiv ℝ d z), ?_⟩` and prove the remaining obligations.

Rewrite using `[hG.fderiv]`. Use extensionality with `w`. Simplify using `[StrongDual.extendRCLike_apply, ω, hP]`. Expand and normalize the polynomial expressions, which then agree. Introduce `z _`.

Simplify using the standard rewrite rules.
-/
theorem exists_re_of_levi_zero {e : ℕ} {d : (Fin e → ℂ) → ℝ} {c : Fin e → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ContDiffOn ℝ 2 d (ball c r)) (h0 : ∀ z ∈ ball c r, ∀ w, levi d z w = 0) :
    ∃ G : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ G (ball c r) ∧ ∀ z ∈ ball c r, d z = (G z).re := by
  have hUo : IsOpen (ball c r) := isOpen_ball
  let J : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) := Complex.I • ContinuousLinearMap.id ℝ (Fin e → ℂ)
  let P : ((Fin e → ℂ) →L[ℝ] ℝ) →L[ℝ] ((Fin e → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin e → ℂ) (Fin e → ℂ) ℝ).flip J
  have hP : ∀ (L : (Fin e → ℂ) →L[ℝ] ℝ) (w : Fin e → ℂ), P L w = L (Complex.I • w) := fun L w => rfl
  let ω : (Fin e → ℂ) → (Fin e → ℂ) →L[ℝ] ℝ := fun z => -P (fderiv ℝ d z)
  have hC : ∀ a ∈ ball c r, ContDiffAt ℝ 2 d a := fun a ha => hd.contDiffAt (hUo.mem_nhds ha)
  have hω : ∀ a ∈ ball c r, HasFDerivAt ω (-(P.comp (fderiv ℝ (fderiv ℝ d) a))) a := by
    intro a ha
    have h1 : HasFDerivAt (fderiv ℝ d) (fderiv ℝ (fderiv ℝ d) a) a :=
      (((hC a ha).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    exact (P.hasFDerivAt.comp a h1).neg
  have hωd : DifferentiableOn ℝ ω (ball c r) := fun a ha =>
    (hω a ha).differentiableAt.differentiableWithinAt
  have hsymm : ∀ a ∈ ball c r, ∀ x y, fderiv ℝ ω a x y = fderiv ℝ ω a y x := by
    intro a ha x y
    rw [(hω a ha).fderiv]
    have hS : IsSymmSndFDerivAt ℝ d a := (hC a ha).isSymmSndFDerivAt (by simp)
    have hL : ∀ w, fderiv ℝ (fderiv ℝ d) a w w
        + fderiv ℝ (fderiv ℝ d) a (Complex.I • w) (Complex.I • w) = 0 := by
      intro w
      have h := h0 a ha w
      simp only [levi] at h
      linarith
    have hB : ∀ u v, fderiv ℝ (fderiv ℝ d) a u v
        + fderiv ℝ (fderiv ℝ d) a (Complex.I • u) (Complex.I • v) = 0 := by
      intro u v
      have h1 := hL (u + v)
      have h2 := hL u
      have h3 := hL v
      simp only [smul_add, map_add, ContinuousLinearMap.add_apply] at h1
      have e1 := hS u v
      have e2 := hS (Complex.I • u) (Complex.I • v)
      linarith
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply, hP]
    have k1 := hB x (Complex.I • y)
    rw [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg] at k1
    have k2 := hS (Complex.I • x) y
    linarith
  obtain ⟨v, hv⟩ := (convex_ball c r).exists_forall_hasFDerivAt_of_fderiv_symmetric hUo hωd hsymm
  refine ⟨fun z => (d z : ℂ) + (v z : ℂ) * Complex.I, ?_, ?_⟩
  · have hO := ReciprocityTheory.AnForm.Osgood.osgood
    unfold ReciprocityTheory.AnForm.Osgood.OsgoodStatement at hO
    apply hO e _ _ hUo
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    have hdz : HasFDerivAt d (fderiv ℝ d z) z :=
      ((hC z hz).differentiableAt (by norm_num)).hasFDerivAt
    have hG : HasFDerivAt (fun z => (d z : ℂ) + (v z : ℂ) * Complex.I)
        (Complex.ofRealCLM.comp (fderiv ℝ d z) + Complex.I • Complex.ofRealCLM.comp (ω z)) z :=
      (Complex.ofRealCLM.hasFDerivAt.comp z hdz).add
        ((Complex.ofRealCLM.hasFDerivAt.comp z (hv z hz)).mul_const Complex.I)
    rw [differentiableAt_iff_restrictScalars ℝ hG.differentiableAt]
    refine ⟨StrongDual.extendRCLike (fderiv ℝ d z), ?_⟩
    rw [hG.fderiv]
    ext w
    simp [StrongDual.extendRCLike_apply, ω, hP]
    ring
  · intro z _
    simp

end PositivityTheory.UnitarySelfGeneration.HolomorphicMinorCharts
