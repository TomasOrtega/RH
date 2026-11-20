import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
import Mathlib

open scoped ContDiff
open MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

section ctw

variable {d : ℕ}

/- English proof (translation)
Proceed by induction on `l₁ with`. Consider the case `nil => rfl`. Consider the case `cons i l ih => simp only [List.cons_append, pdc, ih]`.
-/
theorem ctw_pdc_append (l₁ l₂ : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    pdc (l₁ ++ l₂) f = pdc l₁ (pdc l₂ f) := by
  induction l₁ with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, pdc, ih]

/- English proof (translation)
The claim follows from `| [], m, n, f, hf, hl => hf.of_le (by simp only [List.length_nil, zero_add] at hl; exact_mod_cast hl) | i :: l, m, n, f, hf, hl => by have ih := ctw_contDiffOn_pdc hU l (m + 1) n f hf (by simp only [List.length_cons] at hl; omega) simp only [pdc] exact (ih.fderiv_of_isOpen hU (by …`.
-/
theorem ctw_contDiffOn_pdc {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    ∀ (l : List (Fin d)) (m n : ℕ) (f : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l.length + m ≤ n →
      ContDiffOn ℝ m (pdc l f) U
  | [], m, n, f, hf, hl => hf.of_le (by simp only [List.length_nil, zero_add] at hl; exact_mod_cast hl)
  | i :: l, m, n, f, hf, hl => by
      have ih := ctw_contDiffOn_pdc hU l (m + 1) n f hf (by simp only [List.length_cons] at hl; omega)
      simp only [pdc]
      exact (ih.fderiv_of_isOpen hU (by push_cast; exact le_rfl)).clm_apply contDiffOn_const

/- English proof (translation)
The claim follows from `| [], _, _, h => h | i :: l, f, g, h => by intro x hx have ih := ctw_pdc_congr hU l f g h simp only [pdc] rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ih)]`.
-/
theorem ctw_pdc_congr {U : Set (Fin d → ℝ)} (hU : IsOpen U) :
    ∀ (l : List (Fin d)) (f g : (Fin d → ℝ) → ℂ), Set.EqOn f g U → Set.EqOn (pdc l f) (pdc l g) U
  | [], _, _, h => h
  | i :: l, f, g, h => by
      intro x hx
      have ih := ctw_pdc_congr hU l f g h
      simp only [pdc]
      rw [Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) ih)]

/- English proof (translation)
Establish `hga : ContDiffAt ℝ 2 g x` using `hg.contDiffAt (hU.mem_nhds hx)`. Establish `hd : DifferentiableAt ℝ (fderiv ℝ g) x` using `(hga.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero`. Establish `hs` using `hga.isSymmSndFDerivAt (by simp)`. Rewrite using `[fderiv_clm_apply hd (differentiableAt_const v), fderiv_clm_apply hd (differentiableAt_const w)]`. Simplify using `[hs w v]`.
-/
theorem ctw_swap {U : Set (Fin d → ℝ)} (hU : IsOpen U) {g : (Fin d → ℝ) → ℂ} (hg : ContDiffOn ℝ 2 g U)
    {x : Fin d → ℝ} (hx : x ∈ U) (v w : Fin d → ℝ) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fun y => fderiv ℝ g y w) x v := by
  have hga : ContDiffAt ℝ 2 g x := hg.contDiffAt (hU.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hga.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hs := hga.isSymmSndFDerivAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const v), fderiv_clm_apply hd (differentiableAt_const w)]
  simp [hs w v]

/- English proof (translation)
Proceed by induction on `hp with`. Consider the case `nil => intro n f _ _`. Conclude with `Set.eqOn_refl _ _`. Consider the case `@cons a m₁ m₂ hp ih`. Introduce `n f hf hl`.

Establish `h` using `ih n f hf (by simp only [List.length_cons] at hl; omega)`. Establish `e1` using `ctw_pdc_append [a] m₁ f`. Establish `e2` using `ctw_pdc_append [a] m₂ f`. Simplify using `only [List.singleton_append] at e1 e2`. Rewrite using `[e1, e2]`.

Conclude with `ctw_pdc_congr hU [a] _ _ h`. Consider the case `swap a b l`. Introduce `n f hf hl x hx`. Establish `hg : ContDiffOn ℝ 2 (pdc l f) U` using `ctw_contDiffOn_pdc hU l 2 n f hf (by simp only [List.length_cons] at hl; omega)`. Simplify using `only [pdc]`.

Conclude with `ctw_swap hU hg hx _ _`. Consider the case `trans h₁ _ ih₁ ih₂`. Introduce `n f hf hl`. Conclude with `(ih₁ n f hf hl).trans (ih₂ n f hf (h₁.length_eq ▸ hl))`.
-/
theorem ctw_pdc_perm {U : Set (Fin d → ℝ)} (hU : IsOpen U) {l₁ l₂ : List (Fin d)} (hp : l₁.Perm l₂) :
    ∀ (n : ℕ) (f : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l₁.length ≤ n →
      Set.EqOn (pdc l₁ f) (pdc l₂ f) U := by
  induction hp with
  | nil => intro n f _ _; exact Set.eqOn_refl _ _
  | @cons a m₁ m₂ hp ih =>
      intro n f hf hl
      have h := ih n f hf (by simp only [List.length_cons] at hl; omega)
      have e1 := ctw_pdc_append [a] m₁ f
      have e2 := ctw_pdc_append [a] m₂ f
      simp only [List.singleton_append] at e1 e2
      rw [e1, e2]
      exact ctw_pdc_congr hU [a] _ _ h
  | swap a b l =>
      intro n f hf hl x hx
      have hg : ContDiffOn ℝ 2 (pdc l f) U :=
        ctw_contDiffOn_pdc hU l 2 n f hf (by simp only [List.length_cons] at hl; omega)
      simp only [pdc]
      exact ctw_swap hU hg hx _ _
  | trans h₁ _ ih₁ ih₂ =>
      intro n f hf hl
      exact (ih₁ n f hf hl).trans (ih₂ n f hf (h₁.length_eq ▸ hl))

/- English proof (translation)
Establish `hc : Continuous (fun x => F x * G x)`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Distinguish the cases in `hx : x ∈ U`. Conclude with `(hF.continuousAt (hU.mem_nhds hx)).mul hG.continuousAt`.

Establish `h0 : G =ᶠ[nhds x] 0` using `notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hGU h))`. Establish `h1 : (fun x => F x * G x) =ᶠ[nhds x] fun _ => 0` using `h0.mono fun y hy => by simp [hy]`. Conclude with `continuousAt_const.congr h1.symm`. Establish `hcs : HasCompactSupport (F * G)` using `hGc.mul_left`. Conclude with `hc.integrable_of_hasCompactSupport hcs`.
-/
theorem ctw_integrable {U : Set (Fin d → ℝ)} (hU : IsOpen U) {F G : (Fin d → ℝ) → ℂ}
    (hF : ContinuousOn F U) (hG : Continuous G) (hGc : HasCompactSupport G) (hGU : tsupport G ⊆ U) :
    Integrable (fun x => F x * G x) := by
  have hc : Continuous (fun x => F x * G x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hF.continuousAt (hU.mem_nhds hx)).mul hG.continuousAt
    · have h0 : G =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hGU h))
      have h1 : (fun x => F x * G x) =ᶠ[nhds x] fun _ => 0 := h0.mono fun y hy => by simp [hy]
      exact continuousAt_const.congr h1.symm
  have hcs : HasCompactSupport (F * G) := hGc.mul_left
  exact hc.integrable_of_hasCompactSupport hcs

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact subset_rfl`. Consider the case `cons i l ih`. Use `subset_trans ?_ ((tsupport_fderiv_subset ℝ).trans ih)` and prove the remaining obligations. Use `closure_mono ?_` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [Function.mem_support] at hx ⊢`. Introduce `h`. Apply `hx` to reduce the goal to its premises. Simplify using `only [pdc, h, zero_apply]`.
-/
theorem ctw_tsupport_pdc (l : List (Fin d)) (ψ : (Fin d → ℝ) → ℂ) : tsupport (pdc l ψ) ⊆ tsupport ψ := by
  induction l with
  | nil => exact subset_rfl
  | cons i l ih =>
      refine subset_trans ?_ ((tsupport_fderiv_subset ℝ).trans ih)
      refine closure_mono ?_
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h
      apply hx
      simp only [pdc, h, zero_apply]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact hψ`. Consider the case `cons i l ih`. Simplify using `only [pdc]`. Conclude with `contDiff_infty.2 fun n => ((contDiff_infty.1 ih (n + 1)).fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiff_const`.
-/
theorem ctw_contDiff_pdc (l : List (Fin d)) {ψ : (Fin d → ℝ) → ℂ} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (pdc l ψ) := by
  induction l with
  | nil => exact hψ
  | cons i l ih =>
      simp only [pdc]
      exact contDiff_infty.2 fun n =>
        ((contDiff_infty.1 ih (n + 1)).fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiff_const

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => intro n f ψ _ _ _ _ _`. Simplify using `[pdc]`. Consider the case `cons i l ih`. Introduce `n f ψ hf hl hψ hψc hψU`.

Establish `hl' : l.length + 1 ≤ n` using `by simpa using hl`. Establish `hgs : ContDiff ℝ ∞ (pdc l ψ)` using `ctw_contDiff_pdc l hψ`. Establish `hgt : tsupport (pdc l ψ) ⊆ tsupport ψ` using `ctw_tsupport_pdc l ψ`. Establish `hgc : HasCompactSupport (pdc l ψ)` using `hψc.mono' ((subset_tsupport _).trans hgt)`. Establish `hg's : ContDiff ℝ ∞ (pdc (i :: l) ψ)` using `ctw_contDiff_pdc (i :: l) hψ`.

Establish `hg't : tsupport (pdc (i :: l) ψ) ⊆ tsupport ψ` using `ctw_tsupport_pdc (i :: l) ψ`. Establish `hg'c : HasCompactSupport (pdc (i :: l) ψ)` using `hψc.mono' ((subset_tsupport _).trans hg't)`. Establish `hf1 : ContDiffOn ℝ ((n - 1 : ℕ)) (pdc [i] f) U` using `ctw_contDiffOn_pdc hU [i] (n - 1) n f hf (by simp only [List.length_cons, List.length_nil]; omega)`. Establish `hf0 : ContinuousOn (pdc [i] f) U` using `(ctw_contDiffOn_pdc hU [i] 0 n f hf (by simp only [List.length_cons, List.length_nil]; omega)).continuousOn`. Establish `hstep : ∫ x, f x * pdc (i :: l) ψ x = -∫ x, pdc [i] f x * pdc l ψ x`.

Establish `h` using `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f) (g := pdc l ψ) (v := (Pi.single i 1 : Fin d → ℝ)) (ctw_integrable hU hf0 hgs.continuous hgc (hgt.trans hψU)) (ctw_integrable hU hf.continuousOn hg's.continuous hg'c (hg't.trans hψU)) (ctw_integrable hU hf. …`. Conclude with `h`. Rewrite using `[hstep, ih (n - 1) (pdc [i] f) ψ hf1 (by omega) hψ hψc hψU, List.reverse_cons, ctw_pdc_append, List.length_cons, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ctw_ibp {U : Set (Fin d → ℝ)} (hU : IsOpen U) (l : List (Fin d)) :
    ∀ (n : ℕ) (f ψ : (Fin d → ℝ) → ℂ), ContDiffOn ℝ n f U → l.length ≤ n → ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∫ x, f x * pdc l ψ x = (-1 : ℂ) ^ l.length * ∫ x, pdc l.reverse f x * ψ x := by
  induction l with
  | nil => intro n f ψ _ _ _ _ _; simp [pdc]
  | cons i l ih =>
      intro n f ψ hf hl hψ hψc hψU
      have hl' : l.length + 1 ≤ n := by simpa using hl
      have hgs : ContDiff ℝ ∞ (pdc l ψ) := ctw_contDiff_pdc l hψ
      have hgt : tsupport (pdc l ψ) ⊆ tsupport ψ := ctw_tsupport_pdc l ψ
      have hgc : HasCompactSupport (pdc l ψ) := hψc.mono' ((subset_tsupport _).trans hgt)
      have hg's : ContDiff ℝ ∞ (pdc (i :: l) ψ) := ctw_contDiff_pdc (i :: l) hψ
      have hg't : tsupport (pdc (i :: l) ψ) ⊆ tsupport ψ := ctw_tsupport_pdc (i :: l) ψ
      have hg'c : HasCompactSupport (pdc (i :: l) ψ) := hψc.mono' ((subset_tsupport _).trans hg't)
      have hf1 : ContDiffOn ℝ ((n - 1 : ℕ)) (pdc [i] f) U :=
        ctw_contDiffOn_pdc hU [i] (n - 1) n f hf (by simp only [List.length_cons, List.length_nil]; omega)
      have hf0 : ContinuousOn (pdc [i] f) U :=
        (ctw_contDiffOn_pdc hU [i] 0 n f hf (by simp only [List.length_cons, List.length_nil]; omega)).continuousOn
      have hstep : ∫ x, f x * pdc (i :: l) ψ x = -∫ x, pdc [i] f x * pdc l ψ x := by
        have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
          (f := f) (g := pdc l ψ) (v := (Pi.single i 1 : Fin d → ℝ))
          (ctw_integrable hU hf0 hgs.continuous hgc (hgt.trans hψU))
          (ctw_integrable hU hf.continuousOn hg's.continuous hg'c (hg't.trans hψU))
          (ctw_integrable hU hf.continuousOn hgs.continuous hgc (hgt.trans hψU))
          (fun x hx => (hf.contDiffAt (hU.mem_nhds (hψU (hgt hx)))).differentiableAt
            (by exact_mod_cast (show n ≠ 0 by omega)))
          (fun x _ => hgs.differentiable (by simp) x)
        exact h
      rw [hstep, ih (n - 1) (pdc [i] f) ψ hf1 (by omega) hψ hψc hψU, List.reverse_cons, ctw_pdc_append,
        List.length_cons, pow_succ]
      ring

/- English proof (translation)
Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `x`. Distinguish the cases in `hx : x ∈ U`. Conclude with `(ha.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt`. Establish `h0 : φ =ᶠ[nhds x] 0` using `notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hφU h))`.

Establish `h1 : (fun y => a y * φ y) =ᶠ[nhds x] fun _ => 0` using `h0.mono fun y hy => by simp [hy]`. Conclude with `contDiffAt_const.congr_of_eventuallyEq h1`.
-/
theorem ctw_smooth_mul {U : Set (Fin d → ℝ)} (hU : IsOpen U) {a φ : (Fin d → ℝ) → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (hφ : ContDiff ℝ ∞ φ) (hφU : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => a y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (ha.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have h0 : φ =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hx (hφU h))
    have h1 : (fun y => a y * φ y) =ᶠ[nhds x] fun _ => 0 := h0.mono fun y hy => by simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h1

end ctw

/- English proof (translation)
Introduce `d N P U u hU ha hord hu hPu φ hφ hφc hφU`. Establish `hφ0 : ∀ x, x ∉ U → φ x = 0` using `fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))`. Establish `hψ : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d), ContDiff ℝ ∞ (fun y => P.a k w y * φ y) ∧ HasCompactSupport (fun y => P.a k w y * φ y) ∧ tsupport (fun y => P.a k w y * φ y) ⊆ U` using `fun k w => ⟨ctw_smooth_mul hU (ha k w) hφ hφU, hφc.mul_left, tsupport_mul_subset_right.trans hφU⟩`. Establish `hk : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d), (List.ofFn w).length ≤ N` using `fun k w => by`. Rewrite using `[List.length_ofFn]`.

Use `k.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hint : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d), Integrable (fun x => u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x))` using `fun k w => by`. Take `⟨h1, h2, h3⟩` from `hψ k w`. Use `ctw_integrable hU hu.continuousOn (continuous_const.mul (ctw_contDiff_pdc _ h1).continuous) ((h2.mono' ((subset_tsupport _).trans (ctw_tsupport_pdc _ _))).mul_left) (tsupport_mul_subset_right.trans ((ctw_tsupport_pdc _ _).trans h3))` and prove the remaining obligations.

Establish `hint2 : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d), Integrable (fun x => P.a k w x * pdc (List.ofFn w) u x * φ x)` using `fun k w => ctw_integrable hU (((ha k w).continuousOn).mul (ctw_contDiffOn_pdc hU (List.ofFn w) 0 N u hu (by simpa using hk k w)).continuousOn) hφ.continuous hφc hφU`. Establish `hterm : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d), ∫ x, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) = ∫ x, P.a k w x * pdc (List.ofFn w) u x * φ x`. Introduce `k w`. Take `⟨h1, h2, h3⟩` from `hψ k w`. Establish `hI` using `ctw_ibp hU (List.ofFn w) N u _ hu (hk k w) h1 h2 h3`.

Establish `hperm` using `ctw_pdc_perm hU (List.reverse_perm (List.ofFn w)) N u hu (by rw [List.length_reverse]; exact hk k w)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = ∫ x, pdc (List.ofFn w).reverse u x * (P.a k w x * φ x) := by`. Rewrite using `[hI, List.length_ofFn, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]`. Use `_ = ∫ x, P.a k w x * pdc (List.ofFn w) u x * φ x := by`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ U`. Rewrite using `[hperm hx]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hφ0 x hx]`.

Establish `hsplit : (fun x => u x * P.tr φ x) = fun x => ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x)`. Use function extensionality and compare the values at `x`. Simplify using `only [SOp.tr, Finset.mul_sum]`. Establish `hinner : ∀ k : Fin (P.ord + 1), ∫ x, ∑ w : Fin k → Fin d, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) = ∫ x, ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x` using `fun k => by`. Rewrite using `[integral_finsetSum _ (fun w _ => hint k w), integral_finsetSum _ (fun w _ => hint2 k w)]`.

Conclude with `Finset.sum_congr rfl (fun w _ => hterm k w)`. Rewrite using `[hsplit, integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun w _ => hint k w)), Finset.sum_congr rfl (fun k _ => hinner k), ← integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun w _ => hint2 k w))]`. Establish `h0 : (fun x => ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x) = fun _ => (0 : ℂ)`. Use function extensionality and compare the values at `x`. Establish `e : ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x = P.app u x * φ x` using `by simp only [SOp.app, Finset.sum_mul]`.

Rewrite using `[e]`. Distinguish the cases in `hx : x ∈ U`. Rewrite using `[hPu x hx, zero_mul]`. Rewrite using `[hφ0 x hx, mul_zero]`. Rewrite using `[h0, integral_zero]`.
-/
theorem classical_to_weak_solution : ClassToWeak := by
  intro d N P U u hU ha hord hu hPu φ hφ hφc hφU
  have hφ0 : ∀ x, x ∉ U → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))
  have hψ : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      ContDiff ℝ ∞ (fun y => P.a k w y * φ y) ∧ HasCompactSupport (fun y => P.a k w y * φ y) ∧
        tsupport (fun y => P.a k w y * φ y) ⊆ U := fun k w =>
    ⟨ctw_smooth_mul hU (ha k w) hφ hφU, hφc.mul_left, tsupport_mul_subset_right.trans hφU⟩
  have hk : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d), (List.ofFn w).length ≤ N := fun k w => by
    rw [List.length_ofFn]; have := k.isLt; omega
  have hint : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      Integrable (fun x => u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x)) :=
    fun k w => by
      obtain ⟨h1, h2, h3⟩ := hψ k w
      refine ctw_integrable hU hu.continuousOn (continuous_const.mul (ctw_contDiff_pdc _ h1).continuous)
        ((h2.mono' ((subset_tsupport _).trans (ctw_tsupport_pdc _ _))).mul_left)
        (tsupport_mul_subset_right.trans ((ctw_tsupport_pdc _ _).trans h3))
  have hint2 : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      Integrable (fun x => P.a k w x * pdc (List.ofFn w) u x * φ x) := fun k w =>
    ctw_integrable hU (((ha k w).continuousOn).mul
      (ctw_contDiffOn_pdc hU (List.ofFn w) 0 N u hu (by simpa using hk k w)).continuousOn) hφ.continuous hφc hφU
  have hterm : ∀ (k : Fin (P.ord + 1)) (w : Fin k → Fin d),
      ∫ x, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) =
        ∫ x, P.a k w x * pdc (List.ofFn w) u x * φ x := by
    intro k w
    obtain ⟨h1, h2, h3⟩ := hψ k w
    have hI := ctw_ibp hU (List.ofFn w) N u _ hu (hk k w) h1 h2 h3
    have hperm := ctw_pdc_perm hU (List.reverse_perm (List.ofFn w)) N u hu
      (by rw [List.length_reverse]; exact hk k w)
    calc ∫ x, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x)
        = (-1 : ℂ) ^ (k : ℕ) * ∫ x, u x * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x := by
          rw [← integral_const_mul]; congr 1; funext x; ring
      _ = ∫ x, pdc (List.ofFn w).reverse u x * (P.a k w x * φ x) := by
          rw [hI, List.length_ofFn, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
      _ = ∫ x, P.a k w x * pdc (List.ofFn w) u x * φ x := by
          congr 1; funext x
          by_cases hx : x ∈ U
          · rw [hperm hx]; ring
          · simp [hφ0 x hx]
  have hsplit : (fun x => u x * P.tr φ x) = fun x => ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d,
      u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) := by
    funext x; simp only [SOp.tr, Finset.mul_sum]
  have hinner : ∀ k : Fin (P.ord + 1),
      ∫ x, ∑ w : Fin k → Fin d, u x * ((-1 : ℂ) ^ (k : ℕ) * pdc (List.ofFn w) (fun y => P.a k w y * φ y) x) =
        ∫ x, ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x := fun k => by
    rw [integral_finsetSum _ (fun w _ => hint k w), integral_finsetSum _ (fun w _ => hint2 k w)]
    exact Finset.sum_congr rfl (fun w _ => hterm k w)
  rw [hsplit, integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun w _ => hint k w)),
    Finset.sum_congr rfl (fun k _ => hinner k),
    ← integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun w _ => hint2 k w))]
  have h0 : (fun x => ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x) =
      fun _ => (0 : ℂ) := by
    funext x
    have e : ∑ k : Fin (P.ord + 1), ∑ w : Fin k → Fin d, P.a k w x * pdc (List.ofFn w) u x * φ x =
        P.app u x * φ x := by simp only [SOp.app, Finset.sum_mul]
    rw [e]
    by_cases hx : x ∈ U
    · rw [hPu x hx, zero_mul]
    · rw [hφ0 x hx, mul_zero]
  rw [h0, integral_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
