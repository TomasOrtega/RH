import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.SUChartSection

/- English proof (translation)
Simplify using `only [yF, yM, Matrix.mul_apply, mat, Matrix.of_apply]`. Establish `hk : gsB X w τ k j = ∑ m, if k = m then gsB X w τ m j else 0` using `by simp`. Rewrite using `[Finset.sum_filter, hk, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy m k with h | h | h` into its components or cases.

Simplify using `[h, h.ne']`. Substitute `h` using the available equality. Simplify using `[nmat]`. Establish `h1 : ¬ m < k` using `not_lt.2 h.le`. Establish `h2 : k ≠ m` using `h.ne`.

Simplify using `[nmat, h1, h2]`.
-/
theorem yF_expand {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (w : V (nd X)) (τ : X.Ψ) (k j : Fin r) :
    yF X w τ k j = (∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m j) + gsB X w τ k j := by
  simp only [yF, yM, Matrix.mul_apply, mat, Matrix.of_apply]
  have hk : gsB X w τ k j = ∑ m, if k = m then gsB X w τ m j else 0 := by simp
  rw [Finset.sum_filter, hk, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rcases lt_trichotomy m k with h | h | h
  · simp [h, h.ne']
  · subst h; simp [nmat]
  · have h1 : ¬ m < k := not_lt.2 h.le
    have h2 : k ≠ m := h.ne
    simp [nmat, h1, h2]

/- English proof (translation)
Distinguish the cases in `hd : DifferentiableAt ℝ (yF X) 0`. Use `swap`. Simplify using `[dY, fderiv_zero_of_not_differentiableAt hd]`. Establish `hY : ∀ k j : Fin r, DifferentiableAt ℝ (fun w => yF X w τ k j) 0`. Introduce `k j`.

Conclude with `differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hd τ) k) j`. Establish `hN : ∀ k m : Fin r, DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ k m) 0` using `fun k m => ((PoinPf.diff_nmat X τ k m) 0).restrictScalars ℝ`. Establish `hB : ∀ n : ℕ, ∀ k : Fin r, k.val = n → DifferentiableAt ℝ (fun w => gsB X w τ k a) 0`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`.

Consider the case `_ n ih`. Introduce `k hk`. Establish `hrepr : (fun w => gsB X w τ k a) = fun w => yF X w τ k a - ∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m a`. Use function extensionality and compare the values at `w`. Rewrite using `[yF_expand]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hrepr]`. Use `(hY k a).sub (DifferentiableAt.fun_sum fun m hm => (hN k m).mul (ih m.val ?_ m rfl))` and prove the remaining obligations. Use `(Finset.mem_filter.1 hm).2` as an intermediate fact. Rewrite `this` using `[Fin.lt_def]`.

Use linear arithmetic over natural numbers and integers. Establish `hN0 : ∀ m : Fin r, m < a → nmat X 0 τ a m = 0`. Introduce `m hm`. Use `congrFun (congrFun (PoinPf.nmat_zero X τ) a) m` as an intermediate fact. Simplify using `only [mat, Matrix.of_apply, Matrix.one_apply, hm.ne', if_false] at this`.

Conclude with `this`. Establish `hB0 : ∀ m : Fin r, m < a → gsB X 0 τ m a = 0`. Introduce `m hm`. Rewrite using `[gsB_zero, Matrix.one_apply, if_neg hm.ne]`. Establish `hsum : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a) (0 : V (nd X) →L[ℝ] ℂ) 0`.

Establish `h : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a) (∑ m ∈ Finset.univ.filter (· < a), (nmat X 0 τ a m • fderiv ℝ (fun w => gsB X w τ m a) 0 + gsB X 0 τ m a • fderiv ℝ (fun w : V (nd X) => nmat X w τ a m) 0)) 0` using `HasFDerivAt.fun_sum (fun m _ => (hN a m).hasFDerivAt.mul (hB m.val m rfl).hasFDerivAt)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `symm`. Use `Finset.sum_eq_zero fun m hm => ?_` and prove the remaining obligations. Establish `hm'` using `(Finset.mem_filter.1 hm).2`.

Rewrite using `[hN0 m hm', hB0 m hm', zero_smul, zero_smul, add_zero]`. Establish `him : HasFDerivAt (fun w => (yF X w τ a a).im) (0 : V (nd X) →L[ℝ] ℝ) 0`. Establish `h` using `Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) hsum`. Rewrite `h` using `[ContinuousLinearMap.comp_zero]`. Establish `hf : (fun w => (yF X w τ a a).im) = ⇑Complex.imCLM ∘ fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a`.

Use function extensionality and compare the values at `w`. Simplify using `only [Function.comp_apply, Complex.imCLM_apply]`. Rewrite using `[yF_expand, Complex.add_im, gsB_diag, Complex.ofReal_im, add_zero]`. Rewrite using `[hf]`. Conclude with `h`.

Set `L : (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ` to `(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) a).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) a).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))`. Establish `hc : HasFDerivAt (fun w => (yF X w τ a a).im) (Complex.imCLM.comp (L.comp (dY X))) 0` using `Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) (L.hasFDerivAt.comp (0 : V (nd X)) hd.hasFDerivAt)`. Use `congrArg (fun L => L z) (hc.unique him)` as an intermediate fact. Simplify `this` using `[L]`.
-/
theorem diagreal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (_hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    (dY X z τ a a).im = 0 := by
  by_cases hd : DifferentiableAt ℝ (yF X) 0
  swap
  · simp [dY, fderiv_zero_of_not_differentiableAt hd]
  have hY : ∀ k j : Fin r, DifferentiableAt ℝ (fun w => yF X w τ k j) 0 := by
    intro k j
    exact differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hd τ) k) j
  have hN : ∀ k m : Fin r, DifferentiableAt ℝ (fun w : V (nd X) => nmat X w τ k m) 0 := fun k m =>
    ((PoinPf.diff_nmat X τ k m) 0).restrictScalars ℝ
  have hB : ∀ n : ℕ, ∀ k : Fin r, k.val = n → DifferentiableAt ℝ (fun w => gsB X w τ k a) 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro k hk
      have hrepr : (fun w => gsB X w τ k a) = fun w => yF X w τ k a -
          ∑ m ∈ Finset.univ.filter (· < k), nmat X w τ k m * gsB X w τ m a := by
        funext w; rw [yF_expand]; ring
      rw [hrepr]
      refine (hY k a).sub (DifferentiableAt.fun_sum fun m hm => (hN k m).mul (ih m.val ?_ m rfl))
      have := (Finset.mem_filter.1 hm).2
      rw [Fin.lt_def] at this
      omega
  have hN0 : ∀ m : Fin r, m < a → nmat X 0 τ a m = 0 := by
    intro m hm
    have := congrFun (congrFun (PoinPf.nmat_zero X τ) a) m
    simp only [mat, Matrix.of_apply, Matrix.one_apply, hm.ne', if_false] at this
    exact this
  have hB0 : ∀ m : Fin r, m < a → gsB X 0 τ m a = 0 := by
    intro m hm
    rw [gsB_zero, Matrix.one_apply, if_neg hm.ne]
  have hsum : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
      (0 : V (nd X) →L[ℝ] ℂ) 0 := by
    have h : HasFDerivAt (fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a)
        (∑ m ∈ Finset.univ.filter (· < a), (nmat X 0 τ a m • fderiv ℝ (fun w => gsB X w τ m a) 0 +
          gsB X 0 τ m a • fderiv ℝ (fun w : V (nd X) => nmat X w τ a m) 0)) 0 :=
      HasFDerivAt.fun_sum (fun m _ => (hN a m).hasFDerivAt.mul (hB m.val m rfl).hasFDerivAt)
    convert h using 1
    symm
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' := (Finset.mem_filter.1 hm).2
    rw [hN0 m hm', hB0 m hm', zero_smul, zero_smul, add_zero]
  have him : HasFDerivAt (fun w => (yF X w τ a a).im) (0 : V (nd X) →L[ℝ] ℝ) 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) hsum
    rw [ContinuousLinearMap.comp_zero] at h
    have hf : (fun w => (yF X w τ a a).im) =
        ⇑Complex.imCLM ∘ fun w => ∑ m ∈ Finset.univ.filter (· < a), nmat X w τ a m * gsB X w τ m a := by
      funext w
      simp only [Function.comp_apply, Complex.imCLM_apply]
      rw [yF_expand, Complex.add_im, gsB_diag, Complex.ofReal_im, add_zero]
    rw [hf]; exact h
  let L : (X.Ψ → Fin r → Fin r → ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℂ) a).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => Fin r → ℂ) a).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X.Ψ => Fin r → Fin r → ℂ) τ))
  have hc : HasFDerivAt (fun w => (yF X w τ a a).im) (Complex.imCLM.comp (L.comp (dY X))) 0 :=
    Complex.imCLM.hasFDerivAt.comp (0 : V (nd X)) (L.hasFDerivAt.comp (0 : V (nd X)) hd.hasFDerivAt)
  have := congrArg (fun L => L z) (hc.unique him)
  simpa [L] using this

end GlobalTheory.SUChartSection
