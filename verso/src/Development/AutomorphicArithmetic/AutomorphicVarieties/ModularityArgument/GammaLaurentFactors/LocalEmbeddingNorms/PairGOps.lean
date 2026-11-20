import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.PairGOps

noncomputable section

open Polynomial

namespace UpperTheory.V.Z.Gam

/- English proof (translation)
Introduce `h0`. Apply `h` to reduce the goal to its premises. Use function extensionality and compare the values at `s`. Use `congrFun h0 (s + z)` as an intermediate fact. Simplify using `using this`.
-/
private theorem ne_zero_sub {f : ℂ → ℂ} (h : f ≠ 0) (z : ℂ) : (fun s => f (s - z)) ≠ 0 := by
  intro h0
  apply h
  funext s
  have := congrFun h0 (s + z)
  simpa using this

/- English proof (translation)
Introduce `hfg`. Apply `hg0` to reduce the goal to its premises. Choose the witnesses or unpack the hypotheses as in `⟨z₀, hz₀⟩ : ∃ z, f z ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Conclude with `hf0 (funext hcon)`. Establish `hev : ∀ᶠ z in nhds z₀, f z ≠ 0` using `hf.continuous.continuousAt.eventually_ne hz₀`. Establish `hg_ev : g =ᶠ[nhds z₀] 0` using `hev.mono fun z hz => by`. Establish `hz'` using `congrFun hfg z`. Simplify using `only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at hz'`.

Conclude with `hz'.resolve_left hz`. Establish `han : AnalyticOnNhd ℂ g Set.univ` using `fun z _ => hg.analyticAt z`. Establish `heq` using `han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z₀) hg_ev`. Use function extensionality and compare the values at `z`. Conclude with `heq (Set.mem_univ z)`.
-/
private theorem mul_ne_zero_entire {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) : f * g ≠ 0 := by
  intro hfg
  apply hg0
  obtain ⟨z₀, hz₀⟩ : ∃ z, f z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hf0 (funext hcon)
  have hev : ∀ᶠ z in nhds z₀, f z ≠ 0 := hf.continuous.continuousAt.eventually_ne hz₀
  have hg_ev : g =ᶠ[nhds z₀] 0 := hev.mono fun z hz => by
    have hz' := congrFun hfg z
    simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at hz'
    exact hz'.resolve_left hz
  have han : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z₀) hg_ev
  funext z
  exact heq (Set.mem_univ z)

/- English proof (translation)
Simplify using `only [fac, eval_mul]`. Use `push_cast`. Rewrite using `[add_mul, Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem fac_mul (c c' : ℂ) (t t' q : ℝ) (P P' : ℂ[X]) (s : ℂ) :
    fac (c * c') (t + t') q (P * P') s = fac c t q P s * fac c' t' q P' s := by
  simp only [fac, eval_mul]
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

/- English proof (translation)
Establish `hq0 : (q : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr (by linarith)`. Unfold `fac`. Simplify using `only [eval_comp, eval_mul, eval_C, eval_X]`. Rewrite using `[← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0, mul_assoc c (Complex.exp _), ← Complex.exp_add]`. Establish `e1 : z + -s = -(s - z)` using `by ring`.

Establish `e2 : z + (1 - s) = 1 - (s - z)` using `by ring`. Establish `e3 : -((t : ℂ) * z) + t * s = t * (s - z)` using `by ring`. Rewrite using `[e1, e2, e3]`.
-/
private theorem fac_sub (c : ℂ) (t : ℝ) {q : ℝ} (hq : 1 < q) (P : ℂ[X]) (z s : ℂ) :
    fac (c * Complex.exp (-(t * z))) t q (P.comp (C ((q : ℂ) ^ z) * X)) s = fac c t q P (s - z) := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  unfold fac
  simp only [eval_comp, eval_mul, eval_C, eval_X]
  rw [← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0, mul_assoc c (Complex.exp _), ← Complex.exp_add]
  have e1 : z + -s = -(s - z) := by ring
  have e2 : z + (1 - s) = 1 - (s - z) := by ring
  have e3 : -((t : ℂ) * z) + t * s = t * (s - z) := by ring
  rw [e1, e2, e3]

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `q`. Use `⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, 1, 1, 1, 0, 0, differentiable_const _, differentiable_const _, ?_, one_ne_zero, one_ne_zero, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Simplify using `using congrFun h 0`.

Introduce `s _`. Simplify using `[fac]`. Introduce `s _`. Simplify using `[fac]`. Introduce `L₁ L₁' L₂ L₂' β₁ β₂ q P₁ P₂ h₁ h₂`.

Take `⟨Z₁, W₁, A₁, B₁, k₁, k₁', c₁, t₁, d₁, hZ₁, hW₁, hZ₁0, hk₁, hk₁', hu₁, hl₁⟩` from `h₁`. Take `⟨Z₂, W₂, A₂, B₂, k₂, k₂', c₂, t₂, d₂, hZ₂, hW₂, hZ₂0, hk₂, hk₂', hu₂, hl₂⟩` from `h₂`. Use `⟨Z₁ * Z₂, W₁ * W₂, A₁ * A₂, B₁ * B₂, k₁ * k₂, k₁' * k₂', c₁ * c₂, t₁ + t₂, max d₁ d₂, hZ₁.mul hZ₂, hW₁.mul hW₂, mul_ne_zero_entire hZ₁ hZ₂ hZ₁0 hZ₂0, mul_ne_zero hk₁ hk₂, mul_ne_zero hk₁' hk₂', ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Take `⟨e₁, f₁⟩` from `hu₁ s (lt_of_le_of_lt (le_max_left _ _) hs)`.

Take `⟨e₂, f₂⟩` from `hu₂ s (lt_of_le_of_lt (le_max_right _ _) hs)`. Simplify using `only [Pi.mul_apply, eval_mul, e₁, e₂, f₁, f₂]`. Apply the tactic sequence `constructor <;> ring`. Introduce `s hs`. Establish `hs₁ : s.re < -d₁` using `lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))`.

Establish `hs₂ : s.re < -d₂` using `lt_of_lt_of_le hs (neg_le_neg (le_max_right _ _))`. Take `⟨e₁, f₁⟩` from `hl₁ s hs₁`. Take `⟨e₂, f₂⟩` from `hl₂ s hs₂`. Simplify using `only [Pi.mul_apply, fac_mul, e₁, e₂, f₁, f₂]`. Apply the tactic sequence `constructor <;> ring`.

Introduce `L L' L₁ L₁' β q P c h hL hL'`. Take `⟨Z, W, A, B, k, k', c₀, t, d, hZ, hW, hZ0, hk, hk', hu, hl⟩` from `h`. Use `⟨Z, W, A, B, k, k', c₀, t, max d (c + 1), hZ, hW, hZ0, hk, hk', ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Establish `h1 : d < s.re` using `lt_of_le_of_lt (le_max_left _ _) hs`.

Establish `h2 : c + 1 < s.re` using `lt_of_le_of_lt (le_max_right _ _) hs`. Take `⟨e, f⟩` from `hu s h1`. Establish `h3 : c < (s + 1).re`. Rewrite using `[Complex.add_re, Complex.one_re]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `⟨by rw [e, hL s (by linarith)], by rw [f, hL (s + 1) h3]⟩`. Introduce `s hs`. Establish `h1 : s.re < -d` using `lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))`. Establish `h2 : s.re < -(c + 1)` using `lt_of_lt_of_le hs (neg_le_neg (le_max_right _ _))`. Take `⟨e, f⟩` from `hl s h1`.

Establish `h3 : (s + 1).re < -c`. Rewrite using `[Complex.add_re, Complex.one_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨by rw [e, hL' s (by linarith)], by rw [f, hL' (s + 1) h3]⟩`. Introduce `L L' β q P z hq h`.

Take `⟨Z, W, A, B, k, k', c₀, t, d, hZ, hW, hZ0, hk, hk', hu, hl⟩` from `h`. Establish `hsh : Differentiable ℂ (fun s : ℂ => s - z)` using `differentiable_id.sub_const z`. Use `⟨fun s => Z (s - z), fun s => W (s - z), fun s => A (s - z), fun s => B (s - z), k, k', c₀ * Complex.exp (-(t * z)), t, d + |z.re|, hZ.comp hsh, hW.comp hsh, ne_zero_sub hZ0 z, hk, hk', ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Establish `h1 : d < (s - z).re`.

Rewrite using `[Complex.sub_re]`. Combine the linear relations using `[le_abs_self z.re]`. Take `⟨e, f⟩` from `hu (s - z) h1`. Use `⟨e, ?_⟩` and prove the remaining obligations. Use `show W (s - z) = k * L (s + 1 - z) * eval s (β.comp (X - C z)) * A (s - z)`.

Rewrite using `[f, eval_comp]`. Simplify using `only [eval_sub, eval_X, eval_C]`. Rewrite using `[show s - z + 1 = s + 1 - z by ring]`. Introduce `s hs`. Establish `h1 : (s - z).re < -d`.

Rewrite using `[Complex.sub_re]`. Combine the linear relations using `[neg_abs_le z.re]`. Take `⟨e, f⟩` from `hl (s - z) h1`. Prove the components needed by the constructor for the conclusion. Use `show Z (s - z) = L' (s - z) * B (s - z) * fac (c₀ * Complex.exp (-(t * z))) t q (P.comp (C ((q : ℂ) ^ z) * X)) s`.

Rewrite using `[e, fac_sub c₀ t hq P z s]`. Use `show W (s - z) = k' * L' (s + 1 - z) * B (s - z) * fac (c₀ * Complex.exp (-(t * z))) t q (P.comp (C ((q : ℂ) ^ z) * X)) (s + 1)`. Rewrite using `[f, fac_sub c₀ t hq P z (s + 1), show s - z + 1 = s + 1 - z by ring]`.
-/
theorem pairGOps : PairGOps := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    refine ⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, 1, 1, 1, 0, 0, differentiable_const _,
      differentiable_const _, ?_, one_ne_zero, one_ne_zero, ?_, ?_⟩
    · intro h
      simpa using congrFun h 0
    · intro s _
      simp [fac]
    · intro s _
      simp [fac]
  · intro L₁ L₁' L₂ L₂' β₁ β₂ q P₁ P₂ h₁ h₂
    obtain ⟨Z₁, W₁, A₁, B₁, k₁, k₁', c₁, t₁, d₁, hZ₁, hW₁, hZ₁0, hk₁, hk₁', hu₁, hl₁⟩ := h₁
    obtain ⟨Z₂, W₂, A₂, B₂, k₂, k₂', c₂, t₂, d₂, hZ₂, hW₂, hZ₂0, hk₂, hk₂', hu₂, hl₂⟩ := h₂
    refine ⟨Z₁ * Z₂, W₁ * W₂, A₁ * A₂, B₁ * B₂, k₁ * k₂, k₁' * k₂', c₁ * c₂, t₁ + t₂, max d₁ d₂,
      hZ₁.mul hZ₂, hW₁.mul hW₂, mul_ne_zero_entire hZ₁ hZ₂ hZ₁0 hZ₂0, mul_ne_zero hk₁ hk₂,
      mul_ne_zero hk₁' hk₂', ?_, ?_⟩
    · intro s hs
      obtain ⟨e₁, f₁⟩ := hu₁ s (lt_of_le_of_lt (le_max_left _ _) hs)
      obtain ⟨e₂, f₂⟩ := hu₂ s (lt_of_le_of_lt (le_max_right _ _) hs)
      simp only [Pi.mul_apply, eval_mul, e₁, e₂, f₁, f₂]
      constructor <;> ring
    · intro s hs
      have hs₁ : s.re < -d₁ := lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))
      have hs₂ : s.re < -d₂ := lt_of_lt_of_le hs (neg_le_neg (le_max_right _ _))
      obtain ⟨e₁, f₁⟩ := hl₁ s hs₁
      obtain ⟨e₂, f₂⟩ := hl₂ s hs₂
      simp only [Pi.mul_apply, fac_mul, e₁, e₂, f₁, f₂]
      constructor <;> ring
  · intro L L' L₁ L₁' β q P c h hL hL'
    obtain ⟨Z, W, A, B, k, k', c₀, t, d, hZ, hW, hZ0, hk, hk', hu, hl⟩ := h
    refine ⟨Z, W, A, B, k, k', c₀, t, max d (c + 1), hZ, hW, hZ0, hk, hk', ?_, ?_⟩
    · intro s hs
      have h1 : d < s.re := lt_of_le_of_lt (le_max_left _ _) hs
      have h2 : c + 1 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
      obtain ⟨e, f⟩ := hu s h1
      have h3 : c < (s + 1).re := by
        rw [Complex.add_re, Complex.one_re]
        linarith
      exact ⟨by rw [e, hL s (by linarith)], by rw [f, hL (s + 1) h3]⟩
    · intro s hs
      have h1 : s.re < -d := lt_of_lt_of_le hs (neg_le_neg (le_max_left _ _))
      have h2 : s.re < -(c + 1) := lt_of_lt_of_le hs (neg_le_neg (le_max_right _ _))
      obtain ⟨e, f⟩ := hl s h1
      have h3 : (s + 1).re < -c := by
        rw [Complex.add_re, Complex.one_re]
        linarith
      exact ⟨by rw [e, hL' s (by linarith)], by rw [f, hL' (s + 1) h3]⟩
  · intro L L' β q P z hq h
    obtain ⟨Z, W, A, B, k, k', c₀, t, d, hZ, hW, hZ0, hk, hk', hu, hl⟩ := h
    have hsh : Differentiable ℂ (fun s : ℂ => s - z) := differentiable_id.sub_const z
    refine ⟨fun s => Z (s - z), fun s => W (s - z), fun s => A (s - z), fun s => B (s - z), k, k',
      c₀ * Complex.exp (-(t * z)), t, d + |z.re|, hZ.comp hsh, hW.comp hsh, ne_zero_sub hZ0 z, hk,
      hk', ?_, ?_⟩
    · intro s hs
      have h1 : d < (s - z).re := by
        rw [Complex.sub_re]
        linarith [le_abs_self z.re]
      obtain ⟨e, f⟩ := hu (s - z) h1
      refine ⟨e, ?_⟩
      show W (s - z) = k * L (s + 1 - z) * eval s (β.comp (X - C z)) * A (s - z)
      rw [f, eval_comp]
      simp only [eval_sub, eval_X, eval_C]
      rw [show s - z + 1 = s + 1 - z by ring]
    · intro s hs
      have h1 : (s - z).re < -d := by
        rw [Complex.sub_re]
        linarith [neg_abs_le z.re]
      obtain ⟨e, f⟩ := hl (s - z) h1
      constructor
      · show Z (s - z) = L' (s - z) * B (s - z) *
          fac (c₀ * Complex.exp (-(t * z))) t q (P.comp (C ((q : ℂ) ^ z) * X)) s
        rw [e, fac_sub c₀ t hq P z s]
      · show W (s - z) = k' * L' (s + 1 - z) * B (s - z) *
          fac (c₀ * Complex.exp (-(t * z))) t q (P.comp (C ((q : ℂ) ^ z) * X)) (s + 1)
        rw [f, fac_sub c₀ t hq P z (s + 1), show s - z + 1 = s + 1 - z by ring]

end UpperTheory.V.Z.Gam
