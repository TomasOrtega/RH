import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AtLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private noncomputable def kA (δ : F) : Fin 4 → A F := ![1, 1, 2, -2 * rt δ]

private noncomputable def qG (δ : F) (v : V4 F) : A F := v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)

/- English proof (translation)
Establish `h2 : TR.pInf F (2 : A F) w = 2`. Rewrite using `[map_ofNat]`. Both sides reduce to the same expression. Apply the tactic sequence `fin_cases i <;> simp [kap, kA, cw, h2]`.
-/
private theorem kap_eq (δ : F) (w : InfinitePlace F) (i : Fin 4) :
    kap δ w i = ((TR.pInf F (kA δ i) w : ℝ) : ℂ) := by
  have h2 : TR.pInf F (2 : A F) w = 2 := by
    rw [map_ofNat]
    rfl
  fin_cases i <;> simp [kap, kA, cw, h2]

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> simp [qG, kA, Pi.single_apply] <;> ring`.
-/
private theorem form_step (δ : F) (v : V4 F) (i : Fin 4) (s : A F) :
    qG δ (v + Pi.single i s) = qG δ v + kA δ i * (2 * v i * s + s * s) := by
  fin_cases i <;> simp [qG, kA, Pi.single_apply] <;> ring

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single w]`. Simplify using the standard rewrite rules. Introduce `b' _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ w) h`.
-/
private theorem sum_step (w : InfinitePlace F) (K b : InfinitePlace F → ℝ) (t : ℝ) :
    ∑ w', (K * (2 * b * Pi.single w t + Pi.single w t * Pi.single w t) : InfinitePlace F → ℝ) w' =
      K w * (2 * b w * t + t * t) := by
  rw [Finset.sum_eq_single w]
  · simp
  · intro b' _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ w) h

/- English proof (translation)
Establish `hp : TR.pInf F (at1 w t) = Pi.single w t` using `(atLaws F w).2.2.1 t`. Establish `hs : (∑ w', TR.pInf F (qG δ (v + Pi.single i (at1 w t))) w' : ℝ) = (∑ w', TR.pInf F (qG δ v) w') + TR.pInf F (kA δ i) w * (2 * TR.pInf F (v i) w * t + t * t)`. Rewrite using `[form_step, ← sum_step w (TR.pInf F (kA δ i)) (TR.pInf F (v i)) t, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun w' _ => ?_` and prove the remaining obligations. Establish `h2 : TR.pInf F (2 : A F) = 2` using `by rw [map_ofNat]`.

Simplify using `only [map_add, map_mul, hp, h2, Pi.add_apply]`. Establish `hg : ∀ u : V4 F, gauss δ u = Complex.exp (-(Real.pi : ℂ) * ((∑ w', TR.pInf F (qG δ u) w' : ℝ) : ℂ))`. Introduce `u`. Unfold `gauss qG`. Both sides reduce to the same expression.

Rewrite using `[hg, hg, hs, ← Complex.exp_add, kap_eq]`. Use `congr 1`. Simplify using `only [cw]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gauss_step (δ : F) (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    gauss δ (v + Pi.single i (at1 w t)) =
      gauss δ v * Complex.exp (-((Real.pi : ℂ) * kap δ w i * (2 * cw w (v i) * t + t * t))) := by
  have hp : TR.pInf F (at1 w t) = Pi.single w t := (atLaws F w).2.2.1 t
  have hs : (∑ w', TR.pInf F (qG δ (v + Pi.single i (at1 w t))) w' : ℝ) =
      (∑ w', TR.pInf F (qG δ v) w') +
        TR.pInf F (kA δ i) w * (2 * TR.pInf F (v i) w * t + t * t) := by
    rw [form_step, ← sum_step w (TR.pInf F (kA δ i)) (TR.pInf F (v i)) t,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w' _ => ?_
    have h2 : TR.pInf F (2 : A F) = 2 := by rw [map_ofNat]
    simp only [map_add, map_mul, hp, h2, Pi.add_apply]
  have hg : ∀ u : V4 F, gauss δ u =
      Complex.exp (-(Real.pi : ℂ) * ((∑ w', TR.pInf F (qG δ u) w' : ℝ) : ℂ)) := by
    intro u
    unfold gauss qG
    rfl
  rw [hg, hg, hs, ← Complex.exp_add, kap_eq]
  congr 1
  simp only [cw]
  push_cast
  ring

/- English proof (translation)
Establish `hp : TR.pInf F (at1 w t) = Pi.single w t` using `(atLaws F w).2.2.1 t`. Simplify using `[cw, hp]`.
-/
private theorem cw_step (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    cw w ((v + Pi.single i (at1 w t) : V4 F) i) = cw w (v i) + t := by
  have hp : TR.pInf F (at1 w t) = Pi.single w t := (atLaws F w).2.2.1 t
  simp [cw, hp]

/- English proof (translation)
Use `set a : ℂ := cw w (v i) with ha`. Use `set κ : ℂ := kap δ w i with hκ`. Set `f : ℝ → ℂ` to `fun t => φ.1 (v + Pi.single i (at1 w t))`. Set `X : ℝ → ℂ` to `fun t => (Real.pi : ℂ) * κ * (2 * a * t + t * t)`. Establish `hf : ∀ t, HasDerivAt f (-2 * Real.pi * κ * (a + t) * f t) t`.

Introduce `t`. Establish `h0` using `O.d_spec w i φ (v + Pi.single i (at1 w t))`. Establish `e : (fun s : ℝ => φ.1 (v + Pi.single i (at1 w t) + Pi.single i (at1 w s))) = fun s => f (t + s)`. Use function extensionality and compare the values at `s`. Simplify using `only [f]`.

Rewrite using `[(atLaws F w).2.2.2.1 t s, Pi.single_add, add_assoc]`. Rewrite `h0` using `[e]`. Establish `h1 : HasDerivAt (fun s => f (t + s)) ((O.d w i φ).1 (v + Pi.single i (at1 w t))) (t - t)`. Simplify using `using h0`. Establish `h2` using `h1.comp_sub_const t t`.

Establish `e2 : (fun x => f (t + (x - t))) = f`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules. Rewrite `h2` using `[e2]`. Establish `key : (O.d w i φ).1 (v + Pi.single i (at1 w t)) = -2 * Real.pi * κ * (a + t) * f t`.

Rewrite using `[h w i]`. Express the relevant statement in the definitionally equal form `(-2 * Real.pi * kap δ w i) * (O.x w i φ).1 (v + Pi.single i (at1 w t)) = _`. Rewrite using `[O.x_apply, cw_step]`. Simplify using `only [f]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h2` using `[key]`. Conclude with `h2`. Establish `hX : ∀ t : ℝ, HasDerivAt X ((Real.pi : ℂ) * κ * (2 * a + 2 * t)) t`. Introduce `t`. Establish `h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t` using `(hasDerivAt_id t).ofReal_comp`.

Establish `h2` using `((h1.const_mul (2 * a)).add (h1.mul h1)).const_mul ((Real.pi : ℂ) * κ)`. Conclude with `h2.congr_deriv (by ring)`. Establish `hE : ∀ t : ℝ, HasDerivAt (fun t => f t * Complex.exp (X t)) 0 t`. Introduce `t`. Establish `h2` using `(hf t).mul (hX t).cexp`.

Conclude with `h2.congr_deriv (by ring)`. Establish `hc` using `is_const_of_deriv_eq_zero (fun t => (hE t).differentiableAt) (fun t => (hE t).deriv) t 0`. Establish `h0 : f 0 = φ.1 v`. Simplify using `only [f]`. Rewrite using `[(atLaws F w).2.2.2.2.1]`.

Simplify using the standard rewrite rules. Establish `hX0 : X 0 = 0` using `by simp [X]`. Simplify using `only [hX0, Complex.exp_zero, mul_one, h0] at hc`. Rewrite using `[gauss_step, ← hc]`. Establish `: Complex.exp (X t) * Complex.exp (-X t) = 1`.

Rewrite using `[← Complex.exp_add]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `f t * gauss δ v = f t * Complex.exp (X t) * (gauss δ v * Complex.exp (-X t))`. Take the linear combination `(-(f t * gauss δ v)) * this`.
-/
private theorem line_step (δ : F) (O : Ops F) (φ : S4 F)
    (h : ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ)
    (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    φ.1 (v + Pi.single i (at1 w t)) * gauss δ v = φ.1 v * gauss δ (v + Pi.single i (at1 w t)) := by
  set a : ℂ := cw w (v i) with ha
  set κ : ℂ := kap δ w i with hκ
  let f : ℝ → ℂ := fun t => φ.1 (v + Pi.single i (at1 w t))
  let X : ℝ → ℂ := fun t => (Real.pi : ℂ) * κ * (2 * a * t + t * t)
  have hf : ∀ t, HasDerivAt f (-2 * Real.pi * κ * (a + t) * f t) t := by
    intro t
    have h0 := O.d_spec w i φ (v + Pi.single i (at1 w t))
    have e : (fun s : ℝ => φ.1 (v + Pi.single i (at1 w t) + Pi.single i (at1 w s))) = fun s => f (t + s) := by
      funext s
      simp only [f]
      rw [(atLaws F w).2.2.2.1 t s, Pi.single_add, add_assoc]
    rw [e] at h0
    have h1 : HasDerivAt (fun s => f (t + s)) ((O.d w i φ).1 (v + Pi.single i (at1 w t))) (t - t) := by
      simpa using h0
    have h2 := h1.comp_sub_const t t
    have e2 : (fun x => f (t + (x - t))) = f := by
      funext x
      simp
    rw [e2] at h2
    have key : (O.d w i φ).1 (v + Pi.single i (at1 w t)) = -2 * Real.pi * κ * (a + t) * f t := by
      rw [h w i]
      change (-2 * Real.pi * kap δ w i) * (O.x w i φ).1 (v + Pi.single i (at1 w t)) = _
      rw [O.x_apply, cw_step]
      simp only [f]
      ring
    rw [key] at h2
    exact h2
  have hX : ∀ t : ℝ, HasDerivAt X ((Real.pi : ℂ) * κ * (2 * a + 2 * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h2 := ((h1.const_mul (2 * a)).add (h1.mul h1)).const_mul ((Real.pi : ℂ) * κ)
    exact h2.congr_deriv (by ring)
  have hE : ∀ t : ℝ, HasDerivAt (fun t => f t * Complex.exp (X t)) 0 t := by
    intro t
    have h2 := (hf t).mul (hX t).cexp
    exact h2.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hE t).differentiableAt) (fun t => (hE t).deriv) t 0
  have h0 : f 0 = φ.1 v := by
    simp only [f]
    rw [(atLaws F w).2.2.2.2.1]
    simp
  have hX0 : X 0 = 0 := by simp [X]
  simp only [hX0, Complex.exp_zero, mul_one, h0] at hc
  rw [gauss_step, ← hc]
  have : Complex.exp (X t) * Complex.exp (-X t) = 1 := by
    rw [← Complex.exp_add]
    simp
  change f t * gauss δ v = f t * Complex.exp (X t) * (gauss δ v * Complex.exp (-X t))
  linear_combination (-(f t * gauss δ v)) * this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert p s hp ih`. Rewrite using `[Finset.sum_insert hp, add_comm (Pi.single p.1 _), ← add_assoc]`. Establish `hs` using `line_step δ O φ h (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) p.1 p.2 (c p)`.

Establish `hg : gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) ≠ 0` using `Complex.exp_ne_zero _`. Use `mul_right_cancel₀ hg ?_` and prove the remaining obligations. Take the linear combination `(gauss δ v) * hs + (gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p)) + Pi.single p.1 (at1 p.2 (c p)))) * ih`.
-/
private theorem chain_step (δ : F) (O : Ops F) (φ : S4 F)
    (h : ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ)
    (v : V4 F) (c : Fin 4 × InfinitePlace F → ℝ) (s : Finset (Fin 4 × InfinitePlace F)) :
    φ.1 (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) * gauss δ v =
      φ.1 v * gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, add_comm (Pi.single p.1 _), ← add_assoc]
    have hs := line_step δ O φ h (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) p.1 p.2 (c p)
    have hg : gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) ≠ 0 := Complex.exp_ne_zero _
    refine mul_right_cancel₀ hg ?_
    linear_combination (gauss δ v) * hs +
      (gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p)) + Pi.single p.1 (at1 p.2 (c p)))) * ih

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F _ _ _ δ O φ h v v' e`. Take `⟨w₀⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Set `c : Fin 4 × InfinitePlace F → ℝ` to `fun p => TR.pInf F (v' p.1 - v p.1) p.2`. Establish `hv : v' = v + ∑ p, Pi.single p.1 (at1 p.2 (c p))`. Use function extensionality and compare the values at `j`.

Establish `h0 : (v' j - v j).2 = 0`. Use `congrFun e j` as an intermediate fact. Express the relevant statement in the definitionally equal form `(v j).2 = (v' j).2 at this`. Express the relevant statement in the definitionally equal form `(v' j).2 - (v j).2 = 0`. Rewrite using `[this, sub_self]`.

Establish `h1` using `(atLaws F w₀).2.2.2.2.2.2.1 (v' j - v j) h0`. Establish `h2 : (∑ p : Fin 4 × InfinitePlace F, (Pi.single p.1 (at1 p.2 (c p)) : V4 F)) j = v' j - v j`. Rewrite using `[h1, Fintype.sum_prod_type, Finset.sum_apply, Finset.sum_eq_single j]`. Rewrite using `[Finset.sum_apply]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Simplify using `[c, ← h1]`. Introduce `b _ hb`. Rewrite using `[Finset.sum_apply]`. Conclude with `Finset.sum_eq_zero fun w _ => Pi.single_eq_of_ne hb.symm _`. Introduce `hj`.

Conclude with `absurd (Finset.mem_univ j) hj`. Rewrite using `[Pi.add_apply, h2]`. Normalize the expressions using the abelian group laws. Use `chain_step δ O φ h v c Finset.univ` as an intermediate fact. Rewrite `this` using `[← hv]`.

Conclude with `this.symm ▸ (by ring)`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.annVac :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F) (φ : S4 F), (∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ) → φ ∈ Vac δ := by
  intro F _ _ _ δ O φ h v v' e
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  let c : Fin 4 × InfinitePlace F → ℝ := fun p => TR.pInf F (v' p.1 - v p.1) p.2
  have hv : v' = v + ∑ p, Pi.single p.1 (at1 p.2 (c p)) := by
    funext j
    have h0 : (v' j - v j).2 = 0 := by
      have := congrFun e j
      change (v j).2 = (v' j).2 at this
      change (v' j).2 - (v j).2 = 0
      rw [this, sub_self]
    have h1 := (atLaws F w₀).2.2.2.2.2.2.1 (v' j - v j) h0
    have h2 : (∑ p : Fin 4 × InfinitePlace F, (Pi.single p.1 (at1 p.2 (c p)) : V4 F)) j = v' j - v j := by
      rw [h1, Fintype.sum_prod_type, Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp [c, ← h1]
      · intro b _ hb
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun w _ => Pi.single_eq_of_ne hb.symm _
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [Pi.add_apply, h2]
    abel
  have := chain_step δ O φ h v c Finset.univ
  rw [← hv] at this
  exact this.symm ▸ (by ring)
