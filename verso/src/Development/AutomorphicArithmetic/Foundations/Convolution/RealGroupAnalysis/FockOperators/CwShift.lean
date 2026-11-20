import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.AtLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

/- English proof (translation)
Establish `hp` using `((atLaws F w).2.2.1) t`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `h1 : (v + Pi.single i (at1 w t) : V4 F) i = v i + at1 w t` using `by simp`. Rewrite using `[h1]`.

Unfold `cw`. Rewrite using `[map_add, Pi.add_apply, hp]`. Distinguish the cases in `hw : w = w'`. Substitute `hw` using the available equality. Simplify using the standard rewrite rules.

Establish `: w' ≠ w` using `fun h => hw h.symm`. Simplify using `[hw, this]`. Establish `h1 : (v + Pi.single i (at1 w t) : V4 F) j = v j`. Simplify using `[Pi.single_apply, Ne.symm hij]`. Rewrite using `[h1]`.

Simplify using `[hij]`.
-/
private lemma cw_shift {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (w w' : InfinitePlace F) (i j : Fin 4) (v : V4 F) (t : ℝ) :
    cw w' ((v + Pi.single i (at1 w t) : V4 F) j) = cw w' (v j) + if w = w' ∧ i = j then (t : ℂ) else 0 := by
  have hp := ((atLaws F w).2.2.1) t
  by_cases hij : i = j
  · subst hij
    have h1 : (v + Pi.single i (at1 w t) : V4 F) i = v i + at1 w t := by simp
    rw [h1]
    unfold cw
    rw [map_add, Pi.add_apply, hp]
    by_cases hw : w = w'
    · subst hw; simp
    · have : w' ≠ w := fun h => hw h.symm
      simp [hw, this]
  · have h1 : (v + Pi.single i (at1 w t) : V4 F) j = v j := by
      simp [Pi.single_apply, Ne.symm hij]
    rw [h1]
    simp [hij]

/- English proof (translation)
Introduce `F _ _ _ O w w' i j`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(O.x w i (O.x w' j φ)).1 v = (O.x w' j (O.x w i φ)).1 v`. Rewrite using `[O.x_apply, O.x_apply, O.x_apply, O.x_apply, mul_left_comm]`.

Use `LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)` and prove the remaining obligations. Establish `h0 : at1 w 0 = (0 : A F)` using `(atLaws F w).2.2.2.2.1`. Establish `hv : (v + Pi.single i (at1 w 0) : V4 F) = v` using `by rw [h0]; simp`. Use `set C : Prop := w = w' ∧ i = j with hC`. Establish `hg` using `O.d_spec w i φ v`.

Establish `hh : HasDerivAt (fun t : ℝ => cw w' (v j) + if C then (t : ℂ) else 0) (if C then 1 else 0) 0`. Distinguish the cases in `c : C`. Simplify using `only [if_pos c]`. Conclude with `(Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add _ |>.congr_deriv (by simp)`. Simplify using `only [if_neg c]`.

Conclude with `hasDerivAt_const _ _`. Establish `hm` using `hh.mul hg`. Establish `hd` using `O.d_spec w i (O.x w' j φ) v`. Establish `he : (fun t : ℝ => (O.x w' j φ).1 (v + Pi.single i (at1 w t) : V4 F)) = (fun t : ℝ => cw w' (v j) + if C then (t : ℂ) else 0) * fun t : ℝ => φ.1 (v + Pi.single i (at1 w t) : V4 F)`. Use function extensionality and compare the values at `t`.

Rewrite using `[O.x_apply, cw_shift]`. Both sides reduce to the same expression. Rewrite `hd` using `[he]`. Establish `hu` using `hd.unique hm`. Express the relevant statement in the definitionally equal form `(O.d w i (O.x w' j φ)).1 v = (O.x w' j (O.d w i φ)).1 v + ((if C then (1 : Module.End ℂ (S4 F)) else 0) φ).1 v`.

Rewrite using `[hu, O.x_apply, hv]`. Distinguish the cases in `c : C`. Simplify using `[c]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[c]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Fo.weyl :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F) w w' i j, O.x w i * O.x w' j = O.x w' j * O.x w i ∧
    O.d w i * O.x w' j = O.x w' j * O.d w i + if w = w' ∧ i = j then 1 else 0 := by
  intro F _ _ _ O w w' i j
  refine ⟨?_, ?_⟩
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    change (O.x w i (O.x w' j φ)).1 v = (O.x w' j (O.x w i φ)).1 v
    rw [O.x_apply, O.x_apply, O.x_apply, O.x_apply, mul_left_comm]
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    have h0 : at1 w 0 = (0 : A F) := (atLaws F w).2.2.2.2.1
    have hv : (v + Pi.single i (at1 w 0) : V4 F) = v := by rw [h0]; simp
    set C : Prop := w = w' ∧ i = j with hC
    have hg := O.d_spec w i φ v
    have hh : HasDerivAt (fun t : ℝ => cw w' (v j) + if C then (t : ℂ) else 0) (if C then 1 else 0) 0 := by
      by_cases c : C
      · simp only [if_pos c]
        exact (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add _ |>.congr_deriv (by simp)
      · simp only [if_neg c]
        exact hasDerivAt_const _ _
    have hm := hh.mul hg
    have hd := O.d_spec w i (O.x w' j φ) v
    have he : (fun t : ℝ => (O.x w' j φ).1 (v + Pi.single i (at1 w t) : V4 F)) =
        (fun t : ℝ => cw w' (v j) + if C then (t : ℂ) else 0) * fun t : ℝ => φ.1 (v + Pi.single i (at1 w t) : V4 F) := by
      funext t
      rw [O.x_apply, cw_shift]
      rfl
    rw [he] at hd
    have hu := hd.unique hm
    change (O.d w i (O.x w' j φ)).1 v = (O.x w' j (O.d w i φ)).1 v + ((if C then (1 : Module.End ℂ (S4 F)) else 0) φ).1 v
    rw [hu, O.x_apply, hv]
    by_cases c : C
    · simp [c]; ring
    · simp [c]
