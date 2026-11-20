import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(TR.infEq F).symm (TR.infEq F (Pi.single w t)) = _`. Conclude with `RingEquiv.symm_apply_apply _ _`.
-/
private lemma infiniteProjection_placeEmbed (w : InfinitePlace F) (t : ℝ) : TR.pInf F (Fo.at1 w t) = Pi.single w t := by
  change (TR.infEq F).symm (TR.infEq F (Pi.single w t)) = _
  exact RingEquiv.symm_apply_apply _ _

/- English proof (translation)
Simplify using `[Fo.at1]`.
-/
private lemma placeEmbedReal_zero (w : InfinitePlace F) : Fo.at1 w 0 = 0 := by
  simp [Fo.at1]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma placeEmbedReal_finitePart (w : InfinitePlace F) (t : ℝ) : (Fo.at1 w t).2 = 0 := rfl

/- English proof (translation)
Simplify using `[placeEmbedReal_zero]`.
-/
private lemma shift_zero (w : InfinitePlace F) (i : Fin 4) (v : V4 F) :
    v + Pi.single i (Fo.at1 w 0) = v := by
  simp [placeEmbedReal_zero]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[finPartPi, placeEmbedReal_finitePart]`. Simplify using `[finPartPi, Pi.single_eq_of_ne h]`.
-/
private lemma finPart_shift (w : InfinitePlace F) (i : Fin 4) (v : V4 F) (t : ℝ) :
    finPartPi (v + Pi.single i (Fo.at1 w t)) = finPartPi v := by
  funext j
  by_cases h : j = i
  · subst h
    simp [finPartPi, placeEmbedReal_finitePart]
  · simp [finPartPi, Pi.single_eq_of_ne h]

/- English proof (translation)
Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Distinguish the cases in `h' : w' = w`. Substitute `h'` using the available equality. Simplify using `[map_add, infiniteProjection_placeEmbed]`.

Simplify using `[map_add, infiniteProjection_placeEmbed, h', Pi.single_eq_of_ne h']`. Simplify using `[h, Pi.single_eq_of_ne h]`.
-/
private lemma coord_shift (w w' : InfinitePlace F) (i j : Fin 4) (v : V4 F) (t : ℝ) :
    ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ) =
      ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ) := by
  by_cases h : j = i
  · subst h
    by_cases h' : w' = w
    · subst h'
      simp [map_add, infiniteProjection_placeEmbed]
    · simp [map_add, infiniteProjection_placeEmbed, h', Pi.single_eq_of_ne h']
  · simp [h, Pi.single_eq_of_ne h]

/- English proof (translation)
Establish `h` using `((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).const_add a`. Simplify using `using h`.
-/
private lemma lin_der (a c : ℂ) : HasDerivAt (fun t : ℝ => a + c * (t : ℂ)) c 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).const_add a
  simpa using h

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨j, w, rfl⟩`.
-/
private lemma coord_mem (j : Fin 4) (w : InfinitePlace F) :
    (fun v : V4 F => ((TR.pInf F (v j) w : ℝ) : ℂ)) ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F) :=
  Algebra.subset_adjoin ⟨j, w, rfl⟩

/- English proof (translation)
Unfold `UpperTheory.ConvolutionTheory.R2.polyFn at hp`. Proceed by induction on `hp using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨j, w', rfl⟩` from `hx`. Use `⟨algebraMap ℂ _ (if j = i ∧ w' = w then 1 else 0), Subalgebra.algebraMap_mem _ _, fun v => ?_⟩` and prove the remaining obligations.

Establish `e : (fun t : ℝ => ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ)) = fun t : ℝ => ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ)`. Use function extensionality and compare the values at `fun t => coord_shift w w' i j v t`. Rewrite using `[e]`. Conclude with `lin_der _ _`. Consider the case `algebraMap r`.

Conclude with `⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨x', hxm, hx⟩` from `hx`. Take `⟨y', hym, hy⟩` from `hy`. Conclude with `⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩`.

Consider the case `mul x y hxa hya hx hy`. Take `⟨x', hxm, hx⟩` from `hx`. Take `⟨y', hym, hy⟩` from `hy`. Use `⟨x' * y + x * y', add_mem (mul_mem hxm hya) (mul_mem hxa hym), fun v => ?_⟩` and prove the remaining obligations. Establish `h` using `(hx v).mul (hy v)`.

Simplify using `only [shift_zero] at h`. Conclude with `h`.
-/
private lemma poly_der (w : InfinitePlace F) (i : Fin 4) {p : V4 F → ℂ}
    (hp : p ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F)) :
    ∃ p' ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∀ v,
      HasDerivAt (fun t : ℝ => p (v + Pi.single i (Fo.at1 w t))) (p' v) 0 := by
  unfold UpperTheory.ConvolutionTheory.R2.polyFn at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, w', rfl⟩ := hx
    refine ⟨algebraMap ℂ _ (if j = i ∧ w' = w then 1 else 0), Subalgebra.algebraMap_mem _ _, fun v => ?_⟩
    have e : (fun t : ℝ => ((TR.pInf F ((v + Pi.single i (Fo.at1 w t) : V4 F) j) w' : ℝ) : ℂ)) =
        fun t : ℝ => ((TR.pInf F (v j) w' : ℝ) : ℂ) + (if j = i ∧ w' = w then 1 else 0) * (t : ℂ) :=
      funext fun t => coord_shift w w' i j v t
    rw [e]
    exact lin_der _ _
  | algebraMap r =>
    exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    exact ⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩
  | mul x y hxa hya hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    refine ⟨x' * y + x * y', add_mem (mul_mem hxm hya) (mul_mem hxa hym), fun v => ?_⟩
    have h := (hx v).mul (hy v)
    simp only [shift_zero] at h
    exact h

private noncomputable def Qf (δ : F) (v : V4 F) : ℂ :=
  ((∑ w, TR.pInf F (v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)) w : ℝ) : ℂ)

/- English proof (translation)
Establish `e : Qf δ = ∑ w, ((fun v : V4 F => ((TR.pInf F (v 0) w : ℝ) : ℂ)) ^ 2 + (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ^ 2 + algebraMap ℂ (V4 F → ℂ) 2 * ((fun v : V4 F => ((TR.pInf F (v 2) w : ℝ) : ℂ)) ^ 2 - algebraMap ℂ (V4 F → ℂ) ((TR.pInf F (rt δ) w : ℝ) : ℂ) * (fun v : V4 F = …`. Use function extensionality and compare the values at `v`. Establish `h2 : ∀ x, TR.pInf F (2 : A F) x = 2` using `fun x => by`. Rewrite using `[map_ofNat]`. Both sides reduce to the same expression.

Simplify using `[Qf, Finset.sum_apply, map_add, map_mul, map_sub, map_pow, h2]`. Rewrite using `[e]`. Use `sum_mem fun w _ => ?_` and prove the remaining obligations. Conclude with `add_mem (add_mem (pow_mem (coord_mem 0 w) 2) (pow_mem (coord_mem 1 w) 2)) (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (pow_mem (coord_mem 2 w) 2) (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (coord_mem 3 w) 2))))`.
-/
private lemma Qf_mem (δ : F) : Qf δ ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F) := by
  have e : Qf δ = ∑ w, ((fun v : V4 F => ((TR.pInf F (v 0) w : ℝ) : ℂ)) ^ 2 +
      (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ^ 2 +
      algebraMap ℂ (V4 F → ℂ) 2 * ((fun v : V4 F => ((TR.pInf F (v 2) w : ℝ) : ℂ)) ^ 2 -
        algebraMap ℂ (V4 F → ℂ) ((TR.pInf F (rt δ) w : ℝ) : ℂ) *
          (fun v : V4 F => ((TR.pInf F (v 3) w : ℝ) : ℂ)) ^ 2)) := by
    funext v
    have h2 : ∀ x, TR.pInf F (2 : A F) x = 2 := fun x => by
      rw [map_ofNat]; rfl
    simp [Qf, Finset.sum_apply, map_add, map_mul, map_sub, map_pow, h2]
  rw [e]
  refine sum_mem fun w _ => ?_
  exact add_mem (add_mem (pow_mem (coord_mem 0 w) 2) (pow_mem (coord_mem 1 w) 2))
    (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (pow_mem (coord_mem 2 w) 2)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem (coord_mem 3 w) 2))))

/- English proof (translation)
Take `⟨q, hq, hd⟩` from `poly_der w i (Qf_mem δ)`. Use `⟨algebraMap ℂ _ (-(Real.pi : ℂ)) * q, mul_mem (Subalgebra.algebraMap_mem _ _) hq, fun v => ?_⟩` and prove the remaining obligations. Establish `h` using `((hd v).const_mul (-(Real.pi : ℂ))).cexp`. Simplify using `only [shift_zero] at h`. Conclude with `h`.
-/
private lemma gauss_der (δ : F) (w : InfinitePlace F) (i : Fin 4) :
    ∃ q ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∀ v, HasDerivAt
      (fun t : ℝ => UpperTheory.ConvolutionTheory.R2.gauss δ (v + Pi.single i (Fo.at1 w t)))
      (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v) 0 := by
  obtain ⟨q, hq, hd⟩ := poly_der w i (Qf_mem δ)
  refine ⟨algebraMap ℂ _ (-(Real.pi : ℂ)) * q, mul_mem (Subalgebra.algebraMap_mem _ _) hq, fun v => ?_⟩
  have h := ((hd v).const_mul (-(Real.pi : ℂ))).cexp
  simp only [shift_zero] at h
  exact h

private def Gen (δ : F) : Set (V4 F → ℂ) :=
  {φ : V4 F → ℂ | ∃ p ∈ UpperTheory.ConvolutionTheory.R2.polyFn (F := F), ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4),
    φ = fun v => p v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v)}

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨p, hp, g, hg, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨(fun v : V4 F => ((TR.pInf F (v i) w : ℝ) : ℂ)) * p, mul_mem (coord_mem i w) hp, g, hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `v`.

Simplify using `[Fo.cw, mul_assoc]`. Consider the case `zero`. Establish `: (fun v : V4 F => Fo.cw w (v i) * (0 : V4 F → ℂ) v) = 0`. Use function extensionality and compare the values at `v`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: (fun v : V4 F => Fo.cw w (v i) * (x + y) v) = (fun v => Fo.cw w (v i) * x v) + fun v => Fo.cw w (v i) * y v`. Use function extensionality and compare the values at `v`.

Simplify using `[mul_add]`. Rewrite using `[this]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx`. Establish `: (fun v : V4 F => Fo.cw w (v i) * (c • x) v) = c • fun v => Fo.cw w (v i) * x v`.

Use function extensionality and compare the values at `v`. Simplify using `[mul_left_comm]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
private lemma cw_coord_mul_mem_span_gen_of_mem (δ : F) (w : InfinitePlace F) (i : Fin 4) {f : V4 F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Gen δ)) :
    (fun v => Fo.cw w (v i) * f v) ∈ Submodule.span ℂ (Gen δ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨(fun v : V4 F => ((TR.pInf F (v i) w : ℝ) : ℂ)) * p,
      mul_mem (coord_mem i w) hp, g, hg, ?_⟩
    funext v
    simp [Fo.cw, mul_assoc]
  | zero =>
    have : (fun v : V4 F => Fo.cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
      funext v; simp
    rw [this]; exact zero_mem _
  | add x y _ _ hx hy =>
    have : (fun v : V4 F => Fo.cw w (v i) * (x + y) v) =
        (fun v => Fo.cw w (v i) * x v) + fun v => Fo.cw w (v i) * y v := by
      funext v; simp [mul_add]
    rw [this]; exact add_mem hx hy
  | smul c x _ hx =>
    have : (fun v : V4 F => Fo.cw w (v i) * (c • x) v) = c • fun v => Fo.cw w (v i) * x v := by
      funext v; simp [mul_left_comm]
    rw [this]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨p, hp, g, hg, rfl⟩` from `hx`. Take `⟨p', hp', hdp⟩` from `poly_der w i hp`. Take `⟨q, hq, hdq⟩` from `gauss_der δ w i`.

Use `⟨fun v => (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v), Submodule.subset_span ⟨p' + p * q, add_mem hp' (mul_mem hp hq), g, hg, rfl⟩, fun v => ?_⟩` and prove the remaining obligations. Establish `h` using `((hdp v).mul (hdq v)).mul_const (g (finPartPi v))`. Simplify using `only [shift_zero] at h`. Simplify using `only [finPart_shift]`. Establish `e : (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v) = (p' v * UpperTheory.ConvolutionTheory.R2.gauss δ v + p v * (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v)) * g (finPartPi v)`.

Simplify using `only [Pi.add_apply, Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h`. Consider the case `zero => exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨x', hxm, hx⟩` from `hx`. Take `⟨y', hym, hy⟩` from `hy`. Conclude with `⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩`. Consider the case `smul c x _ hx`.

Take `⟨x', hxm, hx⟩` from `hx`. Conclude with `⟨c • x', Submodule.smul_mem _ _ hxm, fun v => (hx v).const_mul c⟩`.
-/
private lemma span_d (δ : F) (w : InfinitePlace F) (i : Fin 4) {f : V4 F → ℂ}
    (hf : f ∈ Submodule.span ℂ (Gen δ)) :
    ∃ f' ∈ Submodule.span ℂ (Gen δ), ∀ v,
      HasDerivAt (fun t : ℝ => f (v + Pi.single i (Fo.at1 w t))) (f' v) 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, g, hg, rfl⟩ := hx
    obtain ⟨p', hp', hdp⟩ := poly_der w i hp
    obtain ⟨q, hq, hdq⟩ := gauss_der δ w i
    refine ⟨fun v => (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v),
      Submodule.subset_span ⟨p' + p * q, add_mem hp' (mul_mem hp hq), g, hg, rfl⟩, fun v => ?_⟩
    have h := ((hdp v).mul (hdq v)).mul_const (g (finPartPi v))
    simp only [shift_zero] at h
    simp only [finPart_shift]
    have e : (p' + p * q) v * UpperTheory.ConvolutionTheory.R2.gauss δ v * g (finPartPi v) =
        (p' v * UpperTheory.ConvolutionTheory.R2.gauss δ v + p v * (UpperTheory.ConvolutionTheory.R2.gauss δ v * q v)) * g (finPartPi v) := by
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    rw [e]
    exact h
  | zero => exact ⟨0, zero_mem _, fun v => hasDerivAt_const _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hxm, hx⟩ := hx
    obtain ⟨y', hym, hy⟩ := hy
    exact ⟨x' + y', add_mem hxm hym, fun v => (hx v).add (hy v)⟩
  | smul c x _ hx =>
    obtain ⟨x', hxm, hx⟩ := hx
    exact ⟨c • x', Submodule.smul_mem _ _ hxm, fun v => (hx v).const_mul c⟩

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D O w i φ hφ`. Establish `hs : φ.1 ∈ Submodule.span ℂ (Gen D.δ)` using `hφ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : (O.x w i φ).1 = fun v => Fo.cw w (v i) * φ.1 v` using `funext fun v => O.x_apply w i φ v`. Express the relevant statement in the definitionally equal form `(O.x w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)`.

Rewrite using `[e]`. Conclude with `cw_coord_mul_mem_span_gen_of_mem D.δ w i hs`. Take `⟨f', hf', hd⟩` from `span_d D.δ w i hs`. Establish `e : (O.d w i φ).1 = f'` using `funext fun v => (O.d_spec w i φ v).unique (hd v)`. Express the relevant statement in the definitionally equal form `(O.d w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)`.

Rewrite using `[e]`. Conclude with `hf'`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.opsFock :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F), OpsFock D O := by
  intro F E _ _ _ _ _ _ _ D O w i φ hφ
  have hs : φ.1 ∈ Submodule.span ℂ (Gen D.δ) := hφ
  refine ⟨?_, ?_⟩
  · have e : (O.x w i φ).1 = fun v => Fo.cw w (v i) * φ.1 v := funext fun v => O.x_apply w i φ v
    change (O.x w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)
    rw [e]
    exact cw_coord_mul_mem_span_gen_of_mem D.δ w i hs
  · obtain ⟨f', hf', hd⟩ := span_d D.δ w i hs
    have e : (O.d w i φ).1 = f' := funext fun v => (O.d_spec w i φ v).unique (hd v)
    change (O.d w i φ).1 ∈ Submodule.span ℂ (Gen D.δ)
    rw [e]
    exact hf'
