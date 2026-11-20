import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.PjFdegAllPos

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

section

variable (X : CData) {n₀ : ℕ} {A : ℝ} (hX : X.HypB n₀ A)

include hX

/- English proof (translation)
The claim follows from `(hX.2.1.1 v).2.2.1`.
-/
theorem pj_tr_U (v : InfinitePlace X.I.F) : IsURepOn (UJset (X.I.ε v)) (X.σ v) := (hX.2.1.1 v).2.2.1

/- English proof (translation)
The claim follows from `ContinuousLinearMap.ext_on hX.2.1.2.2.1.2.2 (by rintro _ ⟨x, rfl⟩; exact h x)`.
-/
theorem pj_tr_ext {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] (S T : X.Hs →L[ℂ] M)
    (h : ∀ x, S (X.tens x) = T (X.tens x)) : S = T :=
  ContinuousLinearMap.ext_on hX.2.1.2.2.1.2.2 (by rintro _ ⟨x, rfl⟩; exact h x)

/- English proof (translation)
Use `hX.2.1.2.2.1.2.2.eq_zero_of_inner_right ℂ fun u hu => ?_` and prove the remaining obligations. Establish `hle : Submodule.span ℂ (Set.range X.tens) ≤ (Submodule.span ℂ {z})ᗮ`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h y)`.

Conclude with `Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu)`.
-/
theorem pj_tr_zero (z : X.Hs) (h : ∀ y, ⟪X.tens y, z⟫_ℂ = 0) : z = 0 := by
  refine hX.2.1.2.2.1.2.2.eq_zero_of_inner_right ℂ fun u hu => ?_
  have hle : Submodule.span ℂ (Set.range X.tens) ≤ (Submodule.span ℂ {z})ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h y)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hu)

/- English proof (translation)
Use `pj_tr_ext X hX _ _ fun x => ?_` and prove the remaining obligations. Establish `hT` using `hX.2.1.2.2.1.2.1`. Rewrite using `[ContinuousLinearMap.comp_apply, hT, hT, hT]`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Conclude with `rep_mul_apply' (homOf (X.σ v) (pj_tr_U X hX v)) (g v) (h v) (x v)`.
-/
theorem pj_tr_mul (g h : X.I.Ginf) : X.σs (g * h) = X.σs g ∘L X.σs h := by
  refine pj_tr_ext X hX _ _ fun x => ?_
  have hT := hX.2.1.2.2.1.2.1
  rw [ContinuousLinearMap.comp_apply, hT, hT, hT]
  congr 1
  funext v
  exact rep_mul_apply' (homOf (X.σ v) (pj_tr_U X hX v)) (g v) (h v) (x v)

/- English proof (translation)
Use `pj_tr_ext X hX _ _ fun x => ?_` and prove the remaining obligations. Rewrite using `[hX.2.1.2.2.1.2.1]`. Use `show X.tens _ = X.tens x`. Use `congr 1`. Use function extensionality and compare the values at `v`.

Conclude with `rep_one_apply' (homOf (X.σ v) (pj_tr_U X hX v)) (x v)`.
-/
theorem pj_tr_one : X.σs 1 = 1 := by
  refine pj_tr_ext X hX _ _ fun x => ?_
  rw [hX.2.1.2.2.1.2.1]
  show X.tens _ = X.tens x
  congr 1
  funext v
  exact rep_one_apply' (homOf (X.σ v) (pj_tr_U X hX v)) (x v)

/- English proof (translation)
Establish `hT` using `hX.2.1.2.2.1`. Rewrite using `[hT.2.1, hT.2.1, hT.1, hT.1]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Conclude with `unitary_rep_inner_map (homOf (X.σ v) (pj_tr_U X hX v)) (homOf_norm (X.σ v) (pj_tr_U X hX v)) (g v) (x v) (y v)`.
-/
theorem pj_tr_inner_pure (g : X.I.Ginf) (x y : ∀ v, X.H v) :
    ⟪X.σs g (X.tens x), X.σs g (X.tens y)⟫_ℂ = ⟪X.tens x, X.tens y⟫_ℂ := by
  have hT := hX.2.1.2.2.1
  rw [hT.2.1, hT.2.1, hT.1, hT.1]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact unitary_rep_inner_map (homOf (X.σ v) (pj_tr_U X hX v)) (homOf_norm (X.σ v) (pj_tr_U X hX v)) (g v) (x v) (y v)

/- English proof (translation)
Use `pj_tr_ext X hX _ _ fun x => ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `pj_tr_zero X hX _ fun y => ?_` and prove the remaining obligations. Rewrite using `[inner_sub_right, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, pj_tr_inner_pure X hX, one_apply_eq_self, sub_self]`.
-/
theorem pj_tr_adj (g : X.I.Ginf) : ContinuousLinearMap.adjoint (X.σs g) ∘L X.σs g = 1 := by
  refine pj_tr_ext X hX _ _ fun x => ?_
  rw [← sub_eq_zero]
  refine pj_tr_zero X hX _ fun y => ?_
  rw [inner_sub_right, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    pj_tr_inner_pure X hX, one_apply_eq_self, sub_self]

/- English proof (translation)
Establish `h : ⟪X.σs g x, X.σs g x⟫_ℂ = ⟪x, x⟫_ℂ`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_right]`. Use `congrArg (fun T : X.Hs →L[ℂ] X.Hs => T x) (pj_tr_adj X hX g)` as an intermediate fact. Simplify using `only [ContinuousLinearMap.comp_apply, one_apply_eq_self] at this`. Rewrite using `[this]`.

Establish `h2 : ‖X.σs g x‖ ^ 2 = ‖x‖ ^ 2`. Rewrite using `[← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2`.
-/
theorem pj_tr_norm (g : X.I.Ginf) (x : X.Hs) : ‖X.σs g x‖ = ‖x‖ := by
  have h : ⟪X.σs g x, X.σs g x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have := congrArg (fun T : X.Hs →L[ℂ] X.Hs => T x) (pj_tr_adj X hX g)
    simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self] at this
    rw [this]
  have h2 : ‖X.σs g x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

/- English proof (translation)
Establish `hT` using `hX.2.1.2.2.1`. Use `set a : X.I.Ginf → ∀ v, X.H v := fun g v => X.σ v (uMat (g v)) (x v) with ha`. Establish `hac : ∀ v, Continuous fun g : X.I.Ginf => a g v` using `fun v => (homOf_cont (X.σ v) (pj_tr_U X hX v) (x v)).comp (continuous_apply v)`. Establish `hfun : (fun g => X.σs g (X.tens x)) = fun g => X.tens (a g)` using `funext fun g => hT.2.1 g x`. Rewrite using `[hfun, continuous_iff_continuousAt]`.

Introduce `g0`. Use `set F : X.I.Ginf → ℂ := fun g => (∏ v, ⟪a g v, a g v⟫_ℂ) - (∏ v, ⟪a g v, a g0 v⟫_ℂ) - (∏ v, ⟪a g0 v, a g v⟫_ℂ) + ∏ v, ⟪a g0 v, a g0 v⟫_ℂ with hF`. Establish `hFc : Continuous F`. Use `((Continuous.sub ?_ ?_).sub ?_).add continuous_const` and prove the remaining obligations. Conclude with `continuous_finsetProd _ fun v _ => (hac v).inner (hac v)`.

Conclude with `continuous_finsetProd _ fun v _ => (hac v).inner continuous_const`. Conclude with `continuous_finsetProd _ fun v _ => continuous_const.inner (hac v)`. Establish `hN : ∀ g, ‖X.tens (a g) - X.tens (a g0)‖ = Real.sqrt (RCLike.re (F g))`. Introduce `g`. Rewrite using `[← Real.sqrt_sq (norm_nonneg (X.tens (a g) - X.tens (a g0))), ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sub_left, inner_sub_right, inner_sub_right, hT.1, hT.1, hT.1, hT.1]`.

Use `congr 2`. Simplify using `only [hF]`. Expand and normalize the polynomial expressions, which then agree. Establish `hF0 : F g0 = 0` using `by simp only [hF]; ring`. Rewrite using `[ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]`.

Simplify using `only [hN]`. Establish `hc : Continuous fun g => Real.sqrt (RCLike.re (F g))` using `Real.continuous_sqrt.comp (RCLike.continuous_re.comp hFc)`. Use `hc.tendsto g0` as an intermediate fact. Simplify `this` using `[hF0]`.
-/
theorem pj_tr_cont_pure (x : ∀ v, X.H v) : Continuous fun g => X.σs g (X.tens x) := by
  have hT := hX.2.1.2.2.1
  set a : X.I.Ginf → ∀ v, X.H v := fun g v => X.σ v (uMat (g v)) (x v) with ha
  have hac : ∀ v, Continuous fun g : X.I.Ginf => a g v := fun v =>
    (homOf_cont (X.σ v) (pj_tr_U X hX v) (x v)).comp (continuous_apply v)
  have hfun : (fun g => X.σs g (X.tens x)) = fun g => X.tens (a g) := funext fun g => hT.2.1 g x
  rw [hfun, continuous_iff_continuousAt]
  intro g0
  set F : X.I.Ginf → ℂ := fun g => (∏ v, ⟪a g v, a g v⟫_ℂ) - (∏ v, ⟪a g v, a g0 v⟫_ℂ) - (∏ v, ⟪a g0 v, a g v⟫_ℂ) +
    ∏ v, ⟪a g0 v, a g0 v⟫_ℂ with hF
  have hFc : Continuous F := by
    refine ((Continuous.sub ?_ ?_).sub ?_).add continuous_const
    · exact continuous_finsetProd _ fun v _ => (hac v).inner (hac v)
    · exact continuous_finsetProd _ fun v _ => (hac v).inner continuous_const
    · exact continuous_finsetProd _ fun v _ => continuous_const.inner (hac v)
  have hN : ∀ g, ‖X.tens (a g) - X.tens (a g0)‖ = Real.sqrt (RCLike.re (F g)) := by
    intro g
    rw [← Real.sqrt_sq (norm_nonneg (X.tens (a g) - X.tens (a g0))), ← inner_self_eq_norm_sq (𝕜 := ℂ),
      inner_sub_left, inner_sub_right, inner_sub_right, hT.1, hT.1, hT.1, hT.1]
    congr 2
    simp only [hF]
    ring
  have hF0 : F g0 = 0 := by simp only [hF]; ring
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp only [hN]
  have hc : Continuous fun g => Real.sqrt (RCLike.re (F g)) := Real.continuous_sqrt.comp (RCLike.continuous_re.comp hFc)
  have := hc.tendsto g0
  simpa [hF0] using this

/- English proof (translation)
Establish `hspan : ∀ y ∈ Submodule.span ℂ (Set.range X.tens), Continuous fun g => X.σs g y`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨z, rfl⟩` from `hy`.

Conclude with `pj_tr_cont_pure X hX z`. Consider the case `zero => simpa using continuous_const`. Consider the case `add y z _ _ h1 h2`. Simplify using `only [map_add]`. Conclude with `h1.add h2`.

Consider the case `smul c y _ h1`. Simplify using `only [map_smul]`. Conclude with `h1.const_smul c`. Use `continuous_of_uniform_approx_of_continuous fun u hu => ?_` and prove the remaining obligations. Take `⟨ε, hε, hu⟩` from `Metric.mem_uniformity_dist.1 hu`.

Take `⟨y, hy, hd⟩` from `Metric.mem_closure_iff.1 (hX.2.1.2.2.1.2.2 x) ε hε`. Use `⟨fun g => X.σs g y, hspan y hy, fun g => hu ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, ← map_sub, pj_tr_norm X hX, ← dist_eq_norm]`. Conclude with `hd`.
-/
theorem pj_tr_cont (x : X.Hs) : Continuous fun g => X.σs g x := by
  have hspan : ∀ y ∈ Submodule.span ℂ (Set.range X.tens), Continuous fun g => X.σs g y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, rfl⟩ := hy
      exact pj_tr_cont_pure X hX z
    | zero => simpa using continuous_const
    | add y z _ _ h1 h2 =>
      simp only [map_add]
      exact h1.add h2
    | smul c y _ h1 =>
      simp only [map_smul]
      exact h1.const_smul c
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hu⟩ := Metric.mem_uniformity_dist.1 hu
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 (hX.2.1.2.2.1.2.2 x) ε hε
  refine ⟨fun g => X.σs g y, hspan y hy, fun g => hu ?_⟩
  rw [dist_eq_norm, ← map_sub, pj_tr_norm X hX, ← dist_eq_norm]
  exact hd

/- English proof (translation)
Assemble the required witnesses or components as `⟨pj_tr_mul X hX, pj_tr_one X hX, pj_tr_norm X hX, pj_tr_cont X hX⟩`.
-/
theorem pj_tensRep : TensRep X :=
  ⟨pj_tr_mul X hX, pj_tr_one X hX, pj_tr_norm X hX, pj_tr_cont X hX⟩

end

end Formalism.MainNotions.LeviCoordinates

end
