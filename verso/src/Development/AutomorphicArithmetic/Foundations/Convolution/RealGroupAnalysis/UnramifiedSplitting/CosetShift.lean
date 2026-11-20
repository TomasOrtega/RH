import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical
open scoped nonZeroDivisors

/- English proof (translation)
Rewrite using `[cosetIndicator_apply, cosetIndicator_apply]`. Establish `e : x + s - b = (x - b) + s` using `by ring`. Establish `h : x + s - b ∈ idealFiniteAdeles J ↔ x - b ∈ idealFiniteAdeles J`. Rewrite using `[e]`. Conclude with `AddSubgroup.add_mem_cancel_right _ hs`.

Simplify using `only [h]`.
-/
private theorem coset_shift {K : Type} [Field K] [NumberField K]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b x s : FiniteAdeleRing (𝓞 K) K)
    (hs : s ∈ idealFiniteAdeles J) : cosetIndicator J b (x + s) = cosetIndicator J b x := by
  rw [cosetIndicator_apply, cosetIndicator_apply]
  have e : x + s - b = (x - b) + s := by ring
  have h : x + s - b ∈ idealFiniteAdeles J ↔ x - b ∈ idealFiniteAdeles J := by
    rw [e]
    exact AddSubgroup.add_mem_cancel_right _ hs
  simp only [h]

/- English proof (translation)
Rewrite using `[mem_idealFiniteAdeles]`. Introduce `v'`. Take `⟨-, -, -, -, -, -, -, h8, -⟩` from `sgLaws K v`. Distinguish the cases in `hv : v' = v`. Substitute `hv` using the available equality.

Establish `h3` using `((sgLaws K v').2.2.1 y)`. Establish `: (sg v' y).2 v' = y` using `h3`. Rewrite using `[this, hJ, neg_zero, WithZero.exp_zero]`. Conclude with `hy`. Rewrite using `[(h8 y).2 v' hv]`.

Express the relevant statement in the definitionally equal form `Valued.v (0 : v'.adicCompletion K) ≤ _`. Rewrite using `[map_zero]`. Conclude with `zero_le`.
-/
private theorem std_gen {K : Type} [Field K] [NumberField K]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (v : P K)
    (hJ : FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = 0) (y : Kv v) (hy : IsInt y) :
    (sg v y).2 ∈ idealFiniteAdeles J := by
  rw [mem_idealFiniteAdeles]
  intro v'
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := sgLaws K v
  by_cases hv : v' = v
  · subst hv
    have h3 := ((sgLaws K v').2.2.1 y)
    have : (sg v' y).2 v' = y := h3
    rw [this, hJ, neg_zero, WithZero.exp_zero]
    exact hy
  · rw [(h8 y).2 v' hv]
    change Valued.v (0 : v'.adicCompletion K) ≤ _
    rw [map_zero]
    exact zero_le

/- English proof (translation)
Introduce `K _ _ φ`. Take `⟨f, hf⟩` from `φ`. Express the relevant statement in the definitionally equal form `∀ᶠ v in cofinite, Std v f`. Rewrite `hf` using `[schwartzBruhatPi_eq_cosetSpanPi]`. Proceed by induction on `hf using Submodule.span_induction with`.

Consider the case `mem F h`. Take `⟨g, J, b, rfl⟩` from `h`. Establish `h1 : ∀ᶠ v : P K in cofinite, FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = 0` using `FractionalIdeal.finite_factors (J : FractionalIdeal (𝓞 K)⁰ K)`. Establish `h2 : ∀ᶠ v : P K in cofinite, ∀ i, Valued.v ((b i) v) ≤ 1` using `eventually_all.2 fun i => (b i).2`. Use `filter_upwards [h1, h2] with v hJ hb`.

Use `⟨fun x hx i => ?_, fun x y hy => ?_⟩` and prove the remaining obligations. Establish `hi : cosetIndicator J (b i) ((x i).2) ≠ 0`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Simplify using `only [schwartzBruhatTensorPi, finiteTensor, finPartPi]`.

Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero]`. Rewrite `hi` using `[cosetIndicator_apply]`. Establish `hm : (x i).2 - b i ∈ idealFiniteAdeles J`. Assume the negation of the conclusion as `hc`. Conclude with `hi (if_neg hc)`.

Establish `hv` using `(mem_idealFiniteAdeles J).1 hm v`. Rewrite `hv` using `[hJ, neg_zero, WithZero.exp_zero]`. Establish `e : (x i).2 v = ((x i).2 - b i) v + (b i) v`. Express the relevant statement in the definitionally equal form `_ = (x i).2 v - (b i) v + (b i) v`. Expand and normalize the polynomial expressions, which then agree.

Express the relevant statement in the definitionally equal form `Valued.v ((x i).2 v) ≤ 1`. Rewrite using `[e]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le hv (hb i))`. Establish `e : ∀ i, (x i + sg v (y i)).1 = (x i).1` using `fun i => by`. Express the relevant statement in the definitionally equal form `(x i).1 + (sg v (y i)).1 = _`.

Rewrite using `[((sgLaws K v).2.2.2.2.2.2.2.1 (y i)).1, add_zero]`. Establish `e2 : ∀ i, cosetIndicator J (b i) (x i + sg v (y i)).2 = cosetIndicator J (b i) (x i).2` using `fun i => coset_shift J (b i) _ _ (std_gen J v hJ (y i) (hy i))`. Establish `e3 : infPartPi (fun i => x i + sg v (y i)) = infPartPi x`. Unfold `infPartPi`. Simplify using `only [e]`.

Simplify using `only [schwartzBruhatTensorPi, finiteTensor, finPartPi, e2, e3]`. Consider the case `zero`. Use `Eventually.of_forall fun v => ⟨fun x hx => absurd rfl hx, fun x y _ => rfl⟩` and prove the remaining obligations. Consider the case `add f g _ _ ihf ihg => filter_upwards [ihf, ihg] with v a c`. Use `⟨fun x hx i => ?_, fun x y hy => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h : f x = 0`. Use `c.1 x (fun h' => hx ?_) i` and prove the remaining obligations. Simplify using `[h, h']`. Conclude with `a.1 x h i`. Simplify using `only [Pi.add_apply, a.2 x y hy, c.2 x y hy]`.

Consider the case `smul t f _ ih => filter_upwards [ih] with v a`. Use `⟨fun x hx i => ?_, fun x y hy => ?_⟩` and prove the remaining obligations. Use `a.1 x (fun h' => hx ?_) i` and prove the remaining obligations. Simplify using `[h']`. Simplify using `only [Pi.smul_apply, a.2 x y hy]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.H.stdAe :
    ∀ (K : Type) [Field K] [NumberField K] (φ : S4 K), ∀ᶠ v in cofinite, Std v φ.1 := by
  intro K _ _ φ
  obtain ⟨f, hf⟩ := φ
  change ∀ᶠ v in cofinite, Std v f
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hf
  induction hf using Submodule.span_induction with
  | mem F h =>
    obtain ⟨g, J, b, rfl⟩ := h
    have h1 : ∀ᶠ v : P K in cofinite, FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      FractionalIdeal.finite_factors (J : FractionalIdeal (𝓞 K)⁰ K)
    have h2 : ∀ᶠ v : P K in cofinite, ∀ i, Valued.v ((b i) v) ≤ 1 :=
      eventually_all.2 fun i => (b i).2
    filter_upwards [h1, h2] with v hJ hb
    refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
    · have hi : cosetIndicator J (b i) ((x i).2) ≠ 0 := by
        intro h0
        apply hx
        simp only [schwartzBruhatTensorPi, finiteTensor, finPartPi]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero]
      rw [cosetIndicator_apply] at hi
      have hm : (x i).2 - b i ∈ idealFiniteAdeles J := by
        by_contra hc
        exact hi (if_neg hc)
      have hv := (mem_idealFiniteAdeles J).1 hm v
      rw [hJ, neg_zero, WithZero.exp_zero] at hv
      have e : (x i).2 v = ((x i).2 - b i) v + (b i) v := by
        change _ = (x i).2 v - (b i) v + (b i) v
        ring
      change Valued.v ((x i).2 v) ≤ 1
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le hv (hb i))
    · have e : ∀ i, (x i + sg v (y i)).1 = (x i).1 := fun i => by
        change (x i).1 + (sg v (y i)).1 = _
        rw [((sgLaws K v).2.2.2.2.2.2.2.1 (y i)).1, add_zero]
      have e2 : ∀ i, cosetIndicator J (b i) (x i + sg v (y i)).2 = cosetIndicator J (b i) (x i).2 :=
        fun i => coset_shift J (b i) _ _ (std_gen J v hJ (y i) (hy i))
      have e3 : infPartPi (fun i => x i + sg v (y i)) = infPartPi x := by
        unfold infPartPi
        simp only [e]
      simp only [schwartzBruhatTensorPi, finiteTensor, finPartPi, e2, e3]
  | zero =>
    refine Eventually.of_forall fun v => ⟨fun x hx => absurd rfl hx, fun x y _ => rfl⟩
  | add f g _ _ ihf ihg =>
    filter_upwards [ihf, ihg] with v a c
    refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
    · by_cases h : f x = 0
      · refine c.1 x (fun h' => hx ?_) i
        simp [h, h']
      · exact a.1 x h i
    · simp only [Pi.add_apply, a.2 x y hy, c.2 x y hy]
  | smul t f _ ih =>
    filter_upwards [ih] with v a
    refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
    · refine a.1 x (fun h' => hx ?_) i
      simp [h']
    · simp only [Pi.smul_apply, a.2 x y hy]
