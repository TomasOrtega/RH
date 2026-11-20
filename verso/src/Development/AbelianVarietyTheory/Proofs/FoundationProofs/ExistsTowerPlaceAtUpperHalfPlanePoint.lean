import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3

open Filter Topology

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const Complex.continuous_im`.
-/
theorem isOpen_Hs_place : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨Complex.I, by simp [Hs]⟩, (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected⟩`.
-/
theorem isConnected_Hs_place : IsConnected Hs :=
  ⟨⟨Complex.I, by simp [Hs]⟩, (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected⟩

/- English proof (translation)
Establish `hA : AnalyticOnNhd ℂ a Hs` using `ha.analyticOnNhd isOpen_Hs_place`. Establish `hB : AnalyticOnNhd ℂ b Hs` using `hb.analyticOnNhd isOpen_Hs_place`. Establish `hx : ∃ x ∈ Hs, b x ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `hb0` to reduce the goal to its premises. Rewrite using `[← Filter.Germ.coe_zero]`. Use `Filter.Germ.coe_eq.2 ?_` and prove the remaining obligations. Use `filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz`. Take `⟨x, hxH, hx0⟩` from `hx`.

Establish `hne : b ⁻¹' {0}ᶜ ∈ codiscreteWithin Hs` using `hB.preimage_zero_mem_codiscreteWithin hx0 hxH isConnected_Hs_place`. Establish `hM : MeromorphicAt (a / b) τ` using `(hA τ hτ).meromorphicAt.div (hB τ hτ).meromorphicAt`. Use `⟨toMeromorphicNFAt (a / b) τ, ?_, hM.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 hord⟩` and prove the remaining obligations. Establish `h1 : ((b * b⁻¹ : ℂ → ℂ) : Mero) = 1`. Rewrite using `[← Filter.Germ.coe_one]`.

Use `Filter.Germ.coe_eq.2 ?_` and prove the remaining obligations. Use `filter_upwards [hne] with z hz`. Simplify using `only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]`. Conclude with `mul_inv_cancel₀ hz`. Establish `h2 : X.an f = ((a / b : ℂ → ℂ) : Mero)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h2]`. Use `Filter.Germ.coe_eq.2 ?_` and prove the remaining obligations. Use `filter_upwards [compl_finite_mem_codiscreteWithin (s := Hs) (Set.finite_singleton τ)] with z hz`. Conclude with `hM.eqOn_compl_singleton_toMeromorphicNFAt hz`.
-/
theorem exists_analyticAt_of_order_nonneg {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {τ : ℂ} (hτ : τ ∈ Hs) (f : X.K) (a b : ℂ → ℂ) (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (hb0 : (b : Mero) ≠ 0) (hab : X.an f * (b : Mero) = (a : Mero))
    (hord : 0 ≤ meromorphicOrderAt (a / b) τ) :
    ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs_place
  have hB : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd isOpen_Hs_place
  have hx : ∃ x ∈ Hs, b x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hb0
    rw [← Filter.Germ.coe_zero]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  obtain ⟨x, hxH, hx0⟩ := hx
  have hne : b ⁻¹' {0}ᶜ ∈ codiscreteWithin Hs :=
    hB.preimage_zero_mem_codiscreteWithin hx0 hxH isConnected_Hs_place
  have hM : MeromorphicAt (a / b) τ := (hA τ hτ).meromorphicAt.div (hB τ hτ).meromorphicAt
  refine ⟨toMeromorphicNFAt (a / b) τ, ?_, hM.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 hord⟩
  have h1 : ((b * b⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [← Filter.Germ.coe_one]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [hne] with z hz
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact mul_inv_cancel₀ hz
  have h2 : X.an f = ((a / b : ℂ → ℂ) : Mero) := by
    calc X.an f = X.an f * ((b * b⁻¹ : ℂ → ℂ) : Mero) := by rw [h1, mul_one]
      _ = (X.an f * (b : Mero)) * ((b⁻¹ : ℂ → ℂ) : Mero) := by rw [Filter.Germ.coe_mul, mul_assoc]
      _ = ((a / b : ℂ → ℂ) : Mero) := by rw [hab, ← Filter.Germ.coe_mul, div_eq_mul_inv]
  rw [h2]
  refine Filter.Germ.coe_eq.2 ?_
  filter_upwards [compl_finite_mem_codiscreteWithin (s := Hs) (Set.finite_singleton τ)] with z hz
  exact hM.eqOn_compl_singleton_toMeromorphicNFAt hz

end GlobalTheory.KZ.H3

namespace GlobalTheory.KZ.H3

open Filter Topology

/- English proof (translation)
Introduce `Ω _ _ ε X hj τ hτ`. Establish `h0 : ∃ φ : ℂ → ℂ, X.an 0 = (φ : Mero) ∧ AnalyticAt ℂ φ τ` using `⟨0, by rw [map_zero, Filter.Germ.coe_zero], analyticAt_const⟩`. Set `W : ValuationSubring X.K` to `{ carrier := {f | ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ} zero_mem' := h0 one_mem' := ⟨1, by rw [map_one, Filter.Germ.coe_one], analyticAt_const⟩ add_mem' := by`. Introduce and unpack `f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩`. Conclude with `⟨φ + ψ, by rw [map_add, h1, h3, Filter.Germ.coe_add], h2.add h4⟩`.

Use the proof step `mul_mem' := by`. Introduce and unpack `f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩`. Conclude with `⟨φ * ψ, by rw [map_mul, h1, h3, Filter.Germ.coe_mul], h2.mul h4⟩`. Use the proof step `neg_mem' := by`. Introduce and unpack `f ⟨φ, h1, h2⟩`.

Conclude with `⟨-φ, by rw [map_neg, h1, Filter.Germ.coe_neg], h2.neg⟩`. Use the proof step `mem_or_inv_mem' := by`. Introduce `f`. Distinguish the cases in `hf : f = 0`. Use `left`.

Rewrite using `[hf]`. Conclude with `h0`. Take `⟨a, b, ha, hb, hb0, hab⟩` from `X.an_mero f`. Establish `hu : X.an f⁻¹ * X.an f = 1` using `by rw [← map_mul, inv_mul_cancel₀ hf, map_one]`. Distinguish the cases in `hord : 0 ≤ meromorphicOrderAt (a / b) τ`.

Use `left`. Conclude with `exists_analyticAt_of_order_nonneg X hτ f a b ha hb hb0 hab hord`. Use `right`. Establish `ha0 : (a : Mero) ≠ 0`. Introduce `h`.

Apply `hb0` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hba : X.an f⁻¹ * (a : Mero) = (b : Mero)` using `by rw [← hab, ← mul_assoc, hu, one_mul]`. Establish `hinv : b / a = (a / b)⁻¹`. Use function extensionality and compare the values at `z`.

Simplify using `[inv_div]`. Establish `hord' : 0 ≤ meromorphicOrderAt (b / a) τ`. Rewrite using `[hinv, meromorphicOrderAt_inv]`. Use `push_neg at hord`. Generalize the expression as in `meromorphicOrderAt (a / b) τ = o at hord ⊢`.

Proceed by induction on `o with`. Consider the case `top => simp at hord`. Consider the case `coe n`. Establish `hn : n < 0` using `by exact_mod_cast hord`. Establish `: (0 : WithTop ℤ) ≤ ((-n : ℤ) : WithTop ℤ)` using `by exact_mod_cast (by omega : (0 : ℤ) ≤ -n)`.

Simplify using `using this`. Conclude with `exists_analyticAt_of_order_nonneg X hτ f⁻¹ b a hb ha ha0 hba hord' }`. Use `⟨W, ⟨fun c => ⟨fun _ => ε c, X.an_c c, analyticAt_const⟩, ?_⟩, fun f => Iff.rfl⟩` and prove the remaining obligations. Take `⟨φ, h1, h2⟩` from `hj`. Conclude with `⟨φ, h1, h2.analyticAt (isOpen_Hs_place.mem_nhds hτ)⟩`.
-/
theorem exists_place_at_point : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ τ ∈ Hs,
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ f : X.K, f ∈ W ↔ ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  intro Ω _ _ ε X hj τ hτ
  have h0 : ∃ φ : ℂ → ℂ, X.an 0 = (φ : Mero) ∧ AnalyticAt ℂ φ τ :=
    ⟨0, by rw [map_zero, Filter.Germ.coe_zero], analyticAt_const⟩
  let W : ValuationSubring X.K :=
    { carrier := {f | ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ}
      zero_mem' := h0
      one_mem' := ⟨1, by rw [map_one, Filter.Germ.coe_one], analyticAt_const⟩
      add_mem' := by
        rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
        exact ⟨φ + ψ, by rw [map_add, h1, h3, Filter.Germ.coe_add], h2.add h4⟩
      mul_mem' := by
        rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
        exact ⟨φ * ψ, by rw [map_mul, h1, h3, Filter.Germ.coe_mul], h2.mul h4⟩
      neg_mem' := by
        rintro f ⟨φ, h1, h2⟩
        exact ⟨-φ, by rw [map_neg, h1, Filter.Germ.coe_neg], h2.neg⟩
      mem_or_inv_mem' := by
        intro f
        by_cases hf : f = 0
        · left; rw [hf]; exact h0
        obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero f
        have hu : X.an f⁻¹ * X.an f = 1 := by rw [← map_mul, inv_mul_cancel₀ hf, map_one]
        by_cases hord : 0 ≤ meromorphicOrderAt (a / b) τ
        · left
          exact exists_analyticAt_of_order_nonneg X hτ f a b ha hb hb0 hab hord
        · right
          have ha0 : (a : Mero) ≠ 0 := by
            intro h
            apply hb0
            calc (b : Mero) = X.an f⁻¹ * (X.an f * (b : Mero)) := by rw [← mul_assoc, hu, one_mul]
              _ = 0 := by rw [hab, h, mul_zero]
          have hba : X.an f⁻¹ * (a : Mero) = (b : Mero) := by rw [← hab, ← mul_assoc, hu, one_mul]
          have hinv : b / a = (a / b)⁻¹ := by
            funext z; simp [inv_div]
          have hord' : 0 ≤ meromorphicOrderAt (b / a) τ := by
            rw [hinv, meromorphicOrderAt_inv]
            push_neg at hord
            generalize meromorphicOrderAt (a / b) τ = o at hord ⊢
            induction o with
            | top => simp at hord
            | coe n =>
              have hn : n < 0 := by exact_mod_cast hord
              have : (0 : WithTop ℤ) ≤ ((-n : ℤ) : WithTop ℤ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ -n)
              simpa using this
          exact exists_analyticAt_of_order_nonneg X hτ f⁻¹ b a hb ha ha0 hba hord' }
  refine ⟨W, ⟨fun c => ⟨fun _ => ε c, X.an_c c, analyticAt_const⟩, ?_⟩, fun f => Iff.rfl⟩
  obtain ⟨φ, h1, h2⟩ := hj
  exact ⟨φ, h1, h2.analyticAt (isOpen_Hs_place.mem_nhds hτ)⟩

end GlobalTheory.KZ.H3
