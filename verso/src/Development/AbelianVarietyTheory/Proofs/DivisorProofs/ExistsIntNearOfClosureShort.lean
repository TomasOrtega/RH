import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

/- English proof (translation)
Establish `h : ∀ z : ι → ℤ, (fun i => (z i : ℝ)) ∈ Submodule.span ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T)`. Introduce `z`. Establish `hz : z ∈ AddSubgroup.closure T` using `by rw [hT]; trivial`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩`.

Consider the case `zero`. Establish `: (fun i => (((0 : ι → ℤ) i : ℤ) : ℝ)) = 0` using `by ext i; simp`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add u v _ _ hu hv`.

Establish `: (fun i => (((u + v) i : ℤ) : ℝ)) = (fun i => (u i : ℝ)) + fun i => (v i : ℝ)`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hu hv`.

Consider the case `neg u _ hu`. Establish `: (fun i => (((-u) i : ℤ) : ℝ)) = -(fun i => (u i : ℝ))`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Submodule.neg_mem _ hu`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Rewrite using `[pi_eq_sum_univ x]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations.

Use `h (fun j => if i = j then 1 else 0)` as an intermediate fact. Use `this using 2 with j` and compare the differences between its conclusion and the goal. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem span_intCast_image_eq_top {ι : Type} [Fintype ι] [DecidableEq ι] (T : Set (ι → ℤ))
    (hT : AddSubgroup.closure T = ⊤) :
    Submodule.span ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T) = ⊤ := by
  have h : ∀ z : ι → ℤ, (fun i => (z i : ℝ)) ∈
      Submodule.span ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T) := by
    intro z
    have hz : z ∈ AddSubgroup.closure T := by rw [hT]; trivial
    induction hz using AddSubgroup.closure_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero =>
      have : (fun i => (((0 : ι → ℤ) i : ℤ) : ℝ)) = 0 := by ext i; simp
      rw [this]; exact Submodule.zero_mem _
    | add u v _ _ hu hv =>
      have : (fun i => (((u + v) i : ℤ) : ℝ)) = (fun i => (u i : ℝ)) + fun i => (v i : ℝ) := by
        ext i; simp
      rw [this]; exact Submodule.add_mem _ hu hv
    | neg u _ hu =>
      have : (fun i => (((-u) i : ℤ) : ℝ)) = -(fun i => (u i : ℝ)) := by
        ext i; simp
      rw [this]; exact Submodule.neg_mem _ hu
  rw [eq_top_iff]
  intro x _
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have := h (fun j => if i = j then 1 else 0)
  convert this using 2 with j
  split_ifs <;> simp

/- English proof (translation)
Introduce `ι _ _ A hA T ρ hρ hT hz x`. Use `set B : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toBilin' A with hB`. Establish `hBq : ∀ v : ι → ℝ, ∑ i, ∑ j, A i j * v i * v j = B v v`. Introduce `v`. Rewrite using `[hB, Matrix.toBilin'_apply]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Establish `hpos : ∀ v : ι → ℝ, 0 ≤ B v v`. Introduce `v`. Rewrite using `[hB, Matrix.toBilin'_apply']`. Simplify using `using hA.posSemidef.dotProduct_mulVec_nonneg v`.

Establish `hsymm : ∀ u v : ι → ℝ, B u v = B v u`. Introduce `u v`. Rewrite using `[hB, Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `: A j i = A i j` using `by simpa using hA.isHermitian.apply i j`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨b, hbS, hspan, hli⟩` from `exists_linearIndependent ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T)`. Rewrite `hspan` using `[span_intCast_image_eq_top T hT]`. Establish `hfin : b.Finite` using `hli.setFinite`.

Use `haveI : Fintype b := hfin.fintype`. Establish `hcard : Fintype.card b ≤ Fintype.card ι`. Simplify using `using hli.fintype_card_le_finrank`. Establish `hx : x ∈ Submodule.span ℝ (Set.range ((↑) : b → ι → ℝ))`. Rewrite using `[Subtype.range_coe, hspan]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨t, ht⟩` from `(Submodule.mem_span_range_iff_exists_fun ℝ).1 hx`. Use `choose w hwT hw using fun a : b => hbS a.2`. Establish `hq : ∀ a : b, B a a ≤ ρ ^ 2`. Introduce `a`.

Rewrite using `[← hBq, ← hw a]`. Conclude with `hz _ (hwT a)`. Establish `hq2 : ∀ a c : b, B a c ≤ ρ ^ 2`. Introduce `a c`. Establish `h1` using `hpos ((a : ι → ℝ) - c)`.

Simplify using `only [map_sub, LinearMap.sub_apply] at h1`. Use `hsymm c a` as an intermediate fact. Use `hq a` as an intermediate fact. Use `hq c` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨∑ a : b, ⌊t a⌋ • w a, ?_⟩` and prove the remaining obligations. Establish `hy : (fun i => x i - ((∑ a : b, ⌊t a⌋ • w a) i : ℤ)) = ∑ a : b, Int.fract (t a) • (a : ι → ℝ)`. Use extensionality with `i`. Rewrite using `[← ht]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `: (w a i : ℝ) = (a : ι → ℝ) i` using `congrFun (hw a) i`. Rewrite using `[this, Int.fract]`. Expand and normalize the polynomial expressions, which then agree. Use `hBq (fun i => x i - ((∑ a : b, ⌊t a⌋ • w a) i : ℤ))` as an intermediate fact.

Rewrite using `[this, hy]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `try rw [Finset.mul_sum]`.

Use `Finset.sum_le_sum fun c _ => ?_` and prove the remaining obligations. Establish `h1` using `Int.fract_nonneg (t a)`. Establish `h2` using `(Int.fract_lt_one (t a)).le`. Establish `h3` using `Int.fract_nonneg (t c)`. Establish `h4` using `(Int.fract_lt_one (t c)).le`.

Establish `h5` using `hq2 a c`. Establish `h6` using `hq2 c a`. Establish `h7 : 0 ≤ ρ ^ 2` using `by positivity`. Establish `h8` using `mul_nonneg h1 h3`. Establish `h9 : Int.fract (t a) * Int.fract (t c) ≤ 1` using `mul_le_one₀ h2 h3 h4`.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h5 h8, mul_le_mul_of_nonneg_left h6 h8, mul_le_mul_of_nonneg_right h9 h7]`. Use `_ = (Fintype.card b * ρ) ^ 2 := by`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := by gcongr`.
-/
theorem exists_int_near_of_closure_short :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ : ℝ), 0 ≤ ρ → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → ∀ x : ι → ℝ, ∃ z : ι → ℤ, ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤ (Fintype.card ι * ρ) ^ 2 := by
  intro ι _ _ A hA T ρ hρ hT hz x
  classical
  set B : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toBilin' A with hB
  have hBq : ∀ v : ι → ℝ, ∑ i, ∑ j, A i j * v i * v j = B v v := by
    intro v
    rw [hB, Matrix.toBilin'_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hpos : ∀ v : ι → ℝ, 0 ≤ B v v := by
    intro v
    rw [hB, Matrix.toBilin'_apply']
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg v
  have hsymm : ∀ u v : ι → ℝ, B u v = B v u := by
    intro u v
    rw [hB, Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : A j i = A i j := by simpa using hA.isHermitian.apply i j
    rw [this]; ring
  obtain ⟨b, hbS, hspan, hli⟩ :=
    exists_linearIndependent ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T)
  rw [span_intCast_image_eq_top T hT] at hspan
  have hfin : b.Finite := hli.setFinite
  haveI : Fintype b := hfin.fintype
  have hcard : Fintype.card b ≤ Fintype.card ι := by
    simpa using hli.fintype_card_le_finrank
  have hx : x ∈ Submodule.span ℝ (Set.range ((↑) : b → ι → ℝ)) := by
    rw [Subtype.range_coe, hspan]; trivial
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
  choose w hwT hw using fun a : b => hbS a.2
  have hq : ∀ a : b, B a a ≤ ρ ^ 2 := by
    intro a
    rw [← hBq, ← hw a]
    exact hz _ (hwT a)
  have hq2 : ∀ a c : b, B a c ≤ ρ ^ 2 := by
    intro a c
    have h1 := hpos ((a : ι → ℝ) - c)
    simp only [map_sub, LinearMap.sub_apply] at h1
    have := hsymm c a
    have := hq a
    have := hq c
    linarith
  refine ⟨∑ a : b, ⌊t a⌋ • w a, ?_⟩
  have hy : (fun i => x i - ((∑ a : b, ⌊t a⌋ • w a) i : ℤ)) =
      ∑ a : b, Int.fract (t a) • (a : ι → ℝ) := by
    ext i
    rw [← ht]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : (w a i : ℝ) = (a : ι → ℝ) i := congrFun (hw a) i
    rw [this, Int.fract]; ring
  have := hBq (fun i => x i - ((∑ a : b, ⌊t a⌋ • w a) i : ℤ))
  rw [this, hy]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  calc _ ≤ ∑ _a : b, ∑ _c : b, ρ ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        try rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 := Int.fract_nonneg (t a)
        have h2 := (Int.fract_lt_one (t a)).le
        have h3 := Int.fract_nonneg (t c)
        have h4 := (Int.fract_lt_one (t c)).le
        have h5 := hq2 a c
        have h6 := hq2 c a
        have h7 : 0 ≤ ρ ^ 2 := by positivity
        have h8 := mul_nonneg h1 h3
        have h9 : Int.fract (t a) * Int.fract (t c) ≤ 1 := mul_le_one₀ h2 h3 h4
        nlinarith [mul_le_mul_of_nonneg_left h5 h8, mul_le_mul_of_nonneg_left h6 h8,
          mul_le_mul_of_nonneg_right h9 h7]
    _ = (Fintype.card b * ρ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := by
        gcongr

end GlobalTheory.HSAmp
