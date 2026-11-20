import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite

open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

/- English proof (translation)
Take `⟨u, hu, hmin⟩` from `exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv (0 : E)`. Establish `hin` using `(norm_eq_iInf_iff_real_inner_le_zero hconv hu).1 hmin`. Use `⟨u, hu, fun w hw => ?_⟩` and prove the remaining obligations. Establish `h1` using `hin w hw`. Establish `h3 : inner ℝ (0 - u) (w - u) = ‖u‖ ^ 2 - inner ℝ w u`.

Rewrite using `[zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm w u]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ‖w - u‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w u + ‖u‖ ^ 2` using `norm_sub_sq_real w u`. Establish `h4 : inner ℝ w u ≤ ‖w‖ * ‖u‖` using `real_inner_le_norm w u`. Establish `h5 : ‖u‖ ^ 2 ≤ ‖w‖ * ‖u‖` using `by linarith`.

Prove the components needed by the constructor for the conclusion. Break down `(norm_nonneg u).eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`. Conclude with `norm_nonneg w`. Use the polynomial consequences of the given equalities and inequalities.

Introduce `hle`. Establish `h6 : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2`. Use `norm_nonneg w` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `h7 : ‖w - u‖ ^ 2 ≤ 0` using `by nlinarith`.

Establish `h8 : ‖w - u‖ = 0`. Use `norm_nonneg (w - u)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Conclude with `sub_eq_zero.1 (norm_eq_zero.1 h8)`.
-/
theorem exists_least_norm_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C) (hconv : Convex ℝ C) :
    ∃ u ∈ C, ∀ w ∈ C, ‖u‖ ≤ ‖w‖ ∧ (‖w‖ ≤ ‖u‖ → w = u) := by
  obtain ⟨u, hu, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv (0 : E)
  have hin := (norm_eq_iInf_iff_real_inner_le_zero hconv hu).1 hmin
  refine ⟨u, hu, fun w hw => ?_⟩
  have h1 := hin w hw
  have h3 : inner ℝ (0 - u) (w - u) = ‖u‖ ^ 2 - inner ℝ w u := by
    rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm w u]
    ring
  have h2 : ‖w - u‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w u + ‖u‖ ^ 2 := norm_sub_sq_real w u
  have h4 : inner ℝ w u ≤ ‖w‖ * ‖u‖ := real_inner_le_norm w u
  have h5 : ‖u‖ ^ 2 ≤ ‖w‖ * ‖u‖ := by linarith
  constructor
  · rcases (norm_nonneg u).eq_or_lt with h0 | h0
    · rw [← h0]; exact norm_nonneg w
    · nlinarith
  · intro hle
    have h6 : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have := norm_nonneg w
      nlinarith
    have h7 : ‖w - u‖ ^ 2 ≤ 0 := by nlinarith
    have h8 : ‖w - u‖ = 0 := by
      have := norm_nonneg (w - u)
      nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h8)

/- English proof (translation)
Introduce `G H _ _ _ _ _ _ _ σ hiso hcont`. Take `⟨x, hx⟩` from `exists_ne (0 : H)`. Take `⟨v, hv⟩ : ∃ v : H, ‖v‖ = 1` from `⟨((‖x‖ : ℂ)⁻¹) • x, by`. Establish `: ‖x‖ ≠ 0` using `norm_ne_zero_iff.2 hx`. Simplify using `[norm_smul, this]⟩`.

Establish `hopen : IsOpen {g : G | ‖σ g v - v‖ < 1 / 2}` using `isOpen_lt (((hcont v).sub continuous_const).norm) continuous_const`. Establish `hone : (1 : G) ∈ {g : G | ‖σ g v - v‖ < 1 / 2}` using `by simp`. Take `⟨V, hV⟩` from `NonarchimedeanGroup.is_nonarchimedean _ (hopen.mem_nhds hone)`. Use `letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H`. Use `set A : Set H := Set.range (fun k : V => σ (k : G) v) with hA`.

Use `set C : Set H := closure (convexHull ℝ A) with hC`. Establish `hvA : v ∈ A` using `⟨1, by simp⟩`. Establish `hCne : C.Nonempty` using `⟨v, subset_closure (subset_convexHull ℝ A hvA)⟩`. Establish `hCconv : Convex ℝ C` using `(convex_convexHull ℝ A).closure`. Establish `hCball : C ⊆ Metric.closedBall v (1 / 2)`.

Use `closure_minimal (convexHull_min ?_ (convex_closedBall _ _)) Metric.isClosed_closedBall` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Use `hV k.2` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq] at this`. Rewrite using `[Metric.mem_closedBall, dist_eq_norm]`.

Conclude with `this.le`. Establish `hstable : ∀ k : V, ∀ y ∈ C, σ (k : G) y ∈ C`. Introduce `k y hy`. Establish `hmaps : Set.MapsTo (σ (k : G)) (convexHull ℝ A) (convexHull ℝ A)`. Establish `hconvpre : Convex ℝ ((σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A)` using `(convex_convexHull ℝ A).linear_preimage _`.

Establish `hsub : A ⊆ (σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A`. Introduce and unpack `_ ⟨l, rfl⟩`. Use `subset_convexHull ℝ A ⟨k * l, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `fun z hz => convexHull_min hsub hconvpre hz`.

Conclude with `map_mem_closure (σ (k : G)).continuous hy hmaps`. Take `⟨u, huC, hu⟩` from `exists_least_norm_unique hCne isClosed_closure hCconv`. Use `⟨V.toSubgroup, u, V.isOpen, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Use `hCball huC` as an intermediate fact.

Rewrite `this` using `[Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hv]`. Evaluate the numerical expressions using `at this`. Introduce `k hk`. Conclude with `(hu _ (hstable ⟨k, hk⟩ u huC)).2 (hiso k u).le`.
-/
theorem stFixVec : StFixVec := by
  intro G H _ _ _ _ _ _ _ σ hiso hcont
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨v, hv⟩ : ∃ v : H, ‖v‖ = 1 :=
    ⟨((‖x‖ : ℂ)⁻¹) • x, by
      have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      simp [norm_smul, this]⟩
  have hopen : IsOpen {g : G | ‖σ g v - v‖ < 1 / 2} :=
    isOpen_lt (((hcont v).sub continuous_const).norm) continuous_const
  have hone : (1 : G) ∈ {g : G | ‖σ g v - v‖ < 1 / 2} := by simp
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ (hopen.mem_nhds hone)
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  set A : Set H := Set.range (fun k : V => σ (k : G) v) with hA
  set C : Set H := closure (convexHull ℝ A) with hC
  have hvA : v ∈ A := ⟨1, by simp⟩
  have hCne : C.Nonempty := ⟨v, subset_closure (subset_convexHull ℝ A hvA)⟩
  have hCconv : Convex ℝ C := (convex_convexHull ℝ A).closure
  have hCball : C ⊆ Metric.closedBall v (1 / 2) := by
    refine closure_minimal (convexHull_min ?_ (convex_closedBall _ _)) Metric.isClosed_closedBall
    rintro _ ⟨k, rfl⟩
    have := hV k.2
    simp only [Set.mem_setOf_eq] at this
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact this.le
  have hstable : ∀ k : V, ∀ y ∈ C, σ (k : G) y ∈ C := by
    intro k y hy
    have hmaps : Set.MapsTo (σ (k : G)) (convexHull ℝ A) (convexHull ℝ A) := by
      have hconvpre : Convex ℝ ((σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A) :=
        (convex_convexHull ℝ A).linear_preimage _
      have hsub : A ⊆ (σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A := by
        rintro _ ⟨l, rfl⟩
        refine subset_convexHull ℝ A ⟨k * l, ?_⟩
        simp
      exact fun z hz => convexHull_min hsub hconvpre hz
    exact map_mem_closure (σ (k : G)).continuous hy hmaps
  obtain ⟨u, huC, hu⟩ := exists_least_norm_unique hCne isClosed_closure hCconv
  refine ⟨V.toSubgroup, u, V.isOpen, ?_, ?_⟩
  · rintro rfl
    have := hCball huC
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hv] at this
    norm_num at this
  · intro k hk
    exact (hu _ (hstable ⟨k, hk⟩ u huC)).2 (hiso k u).le

end GlobalTheory.CompanionTheory.RgFl
