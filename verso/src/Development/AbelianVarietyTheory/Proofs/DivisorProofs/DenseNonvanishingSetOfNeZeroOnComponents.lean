import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

/- English proof (translation)
Introduce `n Y _ _ _ _ _ ι La _ A Λ τ T hs hT hP`. Use `set Zs : Set Y := {y | τ (A.pick y) y = 0} with hZs`. Establish `hc : (nz A τ)ᶜ = Zs`. Use extensionality with `y`. Simplify using `[nz, Zs]`.

Establish `toI : ∀ i x, x ∈ (A.chart i).source → τ (A.pick x) x = 0 → τ i x = 0`. Introduce `i x hx h0`. Rewrite using `[hs.2 i (A.pick x) x (Set.mem_univ _) hx (A.mem_pick x), h0, mul_zero]`. Establish `toP : ∀ i x, x ∈ (A.chart i).source → τ i x = 0 → τ (A.pick x) x = 0`. Introduce `i x hx h0`.

Rewrite using `[hs.2 (A.pick x) i x (Set.mem_univ _) (A.mem_pick x) hx, h0, mul_zero]`. Use `set Z := interior Zs with hZ`. Establish `hZo : IsOpen Z` using `isOpen_interior`. Establish `hZc : IsClosed Z`. Rewrite using `[← closure_subset_iff_isClosed]`.

Introduce `y hy`. Use `set i := A.pick y`. Use `set e := A.chart i`. Establish `hyv : e y ∈ e.target` using `e.map_source (A.mem_pick y)`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.mp e.open_target (e y) hyv`.

Use `set W : Set Y := e.source ∩ e ⁻¹' ball (e y) r`. Establish `hWo : IsOpen W` using `e.isOpen_inter_preimage isOpen_ball`. Establish `hyW : y ∈ W` using `⟨A.mem_pick y, mem_ball_self hr⟩`. Take `⟨x, hxW, hxZ⟩` from `(mem_closure_iff.mp hy) W hWo hyW`. Use `set F : V n → ℂ := τ i ∘ e.symm`.

Establish `hF : DifferentiableOn ℂ F (ball (e y) r)`. Use `hs.1 i` as an intermediate fact. Use `this.mono ?_` and prove the remaining obligations. Introduce `w hw`. Conclude with `⟨hball hw, Set.mem_univ _⟩`.

Establish `hxs : e x ∈ ball (e y) r` using `hxW.2`. Establish `hev : F =ᶠ[𝓝 (e x)] 0`. Establish `hxt : e x ∈ e.target` using `e.map_source hxW.1`. Establish `h1 : ∀ᶠ w in 𝓝 (e x), e.symm w ∈ Z`. Establish `hca : ContinuousAt e.symm (e x)` using `e.continuousAt_symm hxt`.

Establish `: e.symm (e x) = x` using `e.left_inv hxW.1`. Use `hca.preimage_mem_nhds ?_` and prove the remaining obligations. Rewrite using `[this]`. Conclude with `hZo.mem_nhds hxZ`. Establish `h2 : ∀ᶠ w in 𝓝 (e x), w ∈ e.target` using `e.open_target.mem_nhds hxt`.

Use `filter_upwards [h1, h2] with w hw1 hw2`. Establish `hsrc : e.symm w ∈ e.source` using `e.map_target hw2`. Conclude with `toI i _ hsrc (interior_subset (s := Zs) hw1)`. Establish `hEq` using `ReciprocityTheory.L2DbarEstimates.C.ident n (ball (e y) r) F (e x) isOpen_ball (convex_ball _ _) hF hxs hev`. Establish `hWZs : W ⊆ Zs`.

Introduce `z hz`. Establish `h0 : F (e z) = 0` using `hEq hz.2`. Establish `: τ i z = 0`. Simplify `h0` using `[F, e.left_inv hz.1]`. Conclude with `toP i z hz.1 this`.

Conclude with `interior_maximal hWZs hWo hyW`. Establish `hempty : Z = ∅`. Assume the negation of the conclusion as `hne`. Take `⟨y, hy⟩` from `Set.nonempty_iff_ne_empty.mpr hne`. Take `⟨P, hPT, hPc⟩` from `hT y`.

Establish `hsub` using `(IsClopen.connectedComponent_subset ⟨hZc, hZo⟩ hy)`. Conclude with `hP P hPT (interior_subset (s := Zs) (hsub hPc))`. Establish `hd` using `interior_eq_empty_iff_dense_compl.mp hempty`. Rewrite `hd` using `[← hc, compl_compl]`. Conclude with `hd`.
-/
theorem nz_dense_of_ne_zero_on_components : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (T : Set Y), A.IsSec Λ τ →
    (∀ y, ∃ P ∈ T, P ∈ connectedComponent y) → (∀ P ∈ T, τ (A.pick P) P ≠ 0) →
    Dense (nz A τ) := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ T hs hT hP
  set Zs : Set Y := {y | τ (A.pick y) y = 0} with hZs
  have hc : (nz A τ)ᶜ = Zs := by
    ext y; simp [nz, Zs]

  have toI : ∀ i x, x ∈ (A.chart i).source → τ (A.pick x) x = 0 → τ i x = 0 := by
    intro i x hx h0
    rw [hs.2 i (A.pick x) x (Set.mem_univ _) hx (A.mem_pick x), h0, mul_zero]
  have toP : ∀ i x, x ∈ (A.chart i).source → τ i x = 0 → τ (A.pick x) x = 0 := by
    intro i x hx h0
    rw [hs.2 (A.pick x) i x (Set.mem_univ _) (A.mem_pick x) hx, h0, mul_zero]
  set Z := interior Zs with hZ
  have hZo : IsOpen Z := isOpen_interior
  have hZc : IsClosed Z := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    set i := A.pick y
    set e := A.chart i
    have hyv : e y ∈ e.target := e.map_source (A.mem_pick y)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) hyv
    set W : Set Y := e.source ∩ e ⁻¹' ball (e y) r
    have hWo : IsOpen W := e.isOpen_inter_preimage isOpen_ball
    have hyW : y ∈ W := ⟨A.mem_pick y, mem_ball_self hr⟩
    obtain ⟨x, hxW, hxZ⟩ := (mem_closure_iff.mp hy) W hWo hyW
    set F : V n → ℂ := τ i ∘ e.symm
    have hF : DifferentiableOn ℂ F (ball (e y) r) := by
      have := hs.1 i
      refine this.mono ?_
      intro w hw; exact ⟨hball hw, Set.mem_univ _⟩
    have hxs : e x ∈ ball (e y) r := hxW.2
    have hev : F =ᶠ[𝓝 (e x)] 0 := by
      have hxt : e x ∈ e.target := e.map_source hxW.1
      have h1 : ∀ᶠ w in 𝓝 (e x), e.symm w ∈ Z := by
        have hca : ContinuousAt e.symm (e x) := e.continuousAt_symm hxt
        have : e.symm (e x) = x := e.left_inv hxW.1
        refine hca.preimage_mem_nhds ?_
        rw [this]; exact hZo.mem_nhds hxZ
      have h2 : ∀ᶠ w in 𝓝 (e x), w ∈ e.target := e.open_target.mem_nhds hxt
      filter_upwards [h1, h2] with w hw1 hw2
      have hsrc : e.symm w ∈ e.source := e.map_target hw2
      exact toI i _ hsrc (interior_subset (s := Zs) hw1)
    have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n (ball (e y) r) F (e x) isOpen_ball (convex_ball _ _) hF hxs hev
    have hWZs : W ⊆ Zs := by
      intro z hz
      have h0 : F (e z) = 0 := hEq hz.2
      have : τ i z = 0 := by
        simpa [F, e.left_inv hz.1] using h0
      exact toP i z hz.1 this
    exact interior_maximal hWZs hWo hyW
  have hempty : Z = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨P, hPT, hPc⟩ := hT y
    have hsub := (IsClopen.connectedComponent_subset ⟨hZc, hZo⟩ hy)
    exact hP P hPT (interior_subset (s := Zs) (hsub hPc))
  have hd := interior_eq_empty_iff_dense_compl.mp hempty
  rw [← hc, compl_compl] at hd
  exact hd

end GlobalTheory
