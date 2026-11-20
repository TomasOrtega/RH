import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormWindow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Introduce `σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hp hsep hrel`. Take `⟨N₀, k, f, hN₀o, hwN₀, hfa, hXN⟩` from `hX`. Take `⟨W₀, hW₀, hW₀iso⟩` from `hiso`. Establish `hev` using `(show ∀ᶠ z in 𝓝 w, z ∈ N₀ from hN₀o.mem_nhds hwN₀).and ((show ∀ᶠ z in 𝓝 w, z ∈ W₀ from hW₀).and (hp.and (Filter.eventually_all.2 hrel)))`. Take `⟨ε, hε, hεs⟩` from `Metric.nhds_basis_closedBall.eventually_iff.1 hev`.

Use `set K : Set (σ → ℂ) := Metric.sphere w ε ∩ (fun z i => f i z) ⁻¹' {0} with hK`. Establish `hsN : Metric.sphere w ε ⊆ N₀` using `fun z hz => (hεs (Metric.sphere_subset_closedBall hz)).1`. Establish `hKc : IsCompact K`. Use `(isCompact_sphere w ε).of_isClosed_subset ?_ Set.inter_subset_left` and prove the remaining obligations. Use `ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_sphere isClosed_singleton` and prove the remaining obligations.

Conclude with `continuousOn_pi.2 fun i => ((hfa i).continuousOn).mono hsN`. Establish `hKX : ∀ z ∈ K, z ∈ X`. Introduce `z hz`. Establish `: z ∈ X ∩ N₀`. Rewrite using `[hXN]`.

Use `⟨hsN hz.1, fun i => ?_⟩` and prove the remaining obligations. Use `congrFun (Set.mem_singleton_iff.1 hz.2) i` as an intermediate fact. Simplify using `using this`. Conclude with `this.1`. Establish `hXK : ∀ z ∈ X, z ∈ Metric.sphere w ε → z ∈ K`.

Introduce `z hzX hzs`. Use `⟨hzs, ?_⟩` and prove the remaining obligations. Establish `: z ∈ X ∩ N₀` using `⟨hzX, hsN hzs⟩`. Rewrite `this` using `[hXN]`. Conclude with `Set.mem_singleton_iff.2 (funext this.2)`.

Establish `hAK : A w ∉ A '' K`. Introduce and unpack `⟨z, hzK, hAz⟩`. Establish `hzw` using `(hεs (Metric.sphere_subset_closedBall hzK.1)).2.1`. Establish `hzeq` using `hW₀iso z ⟨hKX z hzK, hzw⟩ hAz`. Establish `h1` using `hzK.1`.

Rewrite `h1` using `[hzeq, Metric.mem_sphere, dist_self]`. Conclude with `hε.ne h1`. Establish `hclo : IsClosed (A '' K)` using `(hKc.image A.continuous).isClosed`. Establish `hev2` using `(show ∀ᶠ y in 𝓝 (A w), y ∈ (A '' K)ᶜ from hclo.isOpen_compl.mem_nhds hAK).and ((Filter.eventually_all.2 fun j => (ha j).eventually_analyticAt).and (hδ.eventually_analyticAt.and ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (hq i j).eventually_analyticAt).and …`. Take `⟨ρ, hρ, hρs⟩` from `Metric.nhds_basis_ball.eventually_iff.1 hev2`.

Use `⟨Metric.ball w ε, Metric.ball (A w) ρ, N₀, k, f, Metric.isOpen_ball, Metric.mem_ball_self hε, Metric.isOpen_ball, convex_ball _ _, Metric.mem_ball_self hρ, hN₀o, ?_, hfa, hXN, ?_, ?_, ?_, fun j y hy => (hρs hy).2.1 j, fun y hy => (hρs hy).2.2.1, fun i j y hy => (hρs hy).2.2.2.1 i …` and prove the remaining obligations. Rewrite using `[closure_ball w hε.ne']`. Conclude with `fun z hz => (hεs hz).1`. Introduce and unpack `z ⟨hzX, hzc⟩ hzB`. Rewrite `hzc` using `[closure_ball w hε.ne']`.

Break down `(Metric.mem_closedBall.1 hzc).lt_or_eq with h | h` into its components or cases. Conclude with `Metric.mem_ball.2 h`. Conclude with `absurd ⟨z, hXK z hzX (Metric.mem_sphere.2 h), rfl⟩ (hρs hzB).1`. Introduce and unpack `z ⟨hzX, hzW⟩`. Conclude with `(hεs (Metric.ball_subset_closedBall hzW)).2.2.1 hzX`.

Introduce and unpack `i z ⟨hzX, hzW⟩`. Conclude with `(hεs (Metric.ball_subset_closedBall hzW)).2.2.2 i hzX`.
-/
theorem PrimitiveFormWindow.proof : PrimitiveFormWindow.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hp hsep hrel
  obtain ⟨N₀, k, f, hN₀o, hwN₀, hfa, hXN⟩ := hX
  obtain ⟨W₀, hW₀, hW₀iso⟩ := hiso
  have hev := (show ∀ᶠ z in 𝓝 w, z ∈ N₀ from hN₀o.mem_nhds hwN₀).and
    ((show ∀ᶠ z in 𝓝 w, z ∈ W₀ from hW₀).and (hp.and (Filter.eventually_all.2 hrel)))
  obtain ⟨ε, hε, hεs⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hev
  set K : Set (σ → ℂ) := Metric.sphere w ε ∩ (fun z i => f i z) ⁻¹' {0} with hK
  have hsN : Metric.sphere w ε ⊆ N₀ := fun z hz => (hεs (Metric.sphere_subset_closedBall hz)).1
  have hKc : IsCompact K := by
    refine (isCompact_sphere w ε).of_isClosed_subset ?_ Set.inter_subset_left
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_sphere isClosed_singleton
    exact continuousOn_pi.2 fun i => ((hfa i).continuousOn).mono hsN
  have hKX : ∀ z ∈ K, z ∈ X := by
    intro z hz
    have : z ∈ X ∩ N₀ := by
      rw [hXN]
      refine ⟨hsN hz.1, fun i => ?_⟩
      have := congrFun (Set.mem_singleton_iff.1 hz.2) i
      simpa using this
    exact this.1
  have hXK : ∀ z ∈ X, z ∈ Metric.sphere w ε → z ∈ K := by
    intro z hzX hzs
    refine ⟨hzs, ?_⟩
    have : z ∈ X ∩ N₀ := ⟨hzX, hsN hzs⟩
    rw [hXN] at this
    exact Set.mem_singleton_iff.2 (funext this.2)
  have hAK : A w ∉ A '' K := by
    rintro ⟨z, hzK, hAz⟩
    have hzw := (hεs (Metric.sphere_subset_closedBall hzK.1)).2.1
    have hzeq := hW₀iso z ⟨hKX z hzK, hzw⟩ hAz
    have h1 := hzK.1
    rw [hzeq, Metric.mem_sphere, dist_self] at h1
    exact hε.ne h1
  have hclo : IsClosed (A '' K) := (hKc.image A.continuous).isClosed
  have hev2 := (show ∀ᶠ y in 𝓝 (A w), y ∈ (A '' K)ᶜ from hclo.isOpen_compl.mem_nhds hAK).and
    ((Filter.eventually_all.2 fun j => (ha j).eventually_analyticAt).and
      (hδ.eventually_analyticAt.and
        ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
          (hq i j).eventually_analyticAt).and hsep)))
  obtain ⟨ρ, hρ, hρs⟩ := Metric.nhds_basis_ball.eventually_iff.1 hev2
  refine ⟨Metric.ball w ε, Metric.ball (A w) ρ, N₀, k, f, Metric.isOpen_ball, Metric.mem_ball_self hε,
    Metric.isOpen_ball, convex_ball _ _, Metric.mem_ball_self hρ, hN₀o, ?_, hfa, hXN, ?_, ?_, ?_,
    fun j y hy => (hρs hy).2.1 j, fun y hy => (hρs hy).2.2.1, fun i j y hy => (hρs hy).2.2.2.1 i j,
    fun y hy => (hρs hy).2.2.2.2⟩
  · rw [closure_ball w hε.ne']
    exact fun z hz => (hεs hz).1
  · rintro z ⟨hzX, hzc⟩ hzB
    rw [closure_ball w hε.ne'] at hzc
    rcases (Metric.mem_closedBall.1 hzc).lt_or_eq with h | h
    · exact Metric.mem_ball.2 h
    · exact absurd ⟨z, hXK z hzX (Metric.mem_sphere.2 h), rfl⟩ (hρs hzB).1
  · rintro z ⟨hzX, hzW⟩
    exact (hεs (Metric.ball_subset_closedBall hzW)).2.2.1 hzX
  · rintro i z ⟨hzX, hzW⟩
    exact (hεs (Metric.ball_subset_closedBall hzW)).2.2.2 i hzX

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
