import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

/- English proof (translation)
Take `⟨O, hO, hsec⟩` from `hL Set.univ Filter.univ_mem B₀ hB₁`. Establish `hemb : Topology.IsClosedEmbedding (Subtype.val : P → G)` using `hP.isClosedEmbedding_subtypeVal`. Establish `hC₁ : IsCompact ((Subtype.val : P → G) ⁻¹' B₀)` using `hemb.isCompact_preimage hB`. Use `hD.induction_on (p := fun T => ∃ C : Set P, IsCompact C ∧ ∀ g ∈ T, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c) ⟨∅, isCompact_empty, by simp⟩ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `S T hST ⟨C, hC, h⟩`.

Conclude with `⟨C, hC, fun g hg => h g (hST hg)⟩`. Introduce and unpack `S T ⟨C, hC, h⟩ ⟨C', hC', h'⟩`. Use `⟨C ∪ C', hC.union hC', ?_⟩` and prove the remaining obligations. Introduce and unpack `g (hg | hg)`. Take `⟨q, hq, c, hc, e⟩` from `h g hg`.

Conclude with `⟨q, hq, c, Or.inl hc, e⟩`. Take `⟨q, hq, c, hc, e⟩` from `h' g hg`. Conclude with `⟨q, hq, c, Or.inr hc, e⟩`. Introduce `g₀ hg₀`. Take `⟨q₀, hq₀, p₀, hp₀, e₀⟩` from `hDc hg₀`.

Establish `hcont : Continuous fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹` using `by fun_prop`. Establish `hval : (q₀ * x)⁻¹ * g₀ * p₀⁻¹ = 1`. Rewrite using `[e₀]`. Use `group`. Establish `hU : (fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹) ⁻¹' O ∈ 𝓝 g₀` using `hcont.continuousAt.preimage_mem_nhds (by rw [hval]; exact hO)`.

Use `⟨D ∩ (fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹) ⁻¹' O, Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU), (fun c : P => c * (⟨p₀, hp₀⟩ : P)) '' ((Subtype.val : P → G) ⁻¹' B₀), hC₁.image (by fun_prop), ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨hgD, hgU⟩`. Take `⟨q', hq', p', hp', e'⟩` from `hDc hgD`. Establish `hxu : x * ((q₀ * x)⁻¹ * g * p₀⁻¹) ∈ dcos Q P x`. Use `⟨q₀⁻¹ * q', Q.mul_mem (Q.inv_mem hq₀) hq', p' * p₀⁻¹, P.mul_mem hp' (P.inv_mem hp₀), ?_⟩` and prove the remaining obligations.

Rewrite using `[e']`. Use `group`. Take `⟨s, hs, -, p₂, hp₂, hp₂B, e₂⟩` from `hsec _ hgU hxu`. Use `⟨q₀ * s, Q.mul_mem hq₀ hs, ⟨p₂, hp₂⟩ * ⟨p₀, hp₀⟩, ⟨⟨p₂, hp₂⟩, hp₂B, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e₃ : g = q₀ * (x * ((q₀ * x)⁻¹ * g * p₀⁻¹)) * p₀` using `by group`.

Rewrite using `[e₃, e₂]`. Simplify using `[mul_assoc]`.
-/
theorem dcos_compact_lift {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Q P : Subgroup G} {x : G}
    (hL : LocSec Q P x) (hP : IsClosed (P : Set G)) (B₀ : Set G) (hB : IsCompact B₀) (hB₁ : B₀ ∈ 𝓝 (1 : G))
    (D : Set G) (hD : IsCompact D) (hDc : D ⊆ dcos Q P x) :
    ∃ C : Set P, IsCompact C ∧ ∀ g ∈ D, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c := by
  obtain ⟨O, hO, hsec⟩ := hL Set.univ Filter.univ_mem B₀ hB₁
  have hemb : Topology.IsClosedEmbedding (Subtype.val : P → G) := hP.isClosedEmbedding_subtypeVal
  have hC₁ : IsCompact ((Subtype.val : P → G) ⁻¹' B₀) := hemb.isCompact_preimage hB
  refine hD.induction_on
    (p := fun T => ∃ C : Set P, IsCompact C ∧ ∀ g ∈ T, ∃ q ∈ Q, ∃ c ∈ C, g = q * x * c)
    ⟨∅, isCompact_empty, by simp⟩ ?_ ?_ ?_
  · rintro S T hST ⟨C, hC, h⟩
    exact ⟨C, hC, fun g hg => h g (hST hg)⟩
  · rintro S T ⟨C, hC, h⟩ ⟨C', hC', h'⟩
    refine ⟨C ∪ C', hC.union hC', ?_⟩
    rintro g (hg | hg)
    · obtain ⟨q, hq, c, hc, e⟩ := h g hg
      exact ⟨q, hq, c, Or.inl hc, e⟩
    · obtain ⟨q, hq, c, hc, e⟩ := h' g hg
      exact ⟨q, hq, c, Or.inr hc, e⟩
  · intro g₀ hg₀
    obtain ⟨q₀, hq₀, p₀, hp₀, e₀⟩ := hDc hg₀
    have hcont : Continuous fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹ := by fun_prop
    have hval : (q₀ * x)⁻¹ * g₀ * p₀⁻¹ = 1 := by
      rw [e₀]; group
    have hU : (fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹) ⁻¹' O ∈ 𝓝 g₀ :=
      hcont.continuousAt.preimage_mem_nhds (by rw [hval]; exact hO)
    refine ⟨D ∩ (fun g : G => (q₀ * x)⁻¹ * g * p₀⁻¹) ⁻¹' O,
      Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU),
      (fun c : P => c * (⟨p₀, hp₀⟩ : P)) '' ((Subtype.val : P → G) ⁻¹' B₀),
      hC₁.image (by fun_prop), ?_⟩
    rintro g ⟨hgD, hgU⟩
    obtain ⟨q', hq', p', hp', e'⟩ := hDc hgD
    have hxu : x * ((q₀ * x)⁻¹ * g * p₀⁻¹) ∈ dcos Q P x := by
      refine ⟨q₀⁻¹ * q', Q.mul_mem (Q.inv_mem hq₀) hq', p' * p₀⁻¹, P.mul_mem hp' (P.inv_mem hp₀), ?_⟩
      rw [e']; group
    obtain ⟨s, hs, -, p₂, hp₂, hp₂B, e₂⟩ := hsec _ hgU hxu
    refine ⟨q₀ * s, Q.mul_mem hq₀ hs, ⟨p₂, hp₂⟩ * ⟨p₀, hp₀⟩, ⟨⟨p₂, hp₂⟩, hp₂B, rfl⟩, ?_⟩
    have e₃ : g = q₀ * (x * ((q₀ * x)⁻¹ * g * p₀⁻¹)) * p₀ := by group
    rw [e₃, e₂]
    simp [mul_assoc]

end GlobalTheory.CompanionTheory.BZRes
