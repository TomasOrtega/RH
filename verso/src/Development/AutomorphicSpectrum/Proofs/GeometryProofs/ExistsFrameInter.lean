import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.InterFrame

/- English proof (translation)
Introduce `X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p r 𝓗 σ v x hst hv hsp _`. Establish `hrange : LinearMap.range (HT.eigProj ρ σ) = HT.eigSp ρ σ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `HT.LatBasic.eigProj_mem ρ σ w`.

Introduce `w hw`. Conclude with `⟨w, HT.LatBasic.eigProj_of_mem hw⟩`. Establish `hidem : HT.eigProj ρ σ ∘ₗ HT.eigProj ρ σ = HT.eigProj ρ σ` using `LinearMap.ext fun w => HT.LatBasic.eigProj_of_mem (HT.LatBasic.eigProj_mem ρ σ w)`. Establish `hVB : L.IsVBOn {x} (Module.finrank Ω V) ⊤` using `fun q _ => by`. Take `⟨U, hU, b, hb, h⟩` from `𝓗.vb q trivial`.

Conclude with `⟨U, hU, b, hb, fun q' _ hq' => h q' trivial hq'⟩`. Establish `h` using `EigSplit.isVBOn_inter_range L {x} _ (HT.eigProj ρ σ) hidem hVB (fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hst)`. Rewrite `h` using `[hrange]`. Take `⟨U, hU, f, hf, hfr⟩` from `h x rfl`. Establish `hfx` using `hfr x rfl hU`.

Establish `hn : Module.finrank Ω (HT.eigSp ρ σ) = p`. Rewrite using `[← hsp, finrank_span_eq_card hv, Fintype.card_fin]`. Substitute `hn` using the available equality. Establish `hmem : ∀ i, f i ∈ Submodule.span Ω (Set.range v)` using `fun i => by`. Rewrite using `[hsp, ← hf]`.

Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Use `choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hmem i)`. Use `⟨Matrix.of P, ?_⟩` and prove the remaining obligations. Simplify `hfx` using `only [Matrix.of_apply, hP]`.
-/
theorem exists_frame_inter : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (v : Fin p → V) (x : Cpt ξ), (∀ z ∈ L x, HT.eigProj ρ σ z ∈ L x) → LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → (∃ (n : ℕ) (b : Fin n → V), L.IsFrameAt b x) → ∃ P : Matrix (Fin p) (Fin p) Ω, (L.inter (HT.eigSp ρ σ)).IsFrameAt (fun i => ∑ j, P i j • v j) x := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p r 𝓗 σ v x hst hv hsp _
  have hrange : LinearMap.range (HT.eigProj ρ σ) = HT.eigSp ρ σ := by
    apply le_antisymm
    · rintro _ ⟨w, rfl⟩
      exact HT.LatBasic.eigProj_mem ρ σ w
    · intro w hw
      exact ⟨w, HT.LatBasic.eigProj_of_mem hw⟩
  have hidem : HT.eigProj ρ σ ∘ₗ HT.eigProj ρ σ = HT.eigProj ρ σ :=
    LinearMap.ext fun w => HT.LatBasic.eigProj_of_mem (HT.LatBasic.eigProj_mem ρ σ w)
  have hVB : L.IsVBOn {x} (Module.finrank Ω V) ⊤ := fun q _ => by
    obtain ⟨U, hU, b, hb, h⟩ := 𝓗.vb q trivial
    exact ⟨U, hU, b, hb, fun q' _ hq' => h q' trivial hq'⟩
  have h := EigSplit.isVBOn_inter_range L {x} _ (HT.eigProj ρ σ) hidem hVB
    (fun q hq => by rw [Set.mem_singleton_iff.1 hq]; exact hst)
  rw [hrange] at h
  obtain ⟨U, hU, f, hf, hfr⟩ := h x rfl
  have hfx := hfr x rfl hU
  have hn : Module.finrank Ω (HT.eigSp ρ σ) = p := by
    rw [← hsp, finrank_span_eq_card hv, Fintype.card_fin]
  subst hn
  have hmem : ∀ i, f i ∈ Submodule.span Ω (Set.range v) := fun i => by
    rw [hsp, ← hf]
    exact Submodule.subset_span ⟨i, rfl⟩
  choose P hP using fun i => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hmem i)
  refine ⟨Matrix.of P, ?_⟩
  simpa only [Matrix.of_apply, hP] using hfx

end GlobalTheory.CompanionTheory.Ar.Flat.InterFrame
