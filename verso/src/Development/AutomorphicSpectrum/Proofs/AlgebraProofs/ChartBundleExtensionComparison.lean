import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Imports
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundle
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ _ ι _ x N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hQ`. Take `⟨Γ, Δ, hΓ, hΔ, hX⟩` from `hQ`. Take `⟨F, hF⟩ : ∃ F : (∀ k, ι k) → AddSubgroup V, F = fun s => (Δ s).comap (AddMonoidHom.inl V V₂)` from `⟨_, rfl⟩`. Establish `memF : ∀ s b, b ∈ F s ↔ (b, (0 : V₂)) ∈ Δ s`. Introduce `s b`.

Substitute `hF` using the available equality. Conclude with `Iff.rfl`. Establish `hFlat : IsLatFamily O x F`. Use `⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩` and prove the remaining obligations. Establish `h` using `hΔ.1.1 s hs a ha (v, 0) ((memF s v).1 hv)`.

Rewrite using `[memF]`. Simplify using `using h`. Take `⟨m, hm⟩` from `hΔ.1.2 s t hs ht (v, 0) ((memF s v).1 hv)`. Use `⟨m, ?_⟩` and prove the remaining obligations. Rewrite using `[memF]`.

Simplify using `using hm`. Establish `hFfree : ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (F s)`. Introduce `s hs`. Establish `hE` using `((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N V).2 E).2 s hs`. Establish `hC` using `((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₂ V₂).2 C).2 s hs`.

Establish `hC'` using `((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₂ V₂).2 C').2 s hs`. Establish `h` using `(GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main (chartRing O (mseg x) s) N N₂ (E.lat s) (C.lat s) (C'.lat s) (Δ s) hE hC hC' (fun a ha v hv => hΔ.1.1 s hs a ha v hv) (fun v w h => (hΔ.2 s hs).1 v w h) (fun v hv => (hΔ.2 s hs).2.1 v hv) (fun w => (hΔ.2 s hs).2.2.1 w) (fu …`. Rewrite using `[hF]`. Conclude with `h`. Take `⟨E'', hE''⟩` from `(GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N V).1 F hFlat hFfree`.

Establish `memE'' : ∀ s, mseg x s ≠ 0 → ∀ b, b ∈ E''.lat s ↔ (b, (0 : V₂)) ∈ Δ s`. Introduce `s hs b`. Rewrite using `[hE'' s hs, memF]`. Use `⟨E'', fun s hs b hb => ?_, fun s hs b hb => ?_, ⟨Γ, ⟨hΓ.1, fun s hs => ⟨fun v w h => ⟨((hΓ.2 s hs).1 v w h).1, (memE'' s hs w).2 (((hX s hs).2.2 w).2 ⟨v, h⟩)⟩, (hΓ.2 s hs).2.1, (hΓ.2 s hs).2.2.1, (hΓ.2 s hs).2.2.2⟩⟩, fun s hs => ⟨(hX s hs).1, fun w hw => ((hX s hs).2.2 w).1 ((mem …` and prove the remaining obligations. Conclude with `(memE'' s hs b).2 ((hΔ.2 s hs).2.2.2 b hb)`.

Conclude with `((hΔ.2 s hs).1 b 0 ((memE'' s hs b).1 hb)).1`.
-/
theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : (∀ k, ι k) → AddSubgroup V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), QuotExact O x A A' E.lat E'.lat C.lat C'.lat → ∃ E'' : ChartBundle O (mseg x) N V, LatLE O x E' E'' ∧ LatLE O x E'' E ∧ QuotEquiv O x A A' E''.lat E'.lat ∧ QuotEquiv O x E.lat E''.lat C.lat C'.lat := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hQ
  obtain ⟨Γ, Δ, hΓ, hΔ, hX⟩ := hQ
  obtain ⟨F, hF⟩ : ∃ F : (∀ k, ι k) → AddSubgroup V,
      F = fun s => (Δ s).comap (AddMonoidHom.inl V V₂) := ⟨_, rfl⟩
  have memF : ∀ s b, b ∈ F s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s b
    subst hF
    exact Iff.rfl
  have hFlat : IsLatFamily O x F := by
    refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
    · have h := hΔ.1.1 s hs a ha (v, 0) ((memF s v).1 hv)
      rw [memF]
      simpa using h
    · obtain ⟨m, hm⟩ := hΔ.1.2 s t hs ht (v, 0) ((memF s v).1 hv)
      refine ⟨m, ?_⟩
      rw [memF]
      simpa using hm
  have hFfree : ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (F s) := by
    intro s hs
    have hE := ((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N V).2 E).2 s hs
    have hC := ((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₂ V₂).2 C).2 s hs
    have hC' := ((GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N₂ V₂).2 C').2 s hs
    have h := (GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main (chartRing O (mseg x) s) N N₂ (E.lat s) (C.lat s)
      (C'.lat s) (Δ s) hE hC hC' (fun a ha v hv => hΔ.1.1 s hs a ha v hv)
      (fun v w h => (hΔ.2 s hs).1 v w h) (fun v hv => (hΔ.2 s hs).2.1 v hv)
      (fun w => (hΔ.2 s hs).2.2.1 w) (fun w hw => (hX s hs).2.1 w hw)).2
    rw [hF]
    exact h
  obtain ⟨E'', hE''⟩ := (GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily.main O Ω K ι x N V).1 F hFlat hFfree
  have memE'' : ∀ s, mseg x s ≠ 0 → ∀ b, b ∈ E''.lat s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s hs b
    rw [hE'' s hs, memF]
  refine ⟨E'', fun s hs b hb => ?_, fun s hs b hb => ?_,
    ⟨Γ, ⟨hΓ.1, fun s hs => ⟨fun v w h => ⟨((hΓ.2 s hs).1 v w h).1,
        (memE'' s hs w).2 (((hX s hs).2.2 w).2 ⟨v, h⟩)⟩,
      (hΓ.2 s hs).2.1, (hΓ.2 s hs).2.2.1, (hΓ.2 s hs).2.2.2⟩⟩,
      fun s hs => ⟨(hX s hs).1, fun w hw => ((hX s hs).2.2 w).1 ((memE'' s hs w).1 hw)⟩⟩,
    ⟨Δ, ⟨hΔ.1, fun s hs => ⟨(hΔ.2 s hs).1, (hΔ.2 s hs).2.1, (hΔ.2 s hs).2.2.1,
        fun v hv => (memE'' s hs v).1 hv⟩⟩,
      fun s hs => ⟨fun v hv => (memE'' s hs v).2 hv, (hX s hs).2.1⟩⟩⟩
  · exact (memE'' s hs b).2 ((hΔ.2 s hs).2.2.2 b hb)
  · exact ((hΔ.2 s hs).1 b 0 ((memE'' s hs b).1 hb)).1

end GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle
