import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

open Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

/- English proof (translation)
Unfold `FieldUnitBounded`. Introduce `F B _ _ _ _ _ τ hB hτ`. Take `⟨hTop, hLC, hT2, hSC, _hinj, hdisc, C, hC, hcov⟩` from `hT F B`. Set `: TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F)` to `Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)`. Use `hTop` as an intermediate fact.

Use `hLC` as an intermediate fact. Use `hT2` as an intermediate fact. Use `hSC` as an intermediate fact. Establish `: Nontrivial B` using `⟨hB.exists_pair_ne⟩`. Establish `: Infinite F` using `Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective`.

Establish `: Infinite B` using `Infinite.of_injective (algebraMap F B) (algebraMap F B).injective`. Establish `: NoncompactSpace (B ⊗[F] AdeleRing (𝓞 F) F)`. Use `⟨fun hU => ?_⟩` and prove the remaining obligations. Establish `hfin` using `hdisc Set.univ hU`. Simplify using `only [Set.mem_univ, Set.ofPred_true] at hfin`.

Conclude with `Set.infinite_univ hfin`. Establish `: Countable F` using `(Module.finBasis ℚ F).equivFun.injective.countable`. Establish `: Countable B` using `(Module.finBasis F B).equivFun.injective.countable`. Set `ι` to `inclE (F := F) (E := B) (AdeleRing (𝓞 F) F)`. Set `Λ : AddSubgroup (B ⊗[F] AdeleRing (𝓞 F) F)` to `ι.toAddMonoidHom.range`.

Establish `hΛ : Countable Λ`. Use `Function.Surjective.countable (f := fun b : B => (⟨ι b, b, rfl⟩ : Λ)) ?_` and prove the remaining obligations. Introduce and unpack `⟨y, b, rfl⟩`. Conclude with `⟨b, rfl⟩`. Establish `hcoc : ∃ C' : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact C' ∧ ∀ x, ∃ l ∈ Λ, x - l ∈ C'`.

Use `⟨C, hC, fun x => ?_⟩` and prove the remaining obligations. Take `⟨β, hβ⟩` from `hcov x`. Conclude with `⟨ι β, ⟨β, rfl⟩, hβ⟩`. Take `⟨D, hD, hDu⟩` from `hP (B ⊗[F] AdeleRing (𝓞 F) F) (sigR τ (AdeleRing (𝓞 F) F)) (continuous_sigR τ (AdeleRing (𝓞 F) F)) (sigR_sigR hτ (AdeleRing (𝓞 F) F)) Λ hΛ hcoc`. Use `⟨D, hD, fun u hu => ?_⟩` and prove the remaining obligations.

Take `⟨β, ⟨b, rfl⟩, hβ0, huβ⟩` from `hDu u hu`. Establish `hb : b ≠ 0`. Introduce and unpack `rfl`. Conclude with `hβ0 (map_zero ι)`. Take `⟨c, hc⟩` from `hB.mul_inv_cancel hb`.

Conclude with `⟨b, ⟨⟨b, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩, huβ⟩`.
-/
theorem fieldUnitBounded_of_packing (hP : NormOnePacking) (hT : TensorLattice) :
    FieldUnitBounded := by
  unfold FieldUnitBounded
  intro F B _ _ _ _ _ τ hB hτ

  obtain ⟨hTop, hLC, hT2, hSC, _hinj, hdisc, C, hC, hcov⟩ := hT F B
  let : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  have := hTop
  have := hLC
  have := hT2
  have := hSC

  have : Nontrivial B := ⟨hB.exists_pair_ne⟩
  have : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  have : Infinite B := Infinite.of_injective (algebraMap F B) (algebraMap F B).injective
  have : NoncompactSpace (B ⊗[F] AdeleRing (𝓞 F) F) := by
    refine ⟨fun hU => ?_⟩
    have hfin := hdisc Set.univ hU
    simp only [Set.mem_univ, Set.ofPred_true] at hfin
    exact Set.infinite_univ hfin

  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable B := (Module.finBasis F B).equivFun.injective.countable

  let ι := inclE (F := F) (E := B) (AdeleRing (𝓞 F) F)
  let Λ : AddSubgroup (B ⊗[F] AdeleRing (𝓞 F) F) := ι.toAddMonoidHom.range
  have hΛ : Countable Λ := by
    refine Function.Surjective.countable (f := fun b : B => (⟨ι b, b, rfl⟩ : Λ)) ?_
    rintro ⟨y, b, rfl⟩
    exact ⟨b, rfl⟩
  have hcoc : ∃ C' : Set (B ⊗[F] AdeleRing (𝓞 F) F), IsCompact C' ∧
      ∀ x, ∃ l ∈ Λ, x - l ∈ C' := by
    refine ⟨C, hC, fun x => ?_⟩
    obtain ⟨β, hβ⟩ := hcov x
    exact ⟨ι β, ⟨β, rfl⟩, hβ⟩

  obtain ⟨D, hD, hDu⟩ := hP (B ⊗[F] AdeleRing (𝓞 F) F) (sigR τ (AdeleRing (𝓞 F) F))
    (continuous_sigR τ (AdeleRing (𝓞 F) F)) (sigR_sigR hτ (AdeleRing (𝓞 F) F)) Λ hΛ hcoc
  refine ⟨D, hD, fun u hu => ?_⟩
  obtain ⟨β, ⟨b, rfl⟩, hβ0, huβ⟩ := hDu u hu

  have hb : b ≠ 0 := by
    rintro rfl
    exact hβ0 (map_zero ι)
  obtain ⟨c, hc⟩ := hB.mul_inv_cancel hb
  exact ⟨b, ⟨⟨b, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩, huβ⟩

end GlobalTheory.RegSS
