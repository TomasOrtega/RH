import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermStalkClosedPointToBaseChange

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `X Ω _ ξ X' Ω' _ ξ' f i E E' _ _ _ _ j hD hj L r b p' h hli hb`. Take `⟨h', hreg, -⟩` from `pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hD p'`. Use `⟨hli, ?_⟩` and prove the remaining obligations. Rewrite using `[Lat.pull_apply L hD]`. Establish `hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) (Set.range b)` using `hb.2`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨e, he, rfl⟩`. Establish `he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) (Set.range b)`. Rewrite using `[← hL]`.

Conclude with `he`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 he'`. Use `(Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun k => ⟨i (c k), hreg _ (c k).2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => (hj (c k) (b k)).symm`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Use `Submodule.subset_span ⟨b k, ?_, rfl⟩` and prove the remaining obligations. Use `show b k ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set E)`. Rewrite using `[hL]`.

Conclude with `Submodule.subset_span ⟨k, rfl⟩`.
-/
theorem Lat.pull_isFrameAt_comp : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (E E' : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E'] [Module Ω' E'] (j : E →+ E'), Dominates ξ' ξ f i → (∀ (a : Ω) (e : E), j (a • e) = i a • j e) → ∀ (L : Lat ξ E) (r : ℕ) (b : Fin r → E) (p' : Cpt ξ') (h : genPt ξ ⤳ f p'.1), LinearIndependent Ω' (fun k => j (b k)) → L.IsFrameAt b ⟨f p'.1, h⟩ → (L.pull ξ' f j).IsFrameAt (fun k => j (b k)) p' := by
  intro X Ω _ ξ X' Ω' _ ξ' f i E E' _ _ _ _ j hD hj L r b p' h hli hb
  obtain ⟨h', hreg, -⟩ := pull_reg_and_gen X Ω ξ X' Ω' ξ' f i hD p'
  refine ⟨hli, ?_⟩
  rw [Lat.pull_apply L hD]
  have hL : L ⟨f p'.1, hD.specializes p'⟩ = Submodule.span (regAt ξ ⟨f p'.1, h⟩) (Set.range b) := hb.2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ Submodule.span (regAt ξ ⟨f p'.1, h⟩) (Set.range b) := by
      rw [← hL]; exact he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun k => ⟨i (c k), hreg _ (c k).2⟩, ?_⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => (hj (c k) (b k)).symm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine Submodule.subset_span ⟨b k, ?_, rfl⟩
    show b k ∈ (L ⟨f p'.1, hD.specializes p'⟩ : Set E)
    rw [hL]
    exact Submodule.subset_span ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Flat
