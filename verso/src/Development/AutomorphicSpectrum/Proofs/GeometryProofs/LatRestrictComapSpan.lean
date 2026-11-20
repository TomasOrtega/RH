import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Establish `h : (Set.range fun i => (b i : E)) = (V.subtype.restrictScalars R) '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h, ← Submodule.map_span, Submodule.comap_map_eq_of_injective]`. Conclude with `Subtype.val_injective`.
-/
theorem lat_restrict_comap_span {Ω R E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [Semiring R] [SMul R Ω]
    [Module R E] [IsScalarTower R Ω E] (V : Submodule Ω E) {r : ℕ} (b : Fin r → V) :
    (Submodule.span R (Set.range fun i => (b i : E))).comap (V.subtype.restrictScalars R) =
      Submodule.span R (Set.range b) := by
  have h : (Set.range fun i => (b i : E)) = (V.subtype.restrictScalars R) '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Submodule.map_span, Submodule.comap_map_eq_of_injective]
  exact Subtype.val_injective

/- English proof (translation)
Introduce `X Ω _ ξ E _ _ L T r V h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Take `⟨U, hpU, b, hb, hq⟩` from `h p hp`. Establish `hbV : ∀ i, b i ∈ V` using `fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩`.

Set `b' : Fin r → V` to `fun i => ⟨b i, hbV i⟩`. Establish `hval : (fun i => (b' i : E)) = b` using `rfl`. Use `⟨U, hpU, b', ?_, ?_⟩` and prove the remaining obligations. Apply `Submodule.map_injective_of_injective (f := V.subtype) Subtype.val_injective` to reduce the goal to its premises. Establish `h1 : (Set.range b) = V.subtype '' Set.range b'`.

Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[Submodule.map_span, ← h1, hb, Submodule.map_top, Submodule.range_subtype]`. Introduce `q hqT hqU`. Take `⟨hli, hsp⟩` from `hq q hqT hqU`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `LinearIndependent.of_comp V.subtype hli`. Use `show (L q).comap (V.subtype.restrictScalars (regAt ξ q)) = _`. Rewrite using `[hsp, ← hval]`. Conclude with `lat_restrict_comap_span V b'`.

Introduce `p hp`. Take `⟨U, hpU, b, hb, hq⟩` from `h p hp`. Take `⟨_, hsp⟩` from `hq p hp hpU`. Establish `hle : ∀ e ∈ L p, e ∈ V`. Introduce `e he`.

Rewrite `he` using `[hsp]`. Establish `: Submodule.span (regAt ξ p) (Set.range b) ≤ V.restrictScalars (regAt ξ p)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hb ▸ Submodule.subset_span ⟨i, rfl⟩`.

Conclude with `this he`. Use `show ((L p).comap (V.subtype.restrictScalars (regAt ξ p))).map (V.subtype.restrictScalars (regAt ξ p)) = L p`. Use extensionality with `e`. Simplify using `only [Submodule.mem_map, Submodule.mem_comap]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨v, hv, rfl⟩`. Conclude with `hv`. Introduce `he`. Conclude with `⟨⟨e, hle e he⟩, he, rfl⟩`.
-/
theorem Lat.restrict_isVBOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E),
    L.IsVBOn T r V → (L.comap V.subtype).IsVBOn T r ⊤ ∧
      ∀ p ∈ T, ((L.comap V.subtype).map V.subtype) p = L p := by
  intro X Ω _ ξ E _ _ L T r V h
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨U, hpU, b, hb, hq⟩ := h p hp
    have hbV : ∀ i, b i ∈ V := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
    let b' : Fin r → V := fun i => ⟨b i, hbV i⟩
    have hval : (fun i => (b' i : E)) = b := rfl
    refine ⟨U, hpU, b', ?_, ?_⟩
    · apply Submodule.map_injective_of_injective (f := V.subtype) Subtype.val_injective
      have h1 : (Set.range b) = V.subtype '' Set.range b' := by
        rw [← Set.range_comp]; rfl
      rw [Submodule.map_span, ← h1, hb, Submodule.map_top, Submodule.range_subtype]
    · intro q hqT hqU
      obtain ⟨hli, hsp⟩ := hq q hqT hqU
      refine ⟨?_, ?_⟩
      · exact LinearIndependent.of_comp V.subtype hli
      · show (L q).comap (V.subtype.restrictScalars (regAt ξ q)) = _
        rw [hsp, ← hval]
        exact lat_restrict_comap_span V b'
  · intro p hp
    obtain ⟨U, hpU, b, hb, hq⟩ := h p hp
    obtain ⟨_, hsp⟩ := hq p hp hpU
    have hle : ∀ e ∈ L p, e ∈ V := by
      intro e he
      rw [hsp] at he
      have : Submodule.span (regAt ξ p) (Set.range b) ≤ V.restrictScalars (regAt ξ p) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hb ▸ Submodule.subset_span ⟨i, rfl⟩
      exact this he
    show ((L p).comap (V.subtype.restrictScalars (regAt ξ p))).map (V.subtype.restrictScalars (regAt ξ p)) = L p
    ext e
    simp only [Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro he
      exact ⟨⟨e, hle e he⟩, he, rfl⟩

end GlobalTheory.CompanionTheory.Ar
