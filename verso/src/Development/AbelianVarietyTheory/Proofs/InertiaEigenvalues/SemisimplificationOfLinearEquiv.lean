import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

/- English proof (translation)
Introduce `k Γ _ _ W _ _ _ W' _ _ _ V _ _ _ s s' ρ e he h`. Take `⟨hss, m, Ws, f, hst, hint, hfil⟩` from `h`. Set `o : Submodule k W' ≃o Submodule k W` to `Submodule.orderIsoMapComap e.symm`. Establish `ho : ∀ (U : Submodule k W') (v : W), v ∈ o U ↔ e v ∈ U`. Introduce `U v`.

Express the relevant statement in the definitionally equal form `v ∈ U.map (e.symm : W' →ₗ[k] W) ↔ _`. Rewrite using `[Submodule.mem_map_equiv]`. Simplify using the standard rewrite rules. Establish `ho' : ∀ (U : Submodule k W) (v : W), e v ∈ o.symm U ↔ v ∈ U`. Introduce `U v`.

Rewrite using `[← ho, o.apply_symm_apply]`. Establish `hstab : ∀ U, Stable s' U → Stable s (o U)`. Introduce `U hU g v hv`. Rewrite `hv`, the goal using `[ho]`. Rewrite using `[he]`.

Conclude with `hU g _ hv`. Use `⟨?_, m, fun j => o (Ws j), e.trans f, fun j => hstab _ (hst j), ?_, ?_⟩` and prove the remaining obligations. Introduce `U hU`. Establish `hU' : Stable s' (o.symm U)`. Introduce `g w hw`.

Take `⟨v, rfl⟩` from `e.surjective w`. Rewrite using `[← he, ho']`. Conclude with `hU g v ((ho' U v).1 hw)`. Take `⟨U', h1, h2⟩` from `hss _ hU'`. Use `⟨o U', hstab _ h1, ?_⟩` and prove the remaining obligations.

Use `o.isCompl h2` as an intermediate fact. Rewrite `this` using `[o.apply_symm_apply]`. Then use the resulting hypothesis. Rewrite `hint`, the goal using `[DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]`. Use `⟨iSupIndep.map_orderIso o hint.1, ?_⟩` and prove the remaining obligations. Rewrite using `[← o.map_iSup, hint.2, o.map_top]`.

Introduce `j g v hv`. Rewrite `hv` using `[ho]`. Take `⟨w, hw, hw'⟩` from `hfil j g _ hv`. Use `⟨e.symm w, ?_, ?_⟩` and prove the remaining obligations. Establish `: (⨆ j' ∈ Set.Iio j, o (Ws j')) = o (⨆ j' ∈ Set.Iio j, Ws j')`.

Simplify using `only [o.map_iSup]`. Express the relevant statement in the definitionally equal form `e.symm w ∈ (⨆ j' ∈ Set.Iio j, o (Ws j'))`. Rewrite using `[this, ho]`. Simplify using `using hw`. Simplify `hw'` using `[he]`.
-/
theorem isSemisimplificationOf_of_equiv : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {W' : Type} [AddCommGroup W'] [Module k W'] [FiniteDimensional k W'] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ W') (ρ : Representation k Γ V) (e : W ≃ₗ[k] W'), (∀ g v, e (s g v) = s' g (e v)) → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s' ρ → GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ := by
  intro k Γ _ _ W _ _ _ W' _ _ _ V _ _ _ s s' ρ e he h
  obtain ⟨hss, m, Ws, f, hst, hint, hfil⟩ := h
  let o : Submodule k W' ≃o Submodule k W := Submodule.orderIsoMapComap e.symm
  have ho : ∀ (U : Submodule k W') (v : W), v ∈ o U ↔ e v ∈ U := by
    intro U v
    change v ∈ U.map (e.symm : W' →ₗ[k] W) ↔ _
    rw [Submodule.mem_map_equiv]
    simp
  have ho' : ∀ (U : Submodule k W) (v : W), e v ∈ o.symm U ↔ v ∈ U := by
    intro U v
    rw [← ho, o.apply_symm_apply]
  have hstab : ∀ U, Stable s' U → Stable s (o U) := by
    intro U hU g v hv
    rw [ho] at hv ⊢
    rw [he]
    exact hU g _ hv
  refine ⟨?_, m, fun j => o (Ws j), e.trans f, fun j => hstab _ (hst j), ?_, ?_⟩
  · intro U hU
    have hU' : Stable s' (o.symm U) := by
      intro g w hw
      obtain ⟨v, rfl⟩ := e.surjective w
      rw [← he, ho']
      exact hU g v ((ho' U v).1 hw)
    obtain ⟨U', h1, h2⟩ := hss _ hU'
    refine ⟨o U', hstab _ h1, ?_⟩
    have := o.isCompl h2
    rwa [o.apply_symm_apply] at this
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
    refine ⟨iSupIndep.map_orderIso o hint.1, ?_⟩
    rw [← o.map_iSup, hint.2, o.map_top]
  · intro j g v hv
    rw [ho] at hv
    obtain ⟨w, hw, hw'⟩ := hfil j g _ hv
    refine ⟨e.symm w, ?_, ?_⟩
    · have : (⨆ j' ∈ Set.Iio j, o (Ws j')) = o (⨆ j' ∈ Set.Iio j, Ws j') := by
        simp only [o.map_iSup]
      change e.symm w ∈ (⨆ j' ∈ Set.Iio j, o (Ws j'))
      rw [this, ho]
      simpa using hw
    · simpa [he] using hw'

end GlobalTheory
