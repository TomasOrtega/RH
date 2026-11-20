import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.DOkBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

/- English proof (translation)
Introduce `E _ _ M _ _ _ _ I _ ℓ hℓ hcard`. Take `⟨b, hb⟩` from `GlobalTheory.CompanionTheory.Ar.Fl.exists_local_basis_cm_order.locBasis' (𝓞 E) ℓ hℓ (M := M)`. Set `e : I ≃ Fin (Module.finrank (𝓞 E) M)` to `Fintype.equivFinOfCardEq hcard`. Use `⟨b ∘ e, hb.1.comp e e.injective, ?_⟩` and prove the remaining obligations. Take `⟨n, hn, hsp⟩` from `hb.2`.

Use `⟨n, hn, fun y => ?_⟩` and prove the remaining obligations. Establish `: Set.range (b ∘ e) = Set.range b` using `e.surjective.range_comp b`. Rewrite using `[this]`. Conclude with `hsp y`.
-/
theorem exists_local_basis' : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.IsTorsionFree (𝓞 E) M] (I : Type) [Fintype I] (ℓ : ℕ), ℓ.Prime → Fintype.card I = Module.finrank (𝓞 E) M → ∃ x : I → M, IsLocBasis (𝓞 E) ℓ x := by
  intro E _ _ M _ _ _ _ I _ ℓ hℓ hcard
  obtain ⟨b, hb⟩ := GlobalTheory.CompanionTheory.Ar.Fl.exists_local_basis_cm_order.locBasis' (𝓞 E) ℓ hℓ (M := M)
  let e : I ≃ Fin (Module.finrank (𝓞 E) M) := Fintype.equivFinOfCardEq hcard
  refine ⟨b ∘ e, hb.1.comp e e.injective, ?_⟩
  obtain ⟨n, hn, hsp⟩ := hb.2
  refine ⟨n, hn, fun y => ?_⟩
  have : Set.range (b ∘ e) = Set.range b := e.surjective.range_comp b
  rw [this]
  exact hsp y

end PositivityTheory.Xgf
