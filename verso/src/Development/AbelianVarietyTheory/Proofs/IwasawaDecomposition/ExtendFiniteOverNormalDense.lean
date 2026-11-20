import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory

/- English proof (translation)
Introduce `T P Q p a V a₀ hp hn hln hd h`. Use `GlobalTheory.IsNormalScheme.of_pred hn` as an intermediate fact. Establish `: IsDominant V.ι` using `⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hd⟩`. Establish `: IsIntegralHom p` using `inferInstance`. Take `⟨c, ⟨h1, h2⟩, -⟩` from `existsUnique_lift_of_isOpenImmersion_of_isDominant V.ι p a₀ a h`.

Conclude with `⟨c, h2, h1⟩`.
-/
theorem exists_lift_of_isFinite_of_dense_opens :
    ∀ (T P Q : Scheme.{0}) (p : P ⟶ Q) (a : T ⟶ Q) (V : T.Opens) (a₀ : V.toScheme ⟶ P), IsFinite p →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → IsLocallyNoetherian T → Dense (V : Set T) → a₀ ≫ p = V.ι ≫ a →
    ∃ a' : T ⟶ P, a' ≫ p = a ∧ V.ι ≫ a' = a₀ := by
  intro T P Q p a V a₀ hp hn hln hd h
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsDominant V.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact hd⟩
  have : IsIntegralHom p := inferInstance
  obtain ⟨c, ⟨h1, h2⟩, -⟩ := existsUnique_lift_of_isOpenImmersion_of_isDominant V.ι p a₀ a h
  exact ⟨c, h2, h1⟩

end GlobalTheory
