import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLinearPartRingHom
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

/- English proof (translation)
Introduce `R _ d O _ _ B`. Take `⟨ρ, h⟩` from `GlobalTheory.ChF.linPart_act_ringHom R d B.G O B.A R (RingHom.id R)`. Use `⟨ρ, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[(h a).2]`. Use extensionality with `i j`.

Both sides reduce to the same expression.
-/
theorem rho_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  intro R _ d O _ _ B
  obtain ⟨ρ, h⟩ := GlobalTheory.ChF.linPart_act_ringHom R d B.G O B.A R (RingHom.id R)
  refine ⟨ρ, fun a => ?_⟩
  rw [(h a).2]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.Ar.Conj
