import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SpecialFibreUnits
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier

namespace GlobalTheory.Hartogs

/- English proof (translation)
Introduce `X _ _ hN f x hreg`. Assume the negation of the conclusion as `hf`. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial`. Use `haveI : Nonempty U := ⟨⟨x, hx⟩⟩`. Use `haveI := isIntegrallyClosed_sections_of_stalks hN hU`.

Use `haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Use `haveI := functionField_isFractionRing_of_isAffineOpen X U hU`. Establish `key : ∀ y : U, RegAt (y : X) f ↔ ∃ s c : Γ(X, U), algebraMap _ X.functionField s * f = algebraMap _ X.functionField c ∧ s ∉ (hU.primeIdealOf y).asIdeal` using `fun y => haveI := hU.isLocalization_stalk y GlobalTheory.NormalPole.mem_range_iff (B := X.presheaf.stalk (y : X)) (hU.primeIdealOf y).asIdeal f`. Take `⟨p, hp, hpQ, h1, hpf⟩` from `GlobalTheory.NormalPole.exists_height_one f (hU.primeIdealOf ⟨x, hx⟩).asIdeal fun s c e => by_contra fun hs => hf ((key ⟨x, hx⟩).2 ⟨s, c, e, hs⟩)`. Set `P : PrimeSpectrum Γ(X, U)` to `⟨p, hp⟩`.

Establish `hz : hU.fromSpec P ∈ U`. Establish `: hU.fromSpec P ∈ Set.range hU.fromSpec` using `⟨P, rfl⟩`. Rewrite `this` using `[hU.range_fromSpec]`. Then use the resulting hypothesis. Set `z : U` to `⟨hU.fromSpec P, hz⟩`. Establish `hP : hU.primeIdealOf z = P` using `hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)`.

Establish `hzx : (z : X) ⤳ x`. Establish `h` using `((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hpQ).map hU.fromSpec.continuous`. Rewrite `h` using `[hU.fromSpec_primeIdealOf ⟨x, hx⟩]`. Then use the resulting hypothesis. Establish `hfz : ¬ RegAt (z : X) f` using `fun h => by`. Take `⟨s, c, e, hs⟩` from `(key z).1 h`.

Rewrite `hs` using `[hP]`. Conclude with `hs (hpf s c e)`. Use `clear_value z`. Use `haveI := hU.isLocalization_stalk z`. Use `haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) := isDiscreteValuationRing_of_height_eq_one (hU.primeIdealOf z).asIdeal (by rw [hP]; exact h1) _`.

Conclude with `hfz (hreg z hzx inferInstance)`.
-/
theorem regAt_of_forall_dvr : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X],
    (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
    ∀ (φ : X.functionField) (x : X),
      (∀ z : X, z ⤳ x → IsDiscreteValuationRing (X.presheaf.stalk z) → RegAt z φ) → RegAt x φ := by
  intro X _ _ hN f x hreg
  by_contra hf
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  haveI := isIntegrallyClosed_sections_of_stalks hN hU
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  have key : ∀ y : U, RegAt (y : X) f ↔ ∃ s c : Γ(X, U), algebraMap _ X.functionField s * f =
      algebraMap _ X.functionField c ∧ s ∉ (hU.primeIdealOf y).asIdeal := fun y =>
    haveI := hU.isLocalization_stalk y
    GlobalTheory.NormalPole.mem_range_iff (B := X.presheaf.stalk (y : X)) (hU.primeIdealOf y).asIdeal f
  obtain ⟨p, hp, hpQ, h1, hpf⟩ := GlobalTheory.NormalPole.exists_height_one f (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    fun s c e => by_contra fun hs => hf ((key ⟨x, hx⟩).2 ⟨s, c, e, hs⟩)
  let P : PrimeSpectrum Γ(X, U) := ⟨p, hp⟩
  have hz : hU.fromSpec P ∈ U := by
    have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rwa [hU.range_fromSpec] at this
  let z : U := ⟨hU.fromSpec P, hz⟩
  have hP : hU.primeIdealOf z = P :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
  have hzx : (z : X) ⤳ x := by
    have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hpQ).map
      hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
  have hfz : ¬ RegAt (z : X) f := fun h => by
    obtain ⟨s, c, e, hs⟩ := (key z).1 h
    rw [hP] at hs
    exact hs (hpf s c e)
  clear_value z
  haveI := hU.isLocalization_stalk z
  haveI : IsDiscreteValuationRing (X.presheaf.stalk (z : X)) :=
    isDiscreteValuationRing_of_height_eq_one (hU.primeIdealOf z).asIdeal (by rw [hP]; exact h1) _
  exact hfz (hreg z hzx inferInstance)

end GlobalTheory.Hartogs
