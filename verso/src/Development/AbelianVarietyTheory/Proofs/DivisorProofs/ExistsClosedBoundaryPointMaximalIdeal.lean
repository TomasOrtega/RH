import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageOfClosedPoint

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

namespace GlobalTheory.BoundaryPoint

/- English proof (translation)
Establish `e` using `hU.fromSpec_primeIdealOf ⟨x, hx⟩`. Establish `hle : m ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal` using `fun f hf => by`. Assume the negation of the conclusion as `hc`. Use `h f hf ?_` and prove the remaining obligations. Establish `h₁ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f`.

Rewrite using `[hU.fromSpec_preimage_basicOpen]`. Conclude with `hc`. Establish `h₂ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f` using `h₁`. Rewrite `h₂` using `[e]`. Then use the resulting hypothesis. Establish `hmax : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal` using `hm.eq_of_le (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top hle ▸ hm`.

Establish `hc` using `(PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmax`. Establish `h₃ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹' closedPoints X`. Rewrite using `[hU.fromSpec.isOpenEmbedding.preimage_closedPoints]`. Conclude with `hc`. Establish `h₄ : IsClosed ({hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)} : Set X)` using `h₃`.

Rewrite `h₄` using `[e]`. Then use the resulting hypothesis.
-/
theorem isClosed_of_isMaximal {X : Scheme.{0}} [JacobsonSpace X] {U : X.Opens} (hU : IsAffineOpen U)
    {m : Ideal Γ(X, U)} (hm : m.IsMaximal) {x : X} (hx : x ∈ U) (h : ∀ f ∈ m, x ∉ X.basicOpen f) :
    IsClosed ({x} : Set X) := by
  have e := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have hle : m ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := fun f hf => by
    by_contra hc
    refine h f hf ?_
    have h₁ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact hc
    have h₂ : hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := h₁
    rwa [e] at h₂
  have hmax : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.IsMaximal :=
    hm.eq_of_le (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top hle ▸ hm
  have hc := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hmax
  have h₃ : hU.primeIdealOf ⟨x, hx⟩ ∈ hU.fromSpec ⁻¹' closedPoints X := by
    rw [hU.fromSpec.isOpenEmbedding.preimage_closedPoints]
    exact hc
  have h₄ : IsClosed ({hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩)} : Set X) := h₃
  rwa [e] at h₄

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c Y hs U m hm x hx hU h`. Establish `hi : IsIso (genι Y)` using `GlobalTheory.LogKS.isIso_fst Y`. Establish `: Smooth (genStr Y)` using `SmoothOfRelativeDimension.smooth Dw.dim _`. Establish `: JacobsonSpace Y.X` using `LocallyOfFiniteType.jacobsonSpace (inv (genι Y) ≫ genStr Y)`. Establish `hc` using `isClosed_of_isMaximal U.2 hm hU h`.

Take `⟨x', rfl⟩` from `(genι Y).homeomorph.surjective x`. Use `⟨x', rfl, mem_genBd_iff.2 fun h' => hx ?_, ?_⟩` and prove the remaining obligations. Rewrite `h'` using `[← coe_interior]`. Conclude with `h'`. Rewrite using `[← (genι Y).homeomorph.isClosed_image, Set.image_singleton]`.

Conclude with `hc`.
-/
theorem exists_closed_boundary_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U : Y.X.affineOpens) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → ∃ x' : gen Y, genι Y x' = x ∧ x' ∈ genBd Y ∧ IsClosed ({x'} : Set (gen Y)) := by
  intro E _ _ _ H Dw l Xo c Y hs U m hm x hx hU h
  have hi : IsIso (genι Y) := GlobalTheory.LogKS.isIso_fst Y
  have : Smooth (genStr Y) := SmoothOfRelativeDimension.smooth Dw.dim _
  have : JacobsonSpace Y.X := LocallyOfFiniteType.jacobsonSpace (inv (genι Y) ≫ genStr Y)
  have hc := isClosed_of_isMaximal U.2 hm hU h
  obtain ⟨x', rfl⟩ := (genι Y).homeomorph.surjective x
  refine ⟨x', rfl, mem_genBd_iff.2 fun h' => hx ?_, ?_⟩
  · rw [← coe_interior] at h'
    exact h'
  · rw [← (genι Y).homeomorph.isClosed_image, Set.image_singleton]
    exact hc

end GlobalTheory.BoundaryPoint
