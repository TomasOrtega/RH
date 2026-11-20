import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `X U hU x hx hft p _ φ`. Use `letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩`. Establish `hloc` using `hU.isLocalization_stalk ⟨x, hx⟩`. Use `haveI : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing ℤ Γ(X, U)`. Use `⟨IsLocalization.isNoetherianRing (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ this, ?_⟩` and prove the remaining obligations.

Set `ψ : X.presheaf.stalk x →+* PadicAlgCl p` to `(OO p).subtype.comp φ`. Set `f : Γ(X, U) →+* PadicAlgCl p` to `ψ.comp (algebraMap Γ(X, U) (X.presheaf.stalk x))`. Take `⟨s, hs⟩` from `hft.out`. Set `K : IntermediateField ℚ_[p] (PadicAlgCl p)` to `IntermediateField.adjoin ℚ_[p] ((s.image f : Finset (PadicAlgCl p)) : Set (PadicAlgCl p))`. Use `⟨K, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `IntermediateField.finiteDimensional_adjoin (fun y _ => Algebra.IsIntegral.isIntegral y)`. Establish `hgen : ∀ r : Γ(X, U), f r ∈ K`. Introduce `r`. Establish `hr : r ∈ Algebra.adjoin ℤ (s : Set Γ(X, U))` using `by rw [hs]; trivial`. Proceed by induction on `hr using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Apply `IntermediateField.subset_adjoin` to reduce the goal to its premises. Simplify using `only [Finset.coe_image]`. Conclude with `Set.mem_image_of_mem f hy`. Consider the case `algebraMap n`.

Establish `: f (algebraMap ℤ Γ(X, U) n) = (n : PadicAlgCl p)` using `by simp`. Rewrite using `[this]`. Conclude with `K.intCast_mem n`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `K.add_mem ha hb`.

Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `K.mul_mem ha hb`. Introduce `a`. Take `⟨⟨r, t⟩, rfl⟩` from `IsLocalization.mk'_surjective (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl a`. Establish `hspec` using `IsLocalization.mk'_spec (X.presheaf.stalk x) r t`.

Establish `hunit : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) t)` using `IsLocalization.map_units _ t`. Establish `hne : f t ≠ 0` using `(hunit.map ψ).ne_zero`. Establish `heq : ψ (IsLocalization.mk' (X.presheaf.stalk x) r t) = f r * (f t)⁻¹`. Establish `h2` using `congrArg ψ hspec`. Rewrite `h2` using `[map_mul]`.

Express the relevant statement in the definitionally equal form `ψ _ * f t = f r at h2`. Rewrite using `[← h2, _root_.mul_assoc, mul_inv_cancel₀ hne, _root_.mul_one]`. Express the relevant statement in the definitionally equal form `ψ _ ∈ K`. Rewrite using `[heq]`. Conclude with `K.mul_mem (hgen r) (K.inv_mem (hgen t))`.
-/
theorem stalk_noetherian_and_finite_image :
    ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ x ∈ U, Algebra.FiniteType ℤ Γ(X, U) → ∀ (p : ℕ) [Fact p.Prime] (φ : X.presheaf.stalk x →+* OO p), IsNoetherianRing (X.presheaf.stalk x) ∧ ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ ∀ a, ((φ a : OO p) : PadicAlgCl p) ∈ K := by
  intro X U hU x hx hft p _ φ
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc := hU.isLocalization_stalk ⟨x, hx⟩
  haveI : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing ℤ Γ(X, U)
  refine ⟨IsLocalization.isNoetherianRing (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _ this, ?_⟩
  let ψ : X.presheaf.stalk x →+* PadicAlgCl p := (OO p).subtype.comp φ
  let f : Γ(X, U) →+* PadicAlgCl p := ψ.comp (algebraMap Γ(X, U) (X.presheaf.stalk x))
  obtain ⟨s, hs⟩ := hft.out
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) :=
    IntermediateField.adjoin ℚ_[p] ((s.image f : Finset (PadicAlgCl p)) : Set (PadicAlgCl p))
  refine ⟨K, ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin (fun y _ => Algebra.IsIntegral.isIntegral y)
  · have hgen : ∀ r : Γ(X, U), f r ∈ K := by
      intro r
      have hr : r ∈ Algebra.adjoin ℤ (s : Set Γ(X, U)) := by rw [hs]; trivial
      induction hr using Algebra.adjoin_induction with
      | mem y hy =>
        apply IntermediateField.subset_adjoin
        simp only [Finset.coe_image]
        exact Set.mem_image_of_mem f hy
      | algebraMap n =>
        have : f (algebraMap ℤ Γ(X, U) n) = (n : PadicAlgCl p) := by simp
        rw [this]; exact K.intCast_mem n
      | add a b _ _ ha hb => rw [map_add]; exact K.add_mem ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact K.mul_mem ha hb
    intro a
    obtain ⟨⟨r, t⟩, rfl⟩ := IsLocalization.mk'_surjective
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl a
    have hspec := IsLocalization.mk'_spec (X.presheaf.stalk x) r t
    have hunit : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) t) := IsLocalization.map_units _ t
    have hne : f t ≠ 0 := (hunit.map ψ).ne_zero
    have heq : ψ (IsLocalization.mk' (X.presheaf.stalk x) r t) =
        f r * (f t)⁻¹ := by
      have h2 := congrArg ψ hspec
      rw [map_mul] at h2
      change ψ _ * f t = f r at h2
      rw [← h2, _root_.mul_assoc, mul_inv_cancel₀ hne, _root_.mul_one]
    change ψ _ ∈ K
    rw [heq]
    exact K.mul_mem (hgen r) (K.inv_mem (hgen t))

end GlobalTheory
