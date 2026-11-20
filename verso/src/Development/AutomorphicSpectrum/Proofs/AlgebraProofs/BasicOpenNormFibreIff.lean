import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.PrimesToPts

/- English proof (translation)
Rewrite using `[← Scheme.isoSpec_hom]`. Use `⟨fun a b h => ?_, fun y => ⟨X.isoSpec.inv y, Scheme.inv_hom_apply _ _⟩⟩` and prove the remaining obligations. Establish `h'` using `congrArg X.isoSpec.inv h`. Rewrite `h'` using `[Scheme.hom_inv_apply, Scheme.hom_inv_apply]`. Then use the resulting hypothesis.
-/
private theorem to_spec_gamma_bijective (X : Scheme.{0}) [IsAffine X] : Function.Bijective X.toSpecΓ := by
  rw [← Scheme.isoSpec_hom]
  refine ⟨fun a b h => ?_, fun y => ⟨X.isoSpec.inv y, Scheme.inv_hom_apply _ _⟩⟩
  have h' := congrArg X.isoSpec.inv h
  rwa [Scheme.hom_inv_apply, Scheme.hom_inv_apply] at h'

/- English proof (translation)
Rewrite using `[← X.toSpecΓ_preimage_basicOpen f]`. Conclude with `Iff.rfl`.
-/
theorem mem_basicOpen_iff_toSpecΓ {X : Scheme.{0}} (f : Γ(X, ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ f ∉ (X.toSpecΓ x : PrimeSpectrum Γ(X, ⊤)).asIdeal := by
  rw [← X.toSpecΓ_preimage_basicOpen f]
  exact Iff.rfl

/- English proof (translation)
Establish `h : D.toSpecΓ (v z) = Spec.map v.appTop (P.toSpecΓ z)`. Rewrite using `[← Scheme.Hom.comp_apply, Scheme.toSpecΓ_naturality, Scheme.Hom.comp_apply]`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem comap_toSpecΓ {P D : Scheme.{0}} (v : P ⟶ D) (z : P) :
    (P.toSpecΓ z : PrimeSpectrum Γ(P, ⊤)).asIdeal.comap v.appTop.hom =
      (D.toSpecΓ (v z) : PrimeSpectrum Γ(D, ⊤)).asIdeal := by
  have h : D.toSpecΓ (v z) = Spec.map v.appTop (P.toSpecΓ z) := by
    rw [← Scheme.Hom.comp_apply, Scheme.toSpecΓ_naturality, Scheme.Hom.comp_apply]
  rw [h]
  rfl

/- English proof (translation)
Introduce `P D _ _ v N e hN y`. Use `(GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ N y).trans ((hN (D.toSpecΓ y)).trans ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `H z hz`. Use `(GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ e z).2 (H _ ?_)` and prove the remaining obligations.

Conclude with `(GlobalTheory.CompanionTheory.PrimesToPts.comap_toSpecΓ v z).trans (by rw [hz])`. Introduce `H q hq`. Take `⟨z, rfl⟩` from `(to_spec_gamma_bijective P).2 q`. Establish `hz : v z = y`. Apply `(to_spec_gamma_bijective D).1` to reduce the goal to its premises.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Conclude with `(GlobalTheory.CompanionTheory.PrimesToPts.comap_toSpecΓ v z).symm.trans hq`. Conclude with `(GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ e z).1 (H z hz)`.
-/
theorem primes_to_pts : ∀ {P D : Scheme.{0}} [IsAffine P] [IsAffine D] (v : P ⟶ D) (N : Γ(D, ⊤)) (e : Γ(P, ⊤)), (∀ p : PrimeSpectrum Γ(D, ⊤), N ∉ p.asIdeal ↔ ∀ q : PrimeSpectrum Γ(P, ⊤), q.asIdeal.comap v.appTop.hom = p.asIdeal → e ∉ q.asIdeal) → ∀ y : D, y ∈ D.basicOpen N ↔ ∀ z : P, v z = y → z ∈ P.basicOpen e := by
  intro P D _ _ v N e hN y
  refine (GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ N y).trans ((hN (D.toSpecΓ y)).trans ?_)
  constructor
  · intro H z hz
    refine (GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ e z).2 (H _ ?_)
    exact (GlobalTheory.CompanionTheory.PrimesToPts.comap_toSpecΓ v z).trans (by rw [hz])
  · intro H q hq
    obtain ⟨z, rfl⟩ := (to_spec_gamma_bijective P).2 q
    have hz : v z = y := by
      apply (to_spec_gamma_bijective D).1
      apply PrimeSpectrum.ext
      exact (GlobalTheory.CompanionTheory.PrimesToPts.comap_toSpecΓ v z).symm.trans hq
    exact (GlobalTheory.CompanionTheory.PrimesToPts.mem_basicOpen_iff_toSpecΓ e z).1 (H z hz)

end GlobalTheory.CompanionTheory.PrimesToPts
