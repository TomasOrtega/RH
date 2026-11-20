import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

namespace GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver

/- English proof (translation)
Introduce `X _ Z U q h`. Take `⟨t, f, ht, hfI, hf0, hg⟩` from `h`. Establish `hx : U.2.fromSpec q ∈ X.basicOpen t`. Establish `h1 : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen t`. Rewrite using `[U.2.fromSpec_preimage_basicOpen]`.

Conclude with `ht`. Conclude with `h1`. Establish `hxU : U.2.fromSpec q ∈ U.1` using `X.basicOpen_le t hx`. Establish `inst` using `U.2.isLocalization_basicOpen t`. Set `ρ : Γ(X, U.1) →+* Γ(X, X.basicOpen t)` to `(X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom`.

Establish `hu : IsUnit (ρ t)` using `IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen t)) t`. Establish `hZ : Z.ideal (X.affineBasicOpen t) = Ideal.map ρ (Z.ideal U)` using `(Z.map_ideal_basicOpen U t).symm`. Establish `hne : Nonempty (X.basicOpen t : X.Opens)` using `⟨⟨_, hx⟩⟩`. Establish `hρf : ρ f ≠ 0`. Introduce `h0`.

Apply `hf0` to reduce the goal to its premises. Apply `germ_injective_of_isIntegral X (U := U.1) (U.2.fromSpec q) hxU` to reduce the goal to its premises. Establish `h2` using `congrArg (X.presheaf.germ (X.basicOpen t) (U.2.fromSpec q) hx).hom h0`. Rewrite `h2`, the goal using `[map_zero]`. Rewrite using `[← h2]`.

Simplify using `[ρ]`. Establish `hnz : ρ f ∈ nonZeroDivisors Γ(X, X.basicOpen t)` using `mem_nonZeroDivisors_of_ne_zero hρf`. It suffices to establish `hspan : Ideal.map ρ (Z.ideal U) = Ideal.span {ρ f} from ⟨X.affineBasicOpen t, ρ f, hx, hnz, hZ.trans hspan⟩`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `g hgI`. Take `⟨n, hn⟩` from `hg g hgI`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hn`. Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton']`. Take `⟨u, hu'⟩` from `hu.pow n`.

Use `⟨(↑u⁻¹ : Γ(X, X.basicOpen t)) * ρ c, ?_⟩` and prove the remaining obligations. Establish `h3 : ρ c * ρ f = ρ t ^ n * ρ g`. Rewrite using `[← map_mul, hc, map_mul, map_pow]`. Rewrite using `[mul_assoc, h3, ← hu', Units.inv_mul_cancel_left]`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`.

Conclude with `Ideal.mem_map_of_mem ρ hfI`.
-/
theorem cartAt_of_locPrincipal : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData)
    (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)),
    LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by
  intro X _ Z U q h
  obtain ⟨t, f, ht, hfI, hf0, hg⟩ := h
  have hx : U.2.fromSpec q ∈ X.basicOpen t := by
    have h1 : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen t := by
      rw [U.2.fromSpec_preimage_basicOpen]
      exact ht
    exact h1
  have hxU : U.2.fromSpec q ∈ U.1 := X.basicOpen_le t hx
  have inst := U.2.isLocalization_basicOpen t
  let ρ : Γ(X, U.1) →+* Γ(X, X.basicOpen t) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom
  have hu : IsUnit (ρ t) :=
    IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen t)) t
  have hZ : Z.ideal (X.affineBasicOpen t) = Ideal.map ρ (Z.ideal U) :=
    (Z.map_ideal_basicOpen U t).symm
  have hne : Nonempty (X.basicOpen t : X.Opens) := ⟨⟨_, hx⟩⟩
  have hρf : ρ f ≠ 0 := by
    intro h0
    apply hf0
    apply germ_injective_of_isIntegral X (U := U.1) (U.2.fromSpec q) hxU
    have h2 := congrArg (X.presheaf.germ (X.basicOpen t) (U.2.fromSpec q) hx).hom h0
    rw [map_zero] at h2 ⊢
    rw [← h2]
    simp [ρ]
  have hnz : ρ f ∈ nonZeroDivisors Γ(X, X.basicOpen t) := mem_nonZeroDivisors_of_ne_zero hρf
  suffices hspan : Ideal.map ρ (Z.ideal U) = Ideal.span {ρ f} from
    ⟨X.affineBasicOpen t, ρ f, hx, hnz, hZ.trans hspan⟩
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hgI
    obtain ⟨n, hn⟩ := hg g hgI
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    obtain ⟨u, hu'⟩ := hu.pow n
    refine ⟨(↑u⁻¹ : Γ(X, X.basicOpen t)) * ρ c, ?_⟩
    have h3 : ρ c * ρ f = ρ t ^ n * ρ g := by
      rw [← map_mul, hc, map_mul, map_pow]
    rw [mul_assoc, h3, ← hu', Units.inv_mul_cancel_left]
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem ρ hfI

end GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
