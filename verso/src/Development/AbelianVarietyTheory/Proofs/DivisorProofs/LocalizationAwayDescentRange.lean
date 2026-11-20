import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `k _ P T`. Establish `hs : ∀ t : Localization.Away P, ∃ (f : Polynomial k) (n : ℕ), IsLocalization.mk' (Localization.Away P) f (⟨P ^ n, n, rfl⟩ : Submonoid.powers P) = t`. Introduce `t`. Take `⟨⟨f, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Submonoid.powers P) t`. Take `⟨n, hn⟩` from `s.2`.

Conclude with `⟨f, n, by congr 1; exact Subtype.ext hn⟩`. Use `choose f n hfn using hs`. Use `⟨T.biUnion (fun t => (f t).coeffs), ?_⟩` and prove the remaining obligations. Introduce `R hF P₁ h hP t ht`. Establish `hlift : f t ∈ Polynomial.lifts R.subtype`.

Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `m`. Distinguish the cases in `hm : (f t).coeff m = 0`. Conclude with `⟨0, by simp [hm]⟩`. Establish `: (f t).coeff m ∈ (T.biUnion (fun t => (f t).coeffs) : Set k)`.

Simplify using `only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]`. Conclude with `⟨t, ht, Polynomial.coeff_mem_coeffs hm⟩`. Conclude with `⟨⟨_, hF this⟩, rfl⟩`. Take `⟨f₁, hf₁⟩` from `(Polynomial.mem_lifts _).mp hlift`. Use `⟨IsLocalization.mk' (Localization.Away P₁) f₁ (⟨P₁ ^ n t, n t, rfl⟩ : Submonoid.powers P₁), ?_⟩` and prove the remaining obligations.

Rewrite using `[IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, hf₁, Polynomial.map_pow, hP]`. Establish `key` using `IsLocalization.mk'_spec' (Localization.Away P) (f t) (⟨P ^ n t, n t, rfl⟩ : Submonoid.powers P)`. Rewrite `key` using `[hfn t]`. Conclude with `key.symm`.
-/
theorem localization_away_descent_range :
 ∀ (k : Type) [Field k] (P : Polynomial k) (T : Finset (Localization.Away P)), ∃ F : Finset k, ∀ (R : Subring k), (F : Set k) ⊆ R → ∀ (P₁ : Polynomial R) (h : IsUnit (((algebraMap (Polynomial k) (Localization.Away P)).comp (Polynomial.mapRingHom R.subtype)) P₁)), P₁.map R.subtype = P → ∀ t ∈ T, t ∈ (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ h).range := by
  classical
  intro k _ P T
  have hs : ∀ t : Localization.Away P, ∃ (f : Polynomial k) (n : ℕ),
      IsLocalization.mk' (Localization.Away P) f
        (⟨P ^ n, n, rfl⟩ : Submonoid.powers P) = t := by
    intro t
    obtain ⟨⟨f, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers P) t
    obtain ⟨n, hn⟩ := s.2
    exact ⟨f, n, by congr 1; exact Subtype.ext hn⟩
  choose f n hfn using hs
  refine ⟨T.biUnion (fun t => (f t).coeffs), ?_⟩
  intro R hF P₁ h hP t ht
  have hlift : f t ∈ Polynomial.lifts R.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro m
    by_cases hm : (f t).coeff m = 0
    · exact ⟨0, by simp [hm]⟩
    · have : (f t).coeff m ∈ (T.biUnion (fun t => (f t).coeffs) : Set k) := by
        simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
        exact ⟨t, ht, Polynomial.coeff_mem_coeffs hm⟩
      exact ⟨⟨_, hF this⟩, rfl⟩
  obtain ⟨f₁, hf₁⟩ := (Polynomial.mem_lifts _).mp hlift
  refine ⟨IsLocalization.mk' (Localization.Away P₁) f₁
    (⟨P₁ ^ n t, n t, rfl⟩ : Submonoid.powers P₁), ?_⟩
  rw [IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, hf₁,
    Polynomial.map_pow, hP]
  have key := IsLocalization.mk'_spec' (Localization.Away P) (f t)
    (⟨P ^ n t, n t, rfl⟩ : Submonoid.powers P)
  rw [hfn t] at key
  exact key.symm

end GlobalTheory
