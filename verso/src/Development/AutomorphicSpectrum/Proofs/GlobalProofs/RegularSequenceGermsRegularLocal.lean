import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.ResKCoords

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[← Ideal.comap_symm, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]`. Conclude with `isUnit_map_iff e.symm x`.
-/
theorem map_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  ext x
  rw [← Ideal.comap_symm, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact isUnit_map_iff e.symm x

/- English proof (translation)
Use `⟨?_, h.2.trans (ringKrullDim_eq_of_ringEquiv e)⟩` and prove the remaining obligations. Establish `h1 : Set.range (fun i => e (r i)) = (e : R → S) '' Set.range r`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[h1, ← map_maximalIdeal_of_ringEquiv e, ← h.1]`.

Conclude with `(Ideal.map_span e (Set.range r)).symm`.
-/
theorem rsp_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) (m : ℕ) (r : Fin m → R) (h : FinalTheorems.Rsp R m r) :
    FinalTheorems.Rsp S m (fun i => e (r i)) := by
  refine ⟨?_, h.2.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have h1 : Set.range (fun i => e (r i)) = (e : R → S) '' Set.range r := by
    rw [← Set.range_comp]; rfl
  rw [h1, ← map_maximalIdeal_of_ringEquiv e, ← h.1]
  exact (Ideal.map_span e (Set.range r)).symm

/- English proof (translation)
Introduce `Y U y hy hreg m f hr`. Use `letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : U.1)`. Use `haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := U.2.isLocalization_stalk ⟨y, hy⟩`. Set `e : Y.presheaf.stalk y ≃+* Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal` to `(IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y) (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).toRingEquiv`. Establish `he : ∀ a : Γ(Y, U.1), e (Y.presheaf.germ U.1 y hy a) = algebraMap Γ(Y, U.1) _ a` using `fun a => (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y) (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).commutes a`.

Use `⟨IsRegularLocalRing.of_ringEquiv e, ?_, fun s => ?_⟩` and prove the remaining obligations. Establish `h` using `rsp_of_ringEquiv e m _ hr`. Simplify `h` using `only [he]`. Rewrite using `[Scheme.mem_basicOpen Y s y hy]`. Establish `h` using `IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal s`.

Conclude with `h.trans Iff.rfl`.
-/
theorem stalk_to_localization : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) →
    IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
    FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m
      (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧
    ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro Y U y hy hreg m f hr
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : U.1)
  haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨y, hy⟩
  let e : Y.presheaf.stalk y ≃+* Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).toRingEquiv
  have he : ∀ a : Γ(Y, U.1), e (Y.presheaf.germ U.1 y hy a) = algebraMap Γ(Y, U.1) _ a := fun a =>
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).commutes a
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_, fun s => ?_⟩
  · have h := rsp_of_ringEquiv e m _ hr
    simpa only [he] using h
  · rw [Scheme.mem_basicOpen Y s y hy]
    have h := IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y)
      (U.2.primeIdealOf ⟨y, hy⟩).asIdeal s
    exact h.trans Iff.rfl

end GlobalTheory.CompanionTheory.ResKCoords
