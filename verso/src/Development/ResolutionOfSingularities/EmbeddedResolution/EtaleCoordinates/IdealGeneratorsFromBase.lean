import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

/- English proof (translation)
Establish `hGu : IsUnit (algebraMap S T G)` using `IsLocalization.map_units T (⟨G, Submonoid.mem_powers G⟩ : Submonoid.powers G)`. Rewrite `hGu` using `[hG, map_mul]`. Take `⟨u, hu⟩` from `isUnit_of_mul_isUnit_left hGu`. Establish `hx : algebraMap S T x = (↑u⁻¹ : T) * algebraMap S T (g * x)`. Rewrite using `[map_mul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]`.

Rewrite using `[hx]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hgx)`.
-/
private theorem algebraMap_mem_map_of_mul_mem {S : Type*} [CommRing S] (G : S) (T : Type*)
    [CommRing T] [Algebra S T] [IsLocalization (Submonoid.powers G) T] (J : Ideal S) (g r x : S)
    (hG : G = g * r) (hgx : g * x ∈ J) :
    algebraMap S T x ∈ Ideal.map (algebraMap S T) J := by
  have hGu : IsUnit (algebraMap S T G) :=
    IsLocalization.map_units T (⟨G, Submonoid.mem_powers G⟩ : Submonoid.powers G)
  rw [hG, map_mul] at hGu
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_left hGu
  have hx : algebraMap S T x = (↑u⁻¹ : T) * algebraMap S T (g * x) := by
    rw [map_mul, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [hx]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hgx)

/- English proof (translation)
Take `⟨tI, htI⟩` from `hI`. Take `⟨tJ, htJ⟩` from `hJ`. Establish `keyI : ∀ u : S, ∃ g : S, g ∈ q.primeCompl ∧ (u ∈ I → g * u ∈ J)`. Introduce `u`. Distinguish the cases in `hu : u ∈ I`.

Establish `hmem : algebraMap S A u ∈ Ideal.map (algebraMap S A) J`. Rewrite using `[← h]`. Conclude with `Ideal.mem_map_of_mem _ hu`. Rewrite `hmem` using `[IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A]`. Take `⟨g, hg, hgu⟩` from `hmem`.

Conclude with `⟨g, hg, fun _ => hgu⟩`. Conclude with `⟨1, Submonoid.one_mem _, fun hh => absurd hh hu⟩`. Establish `keyJ : ∀ v : S, ∃ g : S, g ∈ q.primeCompl ∧ (v ∈ J → g * v ∈ I)`. Introduce `v`. Distinguish the cases in `hv : v ∈ J`.

Establish `hmem : algebraMap S A v ∈ Ideal.map (algebraMap S A) I`. Rewrite using `[h]`. Conclude with `Ideal.mem_map_of_mem _ hv`. Rewrite `hmem` using `[IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A]`. Take `⟨g, hg, hgv⟩` from `hmem`.

Conclude with `⟨g, hg, fun _ => hgv⟩`. Conclude with `⟨1, Submonoid.one_mem _, fun hh => absurd hh hv⟩`. Use `choose gI hgI hgIu using keyI`. Use `choose gJ hgJ hgJu using keyJ`. Set `G : S` to `(∏ u ∈ tI, gI u) * ∏ v ∈ tJ, gJ v`.

Establish `hGmem : G ∈ q.primeCompl` using `Submonoid.mul_mem _ (Submonoid.prod_mem _ fun u _ => hgI u) (Submonoid.prod_mem _ fun v _ => hgJ v)`. Use `⟨G, hGmem, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[← htI, Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Establish `hu' : u ∈ tI` using `Finset.mem_coe.mp hu`.

Establish `huI : u ∈ I`. Rewrite using `[← htI]`. Conclude with `Ideal.subset_span hu`. Establish `hGeq : G = gI u * ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v)` using `by show (∏ z ∈ tI, gI z) * (∏ v ∈ tJ, gJ v) = _`. Rewrite using `[← Finset.mul_prod_erase tI gI hu']`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `algebraMap_mem_map_of_mul_mem G (Localization.Away G) J (gI u) ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v) u hGeq (hgIu u huI)`. Rewrite using `[← htJ, Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Establish `hv' : v ∈ tJ` using `Finset.mem_coe.mp hv`.

Establish `hvJ : v ∈ J`. Rewrite using `[← htJ]`. Conclude with `Ideal.subset_span hv`. Establish `hGeq : G = gJ v * ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z)` using `by show (∏ u ∈ tI, gI u) * (∏ z ∈ tJ, gJ z) = _`. Rewrite using `[← Finset.mul_prod_erase tJ gJ hv']`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `algebraMap_mem_map_of_mul_mem G (Localization.Away G) I (gJ v) ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z) v hGeq (hgJu v hvJ)`.
-/
theorem exists_away_map_ideal_eq {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime]
    (A : Type*) [CommRing A] [Algebra S A] [IsLocalization q.primeCompl A]
    (I J : Ideal S) (hI : I.FG) (hJ : J.FG)
    (h : Ideal.map (algebraMap S A) I = Ideal.map (algebraMap S A) J) :
    ∃ g : S, g ∉ q ∧
      Ideal.map (algebraMap S (Localization.Away g)) I =
        Ideal.map (algebraMap S (Localization.Away g)) J := by
  classical
  obtain ⟨tI, htI⟩ := hI
  obtain ⟨tJ, htJ⟩ := hJ
  have keyI : ∀ u : S, ∃ g : S, g ∈ q.primeCompl ∧ (u ∈ I → g * u ∈ J) := by
    intro u
    by_cases hu : u ∈ I
    · have hmem : algebraMap S A u ∈ Ideal.map (algebraMap S A) J := by
        rw [← h]
        exact Ideal.mem_map_of_mem _ hu
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A] at hmem
      obtain ⟨g, hg, hgu⟩ := hmem
      exact ⟨g, hg, fun _ => hgu⟩
    · exact ⟨1, Submonoid.one_mem _, fun hh => absurd hh hu⟩
  have keyJ : ∀ v : S, ∃ g : S, g ∈ q.primeCompl ∧ (v ∈ J → g * v ∈ I) := by
    intro v
    by_cases hv : v ∈ J
    · have hmem : algebraMap S A v ∈ Ideal.map (algebraMap S A) I := by
        rw [h]
        exact Ideal.mem_map_of_mem _ hv
      rw [IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A] at hmem
      obtain ⟨g, hg, hgv⟩ := hmem
      exact ⟨g, hg, fun _ => hgv⟩
    · exact ⟨1, Submonoid.one_mem _, fun hh => absurd hh hv⟩
  choose gI hgI hgIu using keyI
  choose gJ hgJ hgJu using keyJ
  let G : S := (∏ u ∈ tI, gI u) * ∏ v ∈ tJ, gJ v
  have hGmem : G ∈ q.primeCompl :=
    Submonoid.mul_mem _ (Submonoid.prod_mem _ fun u _ => hgI u)
      (Submonoid.prod_mem _ fun v _ => hgJ v)
  refine ⟨G, hGmem, le_antisymm ?_ ?_⟩
  · rw [← htI, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ tI := Finset.mem_coe.mp hu
    have huI : u ∈ I := by
      rw [← htI]
      exact Ideal.subset_span hu
    have hGeq : G = gI u * ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v) := by
      show (∏ z ∈ tI, gI z) * (∏ v ∈ tJ, gJ v) = _
      rw [← Finset.mul_prod_erase tI gI hu']
      ring
    exact algebraMap_mem_map_of_mul_mem G (Localization.Away G) J (gI u)
      ((∏ z ∈ tI.erase u, gI z) * ∏ v ∈ tJ, gJ v) u hGeq (hgIu u huI)
  · rw [← htJ, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ tJ := Finset.mem_coe.mp hv
    have hvJ : v ∈ J := by
      rw [← htJ]
      exact Ideal.subset_span hv
    have hGeq : G = gJ v * ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z) := by
      show (∏ u ∈ tI, gI u) * (∏ z ∈ tJ, gJ z) = _
      rw [← Finset.mul_prod_erase tJ gJ hv']
      ring
    exact algebraMap_mem_map_of_mul_mem G (Localization.Away G) I (gJ v)
      ((∏ u ∈ tI, gI u) * ∏ z ∈ tJ.erase v, gJ z) v hGeq (hgJu v hvJ)

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
