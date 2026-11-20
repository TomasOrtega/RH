import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DerivationLocalization

universe u v w

namespace FunctorialResolution.EmbeddedResolution

variable {k : Type u} {S : Type v} {S' : Type w}

/- English proof (translation)
Rewrite using `[Ideal.map_le_iff_le_comap, derivIdeal_le_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Use `Ideal.mem_comap.mpr ?_` and prove the remaining obligations. Conclude with `le_derivIdeal k _ (Ideal.mem_map_of_mem (algebraMap S S') hx)`.

Introduce `D x hx`. Use `Ideal.mem_comap.mpr ?_` and prove the remaining obligations. Establish `h` using `derivation_apply_mem_derivIdeal k (Ideal.map (algebraMap S S') J) (D.mapToLocalization (S' := S') M) (Ideal.mem_map_of_mem (algebraMap S S') hx)`. Rewrite `h` using `[Derivation.mapToLocalization_algebraMap]`. Then use the resulting hypothesis.
-/
theorem map_derivIdeal_le [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) ≤
      derivIdeal k (Ideal.map (algebraMap S S') J) := by
  rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
  constructor
  · intro x hx
    refine Ideal.mem_comap.mpr ?_
    exact le_derivIdeal k _ (Ideal.mem_map_of_mem (algebraMap S S') hx)
  · intro D x hx
    refine Ideal.mem_comap.mpr ?_
    have h := derivation_apply_mem_derivIdeal k (Ideal.map (algebraMap S S') J)
      (D.mapToLocalization (S' := S') M) (Ideal.mem_map_of_mem (algebraMap S S') hx)
    rwa [Derivation.mapToLocalization_algebraMap] at h

/- English proof (translation)
Take `⟨m, D₀, hm⟩` from `Derivation.exists_derivation_mul_eq_of_isLocalization (R := k) M D`. Use `(Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp ?_` and prove the remaining obligations. Rewrite using `[hm a]`. Conclude with `Ideal.mem_map_of_mem _ (derivation_apply_mem_derivIdeal k J D₀ ha)`.
-/
private theorem derivation_algebraMap_mem_map_derivIdeal [CommRing k] [CommRing S] [CommRing S'] [Algebra k S]
    [Algebra S S'] [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S)
    (D : Derivation k S' S') {a : S} (ha : a ∈ J) :
    D (algebraMap S S' a) ∈ Ideal.map (algebraMap S S') (derivIdeal k J) := by
  obtain ⟨m, D₀, hm⟩ := Derivation.exists_derivation_mul_eq_of_isLocalization (R := k) M D
  refine (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp ?_
  rw [hm a]
  exact Ideal.mem_map_of_mem _ (derivation_apply_mem_derivIdeal k J D₀ ha)

/- English proof (translation)
Rewrite using `[derivIdeal_le_iff]`. Use `⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩` and prove the remaining obligations. Introduce `D x hx`. Rewrite `hx` using `[IsLocalization.mem_map_algebraMap_iff M S']`. Take `⟨⟨a, m⟩, hax⟩` from `hx`.

Establish `h1 : D (x * algebraMap S S' (m : S)) = D (algebraMap S S' (a : S))` using `by rw [hax]`. Rewrite `h1` using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Establish `hA : D (algebraMap S S' (a : S)) ∈ Ideal.map (algebraMap S S') (derivIdeal k J)` using `derivation_algebraMap_mem_map_derivIdeal M J D a.2`. Establish `hmem1 : algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) ∈ Ideal.map (algebraMap S S') (derivIdeal k J)` using `Ideal.mul_mem_left _ _ hA`. Establish `hmem2 : algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) ∈ Ideal.map (algebraMap S S') (derivIdeal k J)` using `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (le_derivIdeal k J a.2))`.

Establish `h3 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) ∈ Ideal.map (algebraMap S S') (derivIdeal k J)`. Establish `h2 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) = algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) - algebraMap S S' (a : S) * D (algebraMap S S' (m : S))`. Take the linear combination `(algebraMap S S' (m : S)) * h1 - (D (algebraMap S S' (m : S))) * hax`. Rewrite using `[h2]`. Conclude with `sub_mem hmem1 hmem2`.

Conclude with `(Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp ((Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp h3)`.
-/
theorem derivIdeal_map_le [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    derivIdeal k (Ideal.map (algebraMap S S') J) ≤
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
  rw [derivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
  intro D x hx
  rw [IsLocalization.mem_map_algebraMap_iff M S'] at hx
  obtain ⟨⟨a, m⟩, hax⟩ := hx
  have h1 : D (x * algebraMap S S' (m : S)) = D (algebraMap S S' (a : S)) := by rw [hax]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
  have hA : D (algebraMap S S' (a : S)) ∈ Ideal.map (algebraMap S S') (derivIdeal k J) :=
    derivation_algebraMap_mem_map_derivIdeal M J D a.2
  have hmem1 : algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) := Ideal.mul_mem_left _ _ hA
  have hmem2 : algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) :=
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (le_derivIdeal k J a.2))
  have h3 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
    have h2 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) =
        algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) -
          algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) := by
      linear_combination (algebraMap S S' (m : S)) * h1 - (D (algebraMap S S' (m : S))) * hax
    rw [h2]
    exact sub_mem hmem1 hmem2
  exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp
    ((Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp h3)

/- English proof (translation)
The claim follows from `le_antisymm (map_derivIdeal_le M J) (derivIdeal_map_le M J)`.
-/
theorem map_derivIdeal [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  le_antisymm (map_derivIdeal_le M J) (derivIdeal_map_le M J)

/- English proof (translation)
The claim follows from `map_derivIdeal (Submonoid.powers g) J`.
-/
theorem map_derivIdeal_away [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  map_derivIdeal (Submonoid.powers g) J

end FunctorialResolution.EmbeddedResolution
