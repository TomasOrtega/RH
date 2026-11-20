import Mathlib

namespace GlobalTheory.DedekindSmooth

open Polynomial IsLocalRing

/- English proof (translation)
Establish `h : IsField (Localization.AtPrime (⊥ : Ideal B))`. Rewrite using `[IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]`. Simplify using the standard rewrite rules. Use `letI := h.toField`. Establish `: Algebra.EssFiniteType B (Localization.AtPrime (⊥ : Ideal B))` using `.of_isLocalization _ (⊥ : Ideal B).primeCompl`.

Establish `: Algebra.EssFiniteType k (Localization.AtPrime (⊥ : Ideal B))` using `.comp _ B _`. Conclude with `Algebra.FormallySmooth.of_perfectField`.
-/
theorem isSmoothAt_bot (k : Type) [Field k] [PerfectField k] (B : Type) [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] : Algebra.IsSmoothAt k (⊥ : Ideal B) := by
  have h : IsField (Localization.AtPrime (⊥ : Ideal B)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
    simp
  letI := h.toField
  have : Algebra.EssFiniteType B (Localization.AtPrime (⊥ : Ideal B)) :=
    .of_isLocalization _ (⊥ : Ideal B).primeCompl
  have : Algebra.EssFiniteType k (Localization.AtPrime (⊥ : Ideal B)) := .comp _ B _
  exact Algebra.FormallySmooth.of_perfectField

/- English proof (translation)
Use `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq (Localization.AtPrime q)` as an intermediate fact. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)`. Take `⟨⟨t, s⟩, h⟩` from `IsLocalization.surj q.primeCompl π`. Establish `hs : IsUnit (algebraMap B (Localization.AtPrime q) s)` using `IsLocalization.map_units _ s`. Establish `hm : maximalIdeal (Localization.AtPrime q) = Ideal.span {algebraMap B (Localization.AtPrime q) t}`.

Simplify using `only at h`. Rewrite using `[← h, Ideal.span_singleton_mul_right_unit hs, hπ.maximalIdeal_eq]`. Use `⟨t, ?_, ?_, hm⟩` and prove the remaining obligations. Rewrite using `[← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, hm]`. Conclude with `Ideal.mem_span_singleton_self _`.

Introduce and unpack `rfl`. Simplify using `only [map_zero] at h`. Conclude with `mul_ne_zero hπ.ne_zero hs.ne_zero h`.
-/
theorem exists_uniformiser (B : Type) [CommRing B] [IsDedekindDomain B] (q : Ideal B) [q.IsPrime]
    (hq : q ≠ ⊥) : ∃ t ∈ q, t ≠ 0 ∧ maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap B (Localization.AtPrime q) t} := by
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hq
    (Localization.AtPrime q)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  obtain ⟨⟨t, s⟩, h⟩ := IsLocalization.surj q.primeCompl π
  have hs : IsUnit (algebraMap B (Localization.AtPrime q) s) := IsLocalization.map_units _ s
  have hm : maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap B (Localization.AtPrime q) t} := by
    simp only at h
    rw [← h, Ideal.span_singleton_mul_right_unit hs, hπ.maximalIdeal_eq]
  refine ⟨t, ?_, ?_, hm⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, hm]
    exact Ideal.mem_span_singleton_self _
  · rintro rfl
    simp only [map_zero] at h
    exact mul_ne_zero hπ.ne_zero hs.ne_zero h

/- English proof (translation)
Take `⟨t, htq, ht0, hm⟩` from `exists_uniformiser B q hq`. Establish `hqm : q.IsMaximal` using `hqp.isMaximal hq`. Establish `htr : Transcendental k t`. Introduce `ha`. Establish `hi` using `ha.isIntegral`.

Establish `hu : IsUnit t` using `hi.isUnit ht0`. Conclude with `hqp.ne_top (Ideal.eq_top_of_isUnit_mem _ htq hu)`. Use `letI : Algebra k[X] B := (aeval t : k[X] →ₐ[k] B).toRingHom.toAlgebra`. Establish `: IsScalarTower k k[X] B` using `.of_algebraMap_eq fun c => by`. Express the relevant statement in the definitionally equal form `_ = aeval t (algebraMap k k[X] c)`.

Simplify using the standard rewrite rules. Establish `hinj : Function.Injective (algebraMap k[X] B)` using `transcendental_iff_injective.mp htr`. Establish `: FaithfulSMul k[X] B` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`. Establish `: Module.Flat k[X] B` using `inferInstance`. Establish `: Algebra.FiniteType k[X] B` using `.of_restrictScalars_finiteType k _ _`.

Establish `: Algebra.FinitePresentation k[X] B` using `(Algebra.FinitePresentation.of_finiteType (R := k[X]) (A := B)).mp ‹_›`. Set `p : Ideal k[X]` to `q.under k[X]`. Use `letI := Localization.AtPrime.algebraOfLiesOver p q`. Establish `hsep : Algebra.IsSeparable p.ResidueField q.ResidueField`. Establish `: Module.Finite k (B ⧸ q)`.

Use `letI := Ideal.Quotient.field q`. Conclude with `finite_of_finite_type_of_isJacobsonRing k (B ⧸ q)`. Establish `: Module.Finite k q.ResidueField` using `Module.Finite.of_surjective (IsScalarTower.toAlgHom k (B ⧸ q) q.ResidueField).toLinearMap (Ideal.bijective_algebraMap_quotient_residueField q).2`. Establish `: IsScalarTower k p.ResidueField q.ResidueField` using `.of_algebraMap_eq fun c => by`. Rewrite using `[IsScalarTower.algebraMap_apply k k[X] p.ResidueField, ← IsScalarTower.algebraMap_apply k[X] p.ResidueField q.ResidueField, ← IsScalarTower.algebraMap_apply]`.

Conclude with `Algebra.isSeparable_tower_top_of_isSeparable k _ _`. Establish `hmap : p.map (algebraMap k[X] (Localization.AtPrime q)) = maximalIdeal _`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`.

Rewrite using `[Ideal.mem_comap, IsScalarTower.algebraMap_apply k[X] B (Localization.AtPrime q), IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]`. Conclude with `hx`. Establish `hX : algebraMap k[X] B X = t` using `aeval_X t`. Rewrite using `[hm, Ideal.span_singleton_le_iff_mem, ← hX, ← IsScalarTower.algebraMap_apply]`. Apply `Ideal.mem_map_of_mem` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `algebraMap k[X] B X ∈ q`. Rewrite using `[hX]` and apply the resulting hypothesis. Establish `: Algebra.IsUnramifiedAt k[X] q` using `(Algebra.isUnramifiedAt_iff_map_eq k[X] p q).mpr ⟨hsep, hmap⟩`. Establish `: Algebra.IsEtaleAt k[X] q` using `.of_isUnramifiedAt_of_flat q`. Conclude with `Algebra.FormallySmooth.comp k k[X] _`.
-/
theorem isSmoothAt_of_ne_bot (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : Ideal B) [hqp : q.IsPrime]
    (hq : q ≠ ⊥) : Algebra.IsSmoothAt k q := by
  obtain ⟨t, htq, ht0, hm⟩ := exists_uniformiser B q hq
  have hqm : q.IsMaximal := hqp.isMaximal hq
  have htr : Transcendental k t := by
    intro ha
    have hi := ha.isIntegral
    have hu : IsUnit t := hi.isUnit ht0
    exact hqp.ne_top (Ideal.eq_top_of_isUnit_mem _ htq hu)
  letI : Algebra k[X] B := (aeval t : k[X] →ₐ[k] B).toRingHom.toAlgebra
  have : IsScalarTower k k[X] B := .of_algebraMap_eq fun c => by
    change _ = aeval t (algebraMap k k[X] c)
    simp
  have hinj : Function.Injective (algebraMap k[X] B) := transcendental_iff_injective.mp htr
  have : FaithfulSMul k[X] B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Module.Flat k[X] B := inferInstance
  have : Algebra.FiniteType k[X] B := .of_restrictScalars_finiteType k _ _
  have : Algebra.FinitePresentation k[X] B :=
    (Algebra.FinitePresentation.of_finiteType (R := k[X]) (A := B)).mp ‹_›
  let p : Ideal k[X] := q.under k[X]
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have hsep : Algebra.IsSeparable p.ResidueField q.ResidueField := by
    have : Module.Finite k (B ⧸ q) := by
      letI := Ideal.Quotient.field q
      exact finite_of_finite_type_of_isJacobsonRing k (B ⧸ q)
    have : Module.Finite k q.ResidueField :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom k (B ⧸ q) q.ResidueField).toLinearMap
        (Ideal.bijective_algebraMap_quotient_residueField q).2
    have : IsScalarTower k p.ResidueField q.ResidueField := .of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k k[X] p.ResidueField,
        ← IsScalarTower.algebraMap_apply k[X] p.ResidueField q.ResidueField,
        ← IsScalarTower.algebraMap_apply]
    exact Algebra.isSeparable_tower_top_of_isSeparable k _ _
  have hmap : p.map (algebraMap k[X] (Localization.AtPrime q)) = maximalIdeal _ := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply k[X] B (Localization.AtPrime q),
        IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q]
      exact hx
    · have hX : algebraMap k[X] B X = t := aeval_X t
      rw [hm, Ideal.span_singleton_le_iff_mem, ← hX, ← IsScalarTower.algebraMap_apply]
      apply Ideal.mem_map_of_mem
      change algebraMap k[X] B X ∈ q
      rwa [hX]
  have : Algebra.IsUnramifiedAt k[X] q :=
    (Algebra.isUnramifiedAt_iff_map_eq k[X] p q).mpr ⟨hsep, hmap⟩
  have : Algebra.IsEtaleAt k[X] q := .of_isUnramifiedAt_of_flat q
  exact Algebra.FormallySmooth.comp k k[X] _

/- English proof (translation)
Introduce `k _ _ B _ _ _ _`. Establish `: Algebra.FinitePresentation k B` using `(Algebra.FinitePresentation.of_finiteType (R := k) (A := B)).mp ‹_›`. Use `⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q => ?_), ‹_›⟩` and prove the remaining obligations. Take `⟨q, hq⟩` from `q`. Distinguish the cases in `h : q = ⊥`.

Substitute `h` using the available equality. Conclude with `isSmoothAt_bot k B`. Conclude with `isSmoothAt_of_ne_bot k B q h`.
-/
theorem smooth_of_isDedekindDomain :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDedekindDomain B]
      [Algebra k B] [Algebra.FiniteType k B], Algebra.Smooth k B := by
  intro k _ _ B _ _ _ _
  have : Algebra.FinitePresentation k B :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := B)).mp ‹_›
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q => ?_), ‹_›⟩
  obtain ⟨q, hq⟩ := q
  by_cases h : q = ⊥
  · subst h
    exact isSmoothAt_bot k B
  · exact isSmoothAt_of_ne_bot k B q h

end GlobalTheory.DedekindSmooth
