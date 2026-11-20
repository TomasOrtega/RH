import Mathlib
import GroundTheory.GlobalFields.ClassFieldConsequences.CongruenceSubgroupLeStandardOpenSubgroup

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing

namespace GroundTheory.Global

noncomputable section

/- English proof (translation)
The claim follows from `hs.subset_isClopen ⟨H.isClosed_of_isOpen hH, hH⟩ ⟨1, h1, H.one_mem⟩`.
-/
theorem Subgroup.subset_of_isPreconnected {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G)) {s : Set G}
    (hs : IsPreconnected s) (h1 : (1 : G) ∈ s) : s ⊆ H :=
  hs.subset_isClopen ⟨H.isClosed_of_isOpen hH, hH⟩ ⟨1, h1, H.one_mem⟩

/- English proof (translation)
Set `f : ℝ → ℝˣ` to `fun t ↦ Units.mk0 (Real.exp t) (Real.exp_ne_zero t)`. Establish `hf : Continuous f` using `Units.isEmbedding_val₀.isInducing.continuous_iff.2 Real.continuous_exp`. Establish `hsub` using `Subgroup.subset_of_isPreconnected H hH (isPreconnected_range hf) ⟨0, Units.ext (by simp [f])⟩`. Conclude with `hsub ⟨Real.log r, Units.ext (Real.exp_log hr)⟩`.
-/
theorem Subgroup.mem_of_isOpen_of_pos (H : Subgroup ℝˣ) (hH : IsOpen (H : Set ℝˣ)) {r : ℝˣ}
    (hr : 0 < (r : ℝ)) : r ∈ H := by
  let f : ℝ → ℝˣ := fun t ↦ Units.mk0 (Real.exp t) (Real.exp_ne_zero t)
  have hf : Continuous f := Units.isEmbedding_val₀.isInducing.continuous_iff.2 Real.continuous_exp
  have hsub := Subgroup.subset_of_isPreconnected H hH (isPreconnected_range hf)
    ⟨0, Units.ext (by simp [f])⟩
  exact hsub ⟨Real.log r, Units.ext (Real.exp_log hr)⟩

/- English proof (translation)
The claim follows from `Subgroup.subset_of_isPreconnected H hH isPreconnected_univ (Set.mem_univ 1) (Set.mem_univ z)`.
-/
theorem Subgroup.mem_of_isOpen_complexUnits (H : Subgroup ℂˣ) (hH : IsOpen (H : Set ℂˣ)) (z : ℂˣ) :
    z ∈ H :=
  Subgroup.subset_of_isPreconnected H hH isPreconnected_univ (Set.mem_univ 1) (Set.mem_univ z)

variable {K : Type*} [Field K] [NumberField K]

open IdeleGroup

/- English proof (translation)
Set `Hr : Subgroup ℝˣ` to `(H.comap (infiniteEmbedding w)).comap (realUnitsHom hw).toMonoidHom`. Establish `hopen : IsOpen (Hr : Set ℝˣ)` using `(hH.preimage (continuous_infiniteEmbedding w)).preimage (realUnitsHom hw).continuous`. Set `r : ℝˣ` to `Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw : w.Completion →+* ℝ).toMonoidHom a`. Establish `hr : 0 < (r : ℝ)`. Express the relevant statement in the definitionally equal form `0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (a : w.Completion)`.

Rewrite using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply]`. Conclude with `ha`. Establish `hmem : r ∈ Hr` using `Subgroup.mem_of_isOpen_of_pos Hr hopen hr`. Rewrite using `[← realUnitsHom_surjective hw a]`. Conclude with `hmem`.
-/
theorem infiniteEmbedding_mem_of_isOpen_of_isReal (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsReal)
    {a : (w.Completion)ˣ}
    (ha : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw (a : w.Completion)) :
    infiniteEmbedding w a ∈ H := by
  let Hr : Subgroup ℝˣ := (H.comap (infiniteEmbedding w)).comap (realUnitsHom hw).toMonoidHom
  have hopen : IsOpen (Hr : Set ℝˣ) :=
    (hH.preimage (continuous_infiniteEmbedding w)).preimage (realUnitsHom hw).continuous
  let r : ℝˣ := Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw :
    w.Completion →+* ℝ).toMonoidHom a
  have hr : 0 < (r : ℝ) := by
    change 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (a : w.Completion)
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact ha
  have hmem : r ∈ Hr := Subgroup.mem_of_isOpen_of_pos Hr hopen hr
  rw [← realUnitsHom_surjective hw a]
  exact hmem

/- English proof (translation)
Set `Hc : Subgroup ℂˣ` to `(H.comap (infiniteEmbedding w)).comap (complexUnitsHom hw).toMonoidHom`. Establish `hopen : IsOpen (Hc : Set ℂˣ)` using `(hH.preimage (continuous_infiniteEmbedding w)).preimage (complexUnitsHom hw).continuous`. Establish `hmem` using `Subgroup.mem_of_isOpen_complexUnits Hc hopen (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw : w.Completion →+* ℂ).toMonoidHom a)`. Rewrite using `[← complexUnitsHom_surjective hw a]`. Conclude with `hmem`.
-/
theorem infiniteEmbedding_mem_of_isOpen_of_isComplex (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) {w : InfinitePlace K} (hw : w.IsComplex)
    (a : (w.Completion)ˣ) : infiniteEmbedding w a ∈ H := by
  let Hc : Subgroup ℂˣ := (H.comap (infiniteEmbedding w)).comap (complexUnitsHom hw).toMonoidHom
  have hopen : IsOpen (Hc : Set ℂˣ) :=
    (hH.preimage (continuous_infiniteEmbedding w)).preimage (complexUnitsHom hw).continuous
  have hmem := Subgroup.mem_of_isOpen_complexUnits Hc hopen
    (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw :
      w.Completion →+* ℂ).toMonoidHom a)
  rw [← complexUnitsHom_surjective hw a]
  exact hmem

/- English proof (translation)
Establish `hWf : (H.comap ofFinite : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ 𝓝 1` using `(hH.preimage continuous_ofFinite).mem_nhds (by simp [H.one_mem])`. Take `⟨S, n, -, hn0, hsub⟩` from `exists_finiteLevel_subset hWf`. Establish `hsupp : (support n).Finite` using `S.finite_toSet.subset fun v hv ↦ by`. Assume the negation of the conclusion as `h`. Conclude with `hv (hn0 v h)`.

Set `𝔪 : Modulus K` to `⟨∏ᶠ v, v.asIdeal ^ n v, finprod_asIdeal_pow_ne_bot n, Set.univ⟩`. Establish `hle : ∀ v, n v ≤ 𝔪.exponent v` using `(finprod_asIdeal_pow_dvd_iff hsupp (finprod_asIdeal_pow_ne_bot n)).1 dvd_rfl`. Use `⟨𝔪, rfl, fun x hx ↦ ?_⟩` and prove the remaining obligations. Take `⟨hf, hi⟩` from `𝔪.mem_congruenceSubgroup.1 hx`. Rewrite using `[← ofFinite_mul_ofInfinite x]`.

Use `H.mul_mem ?_ ?_` and prove the remaining obligations. Establish `: toFinite K x ∈ finiteLevel n` using `mem_finiteLevel.2 fun v ↦ by`. Rewrite using `[finiteComponent_toFinite]`. Conclude with `unitsLevel_antitone v (hle v) (hf v)`. Conclude with `hsub this`.

Rewrite using `[ofInfinite_eq_prod]`. Use `Subgroup.prod_mem H fun w _ ↦ ?_` and prove the remaining obligations. Break down `w.isReal_or_isComplex with hw | hw` into its components or cases. Conclude with `infiniteEmbedding_mem_of_isOpen_of_isReal H hH hw (hi ⟨w, hw⟩ (Set.mem_univ _))`. Conclude with `infiniteEmbedding_mem_of_isOpen_of_isComplex H hH hw _`.
-/
theorem Modulus.exists_congruenceSubgroup_le (H : Subgroup (IdeleGroup K))
    (hH : IsOpen (H : Set (IdeleGroup K))) :
    ∃ 𝔪 : Modulus K, 𝔪.real = Set.univ ∧ 𝔪.congruenceSubgroup ≤ H := by
  classical
  have hWf : (H.comap ofFinite : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∈ 𝓝 1 :=
    (hH.preimage continuous_ofFinite).mem_nhds (by simp [H.one_mem])
  obtain ⟨S, n, -, hn0, hsub⟩ := exists_finiteLevel_subset hWf
  have hsupp : (support n).Finite :=
    S.finite_toSet.subset fun v hv ↦ by
      by_contra h
      exact hv (hn0 v h)
  let 𝔪 : Modulus K := ⟨∏ᶠ v, v.asIdeal ^ n v, finprod_asIdeal_pow_ne_bot n, Set.univ⟩
  have hle : ∀ v, n v ≤ 𝔪.exponent v :=
    (finprod_asIdeal_pow_dvd_iff hsupp (finprod_asIdeal_pow_ne_bot n)).1 dvd_rfl
  refine ⟨𝔪, rfl, fun x hx ↦ ?_⟩
  obtain ⟨hf, hi⟩ := 𝔪.mem_congruenceSubgroup.1 hx
  rw [← ofFinite_mul_ofInfinite x]
  refine H.mul_mem ?_ ?_
  · have : toFinite K x ∈ finiteLevel n := mem_finiteLevel.2 fun v ↦ by
      rw [finiteComponent_toFinite]
      exact unitsLevel_antitone v (hle v) (hf v)
    exact hsub this
  · rw [ofInfinite_eq_prod]
    refine Subgroup.prod_mem H fun w _ ↦ ?_
    rcases w.isReal_or_isComplex with hw | hw
    · exact infiniteEmbedding_mem_of_isOpen_of_isReal H hH hw (hi ⟨w, hw⟩ (Set.mem_univ _))
    · exact infiniteEmbedding_mem_of_isOpen_of_isComplex H hH hw _

/- English proof (translation)
Take `⟨𝔪, h𝔪, hle⟩` from `Modulus.exists_congruenceSubgroup_le (H.comap (IdeleClassGroup.mk K)) (hH.preimage (IdeleClassGroup.continuous_mk K))`. Conclude with `⟨𝔪, h𝔪, Subgroup.map_le_iff_le_comap.2 hle⟩`.
-/
theorem IdeleClassGroup.exists_map_congruenceSubgroup_le (H : Subgroup (IdeleClassGroup K))
    (hH : IsOpen (H : Set (IdeleClassGroup K))) :
    ∃ 𝔪 : Modulus K, 𝔪.real = Set.univ ∧ 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≤ H := by
  obtain ⟨𝔪, h𝔪, hle⟩ := Modulus.exists_congruenceSubgroup_le (H.comap (IdeleClassGroup.mk K))
    (hH.preimage (IdeleClassGroup.continuous_mk K))
  exact ⟨𝔪, h𝔪, Subgroup.map_le_iff_le_comap.2 hle⟩

/- English proof (translation)
The claim follows from `(IdeleClassGroup.exists_map_congruenceSubgroup_le H hH).imp fun _ h ↦ h.2`.
-/
theorem IdeleClassGroup.exists_map_congruenceSubgroup_le_of_finiteIndex
    (H : Subgroup (IdeleClassGroup K)) (hH : IsOpen (H : Set (IdeleClassGroup K)))
    (_ : H.FiniteIndex) :
    ∃ 𝔪 : Modulus K, 𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) ≤ H :=
  (IdeleClassGroup.exists_map_congruenceSubgroup_le H hH).imp fun _ h ↦ h.2

/- English proof (translation)
Rewrite using `[Subgroup.coe_map]`. Conclude with `IdeleClassGroup.isOpenMap_mk K _ 𝔪.isOpen_congruenceSubgroup`.
-/
theorem Modulus.isOpen_map_congruenceSubgroup (𝔪 : Modulus K) :
    IsOpen (𝔪.congruenceSubgroup.map (IdeleClassGroup.mk K) : Set (IdeleClassGroup K)) := by
  rw [Subgroup.coe_map]
  exact IdeleClassGroup.isOpenMap_mk K _ 𝔪.isOpen_congruenceSubgroup

end

end GroundTheory.Global
