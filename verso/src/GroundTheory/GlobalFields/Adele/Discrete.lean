import Mathlib
import GroundTheory.GlobalFields.Adele.Approximation
import GroundTheory.GlobalFields.Adele.IntegersLattice

namespace GroundTheory.Global

open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K]

/- English proof (translation)
Establish `hv : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K k ≤ 1` using `fun v => (coe_mem_adicCompletionIntegers_iff v k).mp (h v)`. Take `⟨z, hz⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one K k hv`. Conclude with `⟨z, hz⟩`.
-/
theorem exists_eq_of_forall_mem_adicCompletionIntegers (k : K)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    ∃ z : 𝓞 K, (z : K) = k := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K k ≤ 1 := fun v =>
    (coe_mem_adicCompletionIntegers_iff v k).mp (h v)
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K k hv
  exact ⟨z, hz⟩

/- English proof (translation)
Introduce `v` and use `(coe_mem_adicCompletionIntegers_iff v (z : K)).mpr (HeightOneSpectrum.valuation_le_one v z)`.
-/
theorem algebraMap_integers_mem_integralFiniteAdeles (z : 𝓞 K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (z : K) ∈ integralFiniteAdeles (𝓞 K) K := fun v =>
  (coe_mem_adicCompletionIntegers_iff v (z : K)).mpr (HeightOneSpectrum.valuation_le_one v z)

/- English proof (translation)
Use `discreteTopology_of_isOpen_of_forall_mem _ ({x : K∞ | ∀ w, ‖x w‖ < 1} ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))) ?_ ⟨fun w => by show ‖(0 : K∞) w‖ < 1` and prove the remaining obligations. Rewrite using `[show (0 : K∞) w = 0 from rfl, norm_zero]`. Conclude with `one_pos,`. Use the proof step `Subring.zero_mem _⟩ ?_`. Use `IsOpen.prod ?_ isOpen_integralFiniteAdeles` and prove the remaining obligations.

Simplify using `only [Set.ofPred_forall]`. Conclude with `isOpen_iInter_of_finite fun w => isOpen_lt (continuous_apply (A := fun w : InfinitePlace K => w.Completion) w).norm continuous_const`. Introduce and unpack `_ ⟨k, rfl⟩ ⟨hinf, hf⟩`. Take `⟨z, rfl⟩` from `exists_eq_of_forall_mem_adicCompletionIntegers K k hf`. Establish `hz : ∀ w : InfinitePlace K, w z < 1` using `fun w => by`.

Use `hinf w` as an intermediate fact. Rewrite `this` using `[show (algebraMap K 𝔸[K] (z : K)).1 = algebraMap K K∞ (z : K) from rfl, norm_algebraMap_apply]`. Then use the resulting hypothesis. Rewrite using `[eq_zero_of_forall_infinitePlace_lt_one K z hz]`. Simplify using the standard rewrite rules.
-/
theorem discreteTopology_principalSubgroup :
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 K) K) := by
  refine discreteTopology_of_isOpen_of_forall_mem _
    ({x : K∞ | ∀ w, ‖x w‖ < 1} ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)))
    ?_ ⟨fun w => by
      show ‖(0 : K∞) w‖ < 1
      rw [show (0 : K∞) w = 0 from rfl, norm_zero]; exact one_pos,
      Subring.zero_mem _⟩ ?_
  · refine IsOpen.prod ?_ isOpen_integralFiniteAdeles
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (continuous_apply (A := fun w : InfinitePlace K => w.Completion) w).norm
        continuous_const
  · rintro _ ⟨k, rfl⟩ ⟨hinf, hf⟩
    obtain ⟨z, rfl⟩ := exists_eq_of_forall_mem_adicCompletionIntegers K k hf
    have hz : ∀ w : InfinitePlace K, w z < 1 := fun w => by
      have := hinf w
      rwa [show (algebraMap K 𝔸[K] (z : K)).1 = algebraMap K K∞ (z : K) from rfl,
        norm_algebraMap_apply] at this
    rw [eq_zero_of_forall_infinitePlace_lt_one K z hz]
    simp

/- English proof (translation)
The claim follows from `haveI := discreteTopology_principalSubgroup K AddSubgroup.isClosed_of_discrete`.
-/
theorem isClosed_principalSubgroup :
    IsClosed (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) :=
  haveI := discreteTopology_principalSubgroup K
  AddSubgroup.isClosed_of_discrete

noncomputable def fundamentalSet : Set 𝔸[K] :=
  fundamentalSetInfinite K ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))

/- English proof (translation)
Take `⟨k₁, hk₁⟩` from `exists_sub_mem_integralFiniteAdeles x.2`. Take `⟨z, hz, -⟩` from `existsUnique_sub_mem_fundamentalSetInfinite K (x.1 - algebraMap K K∞ k₁)`. Use `⟨k₁ + z, ⟨?_, ?_⟩, fun k hk => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x.1 - algebraMap K K∞ (k₁ + z) ∈ _`. Rewrite using `[map_add, ← sub_sub, ← IsScalarTower.algebraMap_apply]`.

Conclude with `hz`. Express the relevant statement in the definitionally equal form `x.2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) (k₁ + z) ∈ _`. Rewrite using `[map_add, ← sub_sub]`. Conclude with `Subring.sub_mem _ hk₁ (algebraMap_integers_mem_integralFiniteAdeles K z)`. Take `⟨hkinf, hkf⟩` from `hk`.

Express the relevant statement in the definitionally equal form `x.1 - algebraMap K K∞ k ∈ fundamentalSetInfinite K at hkinf`. Express the relevant statement in the definitionally equal form `x.2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) k ∈ integralFiniteAdeles (𝓞 K) K at hkf`. Establish `hdiff : algebraMap K (FiniteAdeleRing (𝓞 K) K) (k - (k₁ + z)) ∈ integralFiniteAdeles (𝓞 K) K`. Establish `h2` using `Subring.sub_mem _ (Subring.sub_mem _ hk₁ hkf) (algebraMap_integers_mem_integralFiniteAdeles K z)`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [map_sub, map_add]`. Normalize the expressions using the abelian group laws. Take `⟨u, hu⟩` from `exists_eq_of_forall_mem_adicCompletionIntegers K _ hdiff`. Establish `h1 : z + u = z`. Use `(existsUnique_sub_mem_fundamentalSetInfinite K (x.1 - algebraMap K K∞ k₁)).unique ?_ hz` and prove the remaining obligations.

Use `hkinf using 1` and compare the differences between its conclusion and the goal. Establish `hu' : algebraMap (𝓞 K) K u = k - (k₁ + algebraMap (𝓞 K) K z)` using `hu`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K) K K∞, map_add, hu']`. Simplify using `only [map_sub, map_add]`. Normalize the expressions using the abelian group laws.

Establish `hu0 : u = 0` using `by simpa using h1`. Rewrite `hu` using `[hu0]`. Establish `: k - (k₁ + z) = 0` using `by rw [← hu]; simp`. Conclude with `sub_eq_zero.mp this`.
-/
theorem existsUnique_sub_mem_fundamentalSet (x : 𝔸[K]) :
    ∃! k : K, x - algebraMap K 𝔸[K] k ∈ fundamentalSet K := by
  obtain ⟨k₁, hk₁⟩ := exists_sub_mem_integralFiniteAdeles x.2
  obtain ⟨z, hz, -⟩ := existsUnique_sub_mem_fundamentalSetInfinite K (x.1 - algebraMap K K∞ k₁)
  refine ⟨k₁ + z, ⟨?_, ?_⟩, fun k hk => ?_⟩
  · change x.1 - algebraMap K K∞ (k₁ + z) ∈ _
    rw [map_add, ← sub_sub, ← IsScalarTower.algebraMap_apply]
    exact hz
  · change x.2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) (k₁ + z) ∈ _
    rw [map_add, ← sub_sub]
    exact Subring.sub_mem _ hk₁ (algebraMap_integers_mem_integralFiniteAdeles K z)
  · obtain ⟨hkinf, hkf⟩ := hk
    change x.1 - algebraMap K K∞ k ∈ fundamentalSetInfinite K at hkinf
    change x.2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) k ∈ integralFiniteAdeles (𝓞 K) K at hkf

    have hdiff : algebraMap K (FiniteAdeleRing (𝓞 K) K) (k - (k₁ + z)) ∈
        integralFiniteAdeles (𝓞 K) K := by
      have h2 := Subring.sub_mem _ (Subring.sub_mem _ hk₁ hkf)
        (algebraMap_integers_mem_integralFiniteAdeles K z)
      convert h2 using 1
      simp only [map_sub, map_add]
      abel
    obtain ⟨u, hu⟩ := exists_eq_of_forall_mem_adicCompletionIntegers K _ hdiff
    have h1 : z + u = z := by
      refine (existsUnique_sub_mem_fundamentalSetInfinite K (x.1 - algebraMap K K∞ k₁)).unique
        ?_ hz
      convert hkinf using 1
      have hu' : algebraMap (𝓞 K) K u = k - (k₁ + algebraMap (𝓞 K) K z) := hu
      rw [IsScalarTower.algebraMap_apply (𝓞 K) K K∞, map_add, hu']
      simp only [map_sub, map_add]
      abel
    have hu0 : u = 0 := by simpa using h1
    rw [hu0] at hu
    have : k - (k₁ + z) = 0 := by rw [← hu]; simp
    exact sub_eq_zero.mp this

/- English proof (translation)
Use `⟨closure (fundamentalSetInfinite K), isCompact_closure_fundamentalSetInfinite K, fun x => ?_⟩` and prove the remaining obligations. Take `⟨k, ⟨hinf, hf⟩, -⟩` from `existsUnique_sub_mem_fundamentalSet K x`. Conclude with `⟨k, subset_closure hinf, hf⟩`.
-/
theorem exists_isCompact_forall_exists_sub_mem :
    ∃ C : Set K∞, IsCompact C ∧ ∀ x : 𝔸[K], ∃ k : K, x - algebraMap K 𝔸[K] k ∈
      C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  refine ⟨closure (fundamentalSetInfinite K), isCompact_closure_fundamentalSetInfinite K,
    fun x => ?_⟩
  obtain ⟨k, ⟨hinf, hf⟩, -⟩ := existsUnique_sub_mem_fundamentalSet K x
  exact ⟨k, subset_closure hinf, hf⟩

end GroundTheory.Global
