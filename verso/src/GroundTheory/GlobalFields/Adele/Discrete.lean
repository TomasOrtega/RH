import Mathlib
import GroundTheory.GlobalFields.Adele.Approximation
import GroundTheory.GlobalFields.Adele.IntegersLattice

namespace GroundTheory.Global

open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

variable (K : Type*) [Field K] [NumberField K]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_eq_of_forall_mem_adicCompletionIntegers (k : K)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    ∃ z : 𝓞 K, (z : K) = k := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K k ≤ 1 := fun v =>
    (coe_mem_adicCompletionIntegers_iff v k).mp (h v)
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K k hv
  exact ⟨z, hz⟩

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem algebraMap_integers_mem_integralFiniteAdeles (z : 𝓞 K) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (z : K) ∈ integralFiniteAdeles (𝓞 K) K := fun v =>
  (coe_mem_adicCompletionIntegers_iff v (z : K)).mpr (HeightOneSpectrum.valuation_le_one v z)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
theorem isClosed_principalSubgroup :
    IsClosed (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) :=
  haveI := discreteTopology_principalSubgroup K
  AddSubgroup.isClosed_of_discrete

noncomputable def fundamentalSet : Set 𝔸[K] :=
  fundamentalSetInfinite K ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Express the relevant assertion in an equivalent form by its definition.

Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply an available result and prove the equalities needed to match it to the conclusion. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_isCompact_forall_exists_sub_mem :
    ∃ C : Set K∞, IsCompact C ∧ ∀ x : 𝔸[K], ∃ k : K, x - algebraMap K 𝔸[K] k ∈
      C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  refine ⟨closure (fundamentalSetInfinite K), isCompact_closure_fundamentalSetInfinite K,
    fun x => ?_⟩
  obtain ⟨k, ⟨hinf, hf⟩, -⟩ := existsUnique_sub_mem_fundamentalSet K x
  exact ⟨k, subset_closure hinf, hf⟩

end GroundTheory.Global
