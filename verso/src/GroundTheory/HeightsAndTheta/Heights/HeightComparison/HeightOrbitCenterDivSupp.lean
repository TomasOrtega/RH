import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenter
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField MvPolynomial

def OrbitCenterDivSupp.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ),
    BlockNonzero x → Geo.IsMultiHomog (ι := blockIdx n) s a → s ∉ orbitIdeal x →
    ∀ v : FinitePlace (coordField x), s ∈ orbitCenter x v →
      orbitCenter x v ∈ Geo.divSupp (orbitIdeal x) s

/- English proof (translation)
Establish `: (Ideal.span {(2 : ℤ)}).IsPrime` using `(Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two`. Take `⟨Q, -, hQ, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(2 : ℤ)}) ⊥ (fun a ha ↦ by`. Rewrite `ha` using `[Ideal.mem_comap, Ideal.mem_bot, map_eq_zero_iff _ (algebraMap ℤ (𝓞 K)).injective_int]`. Simplify using `[ha])`. Establish `h2 : (2 : 𝓞 K) ∈ Q`.

Establish `: (2 : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K))` using `hQc ▸ Ideal.mem_span_singleton_self 2`. Simplify using `using this`. Establish `hne : Q ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `h2` using `[Ideal.mem_bot]`.

Conclude with `two_ne_zero h2`. Use `⟨FinitePlace.mk ⟨Q, hQ, hne⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[FinitePlace.mk_apply, show (2 : K) = algebraMap (𝓞 K) K 2 from (map_ofNat _ 2).symm]`. Conclude with `(FinitePlace.norm_lt_one_iff_mem (K := K) (v := (⟨Q, hQ, hne⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (2 : 𝓞 K)).mpr h2`.
-/
theorem exists_finitePlace_two_lt_one (K : Type) [Field K] [NumberField K] :
    ∃ v : FinitePlace K, v 2 < 1 := by
  have : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K)
    (Ideal.span {(2 : ℤ)}) ⊥ (fun a ha ↦ by
      rw [Ideal.mem_comap, Ideal.mem_bot,
        map_eq_zero_iff _ (algebraMap ℤ (𝓞 K)).injective_int] at ha
      simp [ha])
  have h2 : (2 : 𝓞 K) ∈ Q := by
    have : (2 : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self 2
    simpa using this
  have hne : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at h2
    exact two_ne_zero h2
  refine ⟨FinitePlace.mk ⟨Q, hQ, hne⟩, ?_⟩
  rw [FinitePlace.mk_apply, show (2 : K) = algebraMap (𝓞 K) K 2 from (map_ofNat _ 2).symm]
  exact (FinitePlace.norm_lt_one_iff_mem (K := K)
    (v := (⟨Q, hQ, hne⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (2 : 𝓞 K)).mpr h2

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_finitePlace_two_lt_one (coordField samplePoint)`. Use `⟨v, samplePoint_blockNonzero, (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial _ _), chartMonomial_notMem_orbitIdeal _ _ (fun _ ↦ by simp [samplePoint]) 1, ?_⟩` and prove the remaining obligations. Establish `hX : chartMonomial (n` using `fun _ : Unit ↦ 1) (fun _ ↦ 1) 1 = X ⟨(), 1⟩ := by`. Simplify using `[chartMonomial]`. Rewrite using `[hX]`.

Use `X_mem_orbitCenter _ _ () 1 ?_` and prove the remaining obligations. Establish `h1 : coordVec samplePoint () 1 = 2` using `Subtype.ext (by simp [coordVec, samplePoint]; rfl)`. Establish `h0 : coordVec samplePoint () 0 = 1` using `Subtype.ext (by simp [coordVec, samplePoint])`. Rewrite using `[h1]`. Combine the equalities or inequalities in the displayed calculation.
-/
example : ∃ v : FinitePlace (coordField samplePoint), BlockNonzero samplePoint ∧
    Geo.IsMultiHomog (ι := blockIdx (fun _ : Unit ↦ 1)) (chartMonomial (fun _ ↦ 1) 1) 1 ∧
    chartMonomial (fun _ ↦ 1) 1 ∉ orbitIdeal samplePoint ∧
    chartMonomial (fun _ ↦ 1) 1 ∈ orbitCenter samplePoint v := by
  obtain ⟨v, hv⟩ := exists_finitePlace_two_lt_one (coordField samplePoint)
  refine ⟨v, samplePoint_blockNonzero,
    (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial _ _),
    chartMonomial_notMem_orbitIdeal _ _ (fun _ ↦ by simp [samplePoint]) 1, ?_⟩
  have hX : chartMonomial (n := fun _ : Unit ↦ 1) (fun _ ↦ 1) 1 = X ⟨(), 1⟩ := by
    simp [chartMonomial]
  rw [hX]
  refine X_mem_orbitCenter _ _ () 1 ?_
  have h1 : coordVec samplePoint () 1 = 2 :=
    Subtype.ext (by simp [coordVec, samplePoint]; rfl)
  have h0 : coordVec samplePoint () 0 = 1 := Subtype.ext (by simp [coordVec, samplePoint])
  rw [h1]
  calc v 2 < 1 := hv
    _ = v (coordVec samplePoint () 0) := by rw [h0, map_one]
    _ ≤ ⨆ j, v (coordVec samplePoint () j) :=
      le_ciSup (f := fun j ↦ v (coordVec samplePoint () j)) (Set.finite_range _).bddAbove 0

end GroundTheory.Heights₂.Heights
