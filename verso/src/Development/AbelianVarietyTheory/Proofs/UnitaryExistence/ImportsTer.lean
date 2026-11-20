import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

open IsDedekindDomain NumberField Filter Topology

namespace GlobalTheory.LocalNormBound

/- English proof (translation)
Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.1 hW`. Establish `hp : 0 < Ideal.absNorm v.asIdeal` using `Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))`. Use `set p := Ideal.absNorm v.asIdeal with hpdef`. Establish `hlt : Valued.v ((p : ℕ) : v.adicCompletion F) < 1`. Establish `h1 : ((p : ℕ) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F))`.

Simplify using the standard rewrite rules. Rewrite using `[h1]`. Establish `h2` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F (p : 𝓞 F))`. Establish `h3` using `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 (Ideal.absNorm_mem _)`. Conclude with `h2 ▸ h3`.

Establish `ht` using `Valued.tendsto_zero_pow_of_v_lt_one hlt`. Establish `hS` using `Valued.mem_nhds_zero.2 ⟨γ, subset_rfl (a := _)⟩`. Take `⟨n, hn⟩` from `(ht.eventually hS).exists`. Use `⟨p ^ n, pow_pos hp n, fun x hx => hγ ?_⟩` and prove the remaining obligations. Use `lt_of_le_of_lt ?_ hn` and prove the remaining obligations.

Rewrite using `[Valuation.restrict_le_iff, nsmul_eq_mul, map_mul, Nat.cast_pow]`. Conclude with `mul_le_of_le_one_right' hx`.
-/
theorem local_bound (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (W : Set (v.adicCompletion F)) (hW : W ∈ 𝓝 (0 : v.adicCompletion F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ v.adicCompletionIntegers F, N • x ∈ W := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hW
  have hp : 0 < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h))
  set p := Ideal.absNorm v.asIdeal with hpdef
  have hlt : Valued.v ((p : ℕ) : v.adicCompletion F) < 1 := by
    have h1 : ((p : ℕ) : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by
      simp
    rw [h1]
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F (p : 𝓞 F))
    have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 (Ideal.absNorm_mem _)
    exact h2 ▸ h3
  have ht := Valued.tendsto_zero_pow_of_v_lt_one hlt
  have hS := Valued.mem_nhds_zero.2 ⟨γ, subset_rfl (a := _)⟩
  obtain ⟨n, hn⟩ := (ht.eventually hS).exists
  refine ⟨p ^ n, pow_pos hp n, fun x hx => hγ ?_⟩
  refine lt_of_le_of_lt ?_ hn
  rw [Valuation.restrict_le_iff, nsmul_eq_mul, map_mul, Nat.cast_pow]
  exact mul_le_of_le_one_right' hx

/- English proof (translation)
Introduce `F _ _ U hU`. Set `φ : (Π v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F))) → FiniteAdeleRing (𝓞 F) F` to `RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite`. Establish `hφ : Continuous φ` using `RestrictedProduct.isEmbedding_structureMap.continuous`. Set `z : Π v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F))` to `fun v => ⟨0, zero_mem _⟩`. Establish `hz : φ z = 0` using `FiniteAdeleRing.ext F fun v => rfl`.

Establish `h1 : φ ⁻¹' U ∈ 𝓝 z` using `hφ.continuousAt.preimage_mem_nhds (hz ▸ hU)`. Rewrite `h1` using `[nhds_pi, Filter.mem_pi]`. Take `⟨I, hI, t, ht, hsub⟩` from `h1`. Establish `h2 : ∀ v : HeightOneSpectrum (𝓞 F), ∃ N : ℕ, 0 < N ∧ ∀ x (hx : x ∈ v.adicCompletionIntegers F), ⟨N • x, nsmul_mem hx N⟩ ∈ t v`. Introduce `v`.

Take `⟨W, hW, hWt⟩` from `(mem_nhds_subtype _ _ _).1 (ht v)`. Take `⟨N, hN, h⟩` from `local_bound F v W hW`. Conclude with `⟨N, hN, fun x hx => hWt (h x hx)⟩`. Use `choose n hn hnt using h2`. Use `⟨∏ v ∈ hI.toFinset, n v, Finset.prod_pos fun v _ => hn v, fun a ha => ?_⟩` and prove the remaining obligations.

Use `set N := ∏ v ∈ hI.toFinset, n v with hN`. Establish `h3 : φ (fun v => ⟨N • a v, nsmul_mem (ha v) N⟩) = N • a` using `FiniteAdeleRing.ext F fun v => rfl`. Rewrite using `[← h3]`. Use `hsub fun v hv => ?_` and prove the remaining obligations. Take `⟨k, hk⟩ : n v ∣ N` from `Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv)`.

Establish `h4` using `hnt v (k • a v) (nsmul_mem (ha v) k)`. Use `h4 using 2` and compare the differences between its conclusion and the goal. Rewrite using `[hk, mul_smul]`.
-/
theorem main : ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F], ∀ U ∈ nhds (0 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F), ∃ (N : ℕ), (0 : ℕ) < N ∧ ∀ (a : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F), (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (a : (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) → IsDedekindDomain.HeightOneSpectrum.adicCompletion F a) v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) → N • a ∈ U := by
  intro F _ _ U hU
  classical
  let φ : (Π v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F))) →
      FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hφ : Continuous φ := RestrictedProduct.isEmbedding_structureMap.continuous
  let z : Π v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => ⟨0, zero_mem _⟩
  have hz : φ z = 0 := FiniteAdeleRing.ext F fun v => rfl
  have h1 : φ ⁻¹' U ∈ 𝓝 z := hφ.continuousAt.preimage_mem_nhds (hz ▸ hU)
  rw [nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  have h2 : ∀ v : HeightOneSpectrum (𝓞 F), ∃ N : ℕ, 0 < N ∧
      ∀ x (hx : x ∈ v.adicCompletionIntegers F), ⟨N • x, nsmul_mem hx N⟩ ∈ t v := by
    intro v
    obtain ⟨W, hW, hWt⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨N, hN, h⟩ := local_bound F v W hW
    exact ⟨N, hN, fun x hx => hWt (h x hx)⟩
  choose n hn hnt using h2
  refine ⟨∏ v ∈ hI.toFinset, n v, Finset.prod_pos fun v _ => hn v, fun a ha => ?_⟩
  set N := ∏ v ∈ hI.toFinset, n v with hN
  have h3 : φ (fun v => ⟨N • a v, nsmul_mem (ha v) N⟩) = N • a :=
    FiniteAdeleRing.ext F fun v => rfl
  rw [← h3]
  refine hsub fun v hv => ?_
  obtain ⟨k, hk⟩ : n v ∣ N := Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv)
  have h4 := hnt v (k • a v) (nsmul_mem (ha v) k)
  convert h4 using 2
  rw [hk, mul_smul]

end GlobalTheory.LocalNormBound
