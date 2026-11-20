import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClopenComponents
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIrreducibleConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use `le_antisymm ?_ ?_` and prove the remaining obligations. Introduce `f hf`. Take `⟨z₀, hz₀W, hz₀J⟩` from `hne`. Simplify using `only [mem_zeroLocus_iff, not_forall] at hz₀J`. Take `⟨g, hgJ, hg⟩` from `hz₀J`.

Establish `hgW : g ∉ W` using `fun h => hg (hz₀W g h)`. Establish `hfg : f * g ∈ W`. Rewrite using `[← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W, mem_vanishingIdeal_iff]`. Introduce `z hz`. Distinguish the cases in `hzJ : z ∈ zeroLocus ℂ J`.

Rewrite using `[map_mul, hzJ g hgJ, mul_zero]`. Rewrite using `[map_mul, (mem_vanishingIdeal_iff.mp hf) z ⟨hz, hzJ⟩, zero_mul]`. Conclude with `(hW.mem_or_mem hfg).resolve_right hgW`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem vanishingIdeal_zeroLocus_diff_of_nonempty {σ : Type} [Fintype σ]
    (W J : Ideal (MvPolynomial σ ℂ)) [hW : W.IsPrime]
    (hne : (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty) :
    vanishingIdeal ℂ (zeroLocus ℂ W \ zeroLocus ℂ J) = W := by
  refine le_antisymm ?_ ?_
  · intro f hf
    obtain ⟨z₀, hz₀W, hz₀J⟩ := hne
    simp only [mem_zeroLocus_iff, not_forall] at hz₀J
    obtain ⟨g, hgJ, hg⟩ := hz₀J
    have hgW : g ∉ W := fun h => hg (hz₀W g h)
    have hfg : f * g ∈ W := by
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W, mem_vanishingIdeal_iff]
      intro z hz
      by_cases hzJ : z ∈ zeroLocus ℂ J
      · rw [map_mul, hzJ g hgJ, mul_zero]
      · rw [map_mul, (mem_vanishingIdeal_iff.mp hf) z ⟨hz, hzJ⟩, zero_mul]
    exact (hW.mem_or_mem hfg).resolve_right hgW
  · calc W ≤ vanishingIdeal ℂ (zeroLocus ℂ W) := le_vanishingIdeal_zeroLocus W
      _ ≤ _ := vanishingIdeal_anti_mono Set.sdiff_subset

variable (ι) in

def multiIrrelevantIdeal : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  Ideal.span (Set.range fun i : (∀ k, ι k) => ∏ k, (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℂ))

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[multiIrrelevantIdeal, zeroLocus_span]`. Simplify using `only [Set.mem_ofPred_eq, Set.forall_mem_range, not_forall, map_prod, aeval_X]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi⟩ k`. Conclude with `⟨i k, fun h => hi (Finset.prod_eq_zero (Finset.mem_univ k) h)⟩`.

Introduce `h choose i hi using h`. Conclude with `⟨i, Finset.prod_ne_zero_iff.mpr fun k _ => hi k⟩`.
-/
theorem not_mem_zeroLocus_multiIrrelevantIdeal (z : (Σ k, ι k) → ℂ) :
    z ∉ zeroLocus ℂ (multiIrrelevantIdeal ι) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  rw [multiIrrelevantIdeal, zeroLocus_span]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, not_forall, map_prod, aeval_X]
  constructor
  · rintro ⟨i, hi⟩ k
    exact ⟨i k, fun h => hi (Finset.prod_eq_zero (Finset.mem_univ k) h)⟩
  · intro h
    choose i hi using h
    exact ⟨i, Finset.prod_ne_zero_iff.mpr fun k _ => hi k⟩

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Use extensionality with `z`. Rewrite using `[Set.mem_sdiff, not_mem_zeroLocus_multiIrrelevantIdeal]`. Simplify using `only [mcPts, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hb, hv⟩`.

Use `⟨fun p hp => ?_, hb⟩` and prove the remaining obligations. Establish `hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z)`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `f hf`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`.

Conclude with `hv f hf`. Establish `h0` using `RingHom.mem_ker.mp (hle hp)`. Conclude with `h0`. Introduce and unpack `⟨hz, hb⟩`. Use `⟨hb, fun f hf => ?_⟩` and prove the remaining obligations.

Use `hz _ (Ideal.mem_map_of_mem _ hf)` as an intermediate fact. Conclude with `this`.
-/
theorem mcPts_eq_zeroLocus_diff (P : Ideal (MRing ι)) :
    mcPts P = zeroLocus ℂ (P.map (MvPolynomial.map (Int.castRingHom ℂ))) \
      zeroLocus ℂ (multiIrrelevantIdeal ι) := by
  ext z
  rw [Set.mem_sdiff, not_mem_zeroLocus_multiIrrelevantIdeal]
  simp only [mcPts, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hb, hv⟩
    refine ⟨fun p hp => ?_, hb⟩
    have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z) := by
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact hv f hf
    have h0 := RingHom.mem_ker.mp (hle hp)
    exact h0
  · rintro ⟨hz, hb⟩
    refine ⟨hb, fun f hf => ?_⟩
    have := hz _ (Ideal.mem_map_of_mem _ hf)
    exact this

/- English proof (translation)
Introduce `K _ _ ι _ P e A _ hAsub hA`. Use `set PC := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC`. Use `set J := multiIrrelevantIdeal ι with hJ`. Establish `hmc : mcPts P = zeroLocus ℂ PC \ zeroLocus ℂ J` using `mcPts_eq_zeroLocus_diff P`. Establish `hfin` using `Ideal.finite_minimalPrimes_of_isNoetherianRing _ PC`.

Set `S` to `hfin.toFinset.filter fun W => (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty ∧ zeroLocus ℂ W \ zeroLocus ℂ J ⊆ A`. Establish `hS : ∀ W ∈ S, W ∈ PC.minimalPrimes ∧ (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty ∧ zeroLocus ℂ W \ zeroLocus ℂ J ⊆ A`. Introduce `W hW`. Rewrite `hW` using `[Finset.mem_filter, Set.Finite.mem_toFinset]`. Conclude with `hW`.

Establish `hcover : ∀ z ∈ A, ∃ W ∈ S, z ∈ zeroLocus ℂ W \ zeroLocus ℂ J`. Introduce `z hz`. Establish `hzm : z ∈ mcPts P` using `hAsub hz`. Rewrite `hzm` using `[hmc]`. Take `⟨hzPC, hzJ⟩` from `hzm`.

Establish `hker : PC ≤ RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ℂ)` using `fun p hp => RingHom.mem_ker.mpr (hzPC p hp)`. Establish `: (RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ℂ)).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨W, hWmin, hWle⟩` from `Ideal.exists_minimalPrimes_le hker`. Establish `hzW : z ∈ zeroLocus ℂ W \ zeroLocus ℂ J` using `⟨fun p hp => RingHom.mem_ker.mp (hWle hp), hzJ⟩`. Establish `hsub : zeroLocus ℂ W \ zeroLocus ℂ J ⊆ mcPts P`.

Rewrite using `[hmc]`. Conclude with `Set.sdiff_subset_sdiff_left (zeroLocus_anti_mono hWmin.1.2)`. Establish `hpc : IsPreconnected (zeroLocus ℂ W \ zeroLocus ℂ J)` using `h _ W J hWmin.1.1`. Establish `hpc' : IsPreconnected (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' (zeroLocus ℂ W \ zeroLocus ℂ J))`. Rewrite using `[← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe, Set.inter_eq_right.mpr hsub]`.

Conclude with `hpc`. Establish `hin` using `hpc'.subset_isClopen hA ⟨⟨z, hsub hzW⟩, hzW, hz⟩`. Use `⟨W, ?_, hzW⟩` and prove the remaining obligations. Rewrite using `[Finset.mem_filter, Set.Finite.mem_toFinset]`. Conclude with `⟨hWmin, ⟨z, hzW⟩, fun y hy => hin (show (⟨y, hsub hy⟩ : mcPts P) ∈ _ from hy)⟩`.

Establish `hAU : A = ⋃ W ∈ S, (zeroLocus ℂ W \ zeroLocus ℂ J)`. Use extensionality with `z`. Simplify using `only [Set.mem_iUnion, exists_prop]`. Conclude with `⟨fun hz => hcover z hz, fun ⟨W, hW, hz⟩ => (hS W hW).2.2 hz⟩`. Use `⟨S, fun W hW => (hS W hW).1, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `z`. Rewrite using `[hAU, hmc]`. Simplify using `only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨W, hW, hzW, hzJ⟩`.

Conclude with `⟨⟨fun p hp => hzW p ((hS W hW).1.1.2 hp), hzJ⟩, W, hW, hzW⟩`. Introduce and unpack `⟨⟨_, hzJ⟩, W, hW, hzW⟩`. Conclude with `⟨W, hW, hzW, hzJ⟩`. Rewrite using `[hAU]`. Use extensionality with `f`.

Rewrite using `[mem_vanishingIdeal_iff]`. Simplify using `only [Submodule.mem_iInf]`. Prove the components needed by the constructor for the conclusion. Introduce `hf W hW`. Establish `: W.IsPrime` using `(hS W hW).1.1.1`.

Rewrite using `[← vanishingIdeal_zeroLocus_diff_of_nonempty W J (hS W hW).2.1, mem_vanishingIdeal_iff]`. Conclude with `fun x hx => hf x (Set.mem_biUnion hW hx)`. Introduce `hf x hx`. Take `⟨W, hW, hxW⟩` from `Set.mem_iUnion₂.mp hx`. Establish `: W.IsPrime` using `(hS W hW).1.1.1`.

Establish `hfW` using `hf W hW`. Rewrite `hfW` using `[← vanishingIdeal_zeroLocus_diff_of_nonempty W J (hS W hW).2.1, mem_vanishingIdeal_iff]`. Conclude with `hfW x hxW`.
-/
theorem ClopenComponents.proof (h : IrreducibleConnected.Statement) : ClopenComponents.Statement := by
  classical
  intro K _ _ ι _ P e A _ hAsub hA
  set PC := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC
  set J := multiIrrelevantIdeal ι with hJ
  have hmc : mcPts P = zeroLocus ℂ PC \ zeroLocus ℂ J := mcPts_eq_zeroLocus_diff P
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing _ PC
  let S := hfin.toFinset.filter fun W =>
    (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty ∧ zeroLocus ℂ W \ zeroLocus ℂ J ⊆ A
  have hS : ∀ W ∈ S, W ∈ PC.minimalPrimes ∧ (zeroLocus ℂ W \ zeroLocus ℂ J).Nonempty ∧
      zeroLocus ℂ W \ zeroLocus ℂ J ⊆ A := by
    intro W hW
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hW
    exact hW
  have hcover : ∀ z ∈ A, ∃ W ∈ S, z ∈ zeroLocus ℂ W \ zeroLocus ℂ J := by
    intro z hz
    have hzm : z ∈ mcPts P := hAsub hz
    rw [hmc] at hzm
    obtain ⟨hzPC, hzJ⟩ := hzm
    have hker : PC ≤ RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ℂ) :=
      fun p hp => RingHom.mem_ker.mpr (hzPC p hp)
    have : (RingHom.ker (aeval z : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] ℂ)).IsPrime := RingHom.ker_isPrime _
    obtain ⟨W, hWmin, hWle⟩ := Ideal.exists_minimalPrimes_le hker
    have hzW : z ∈ zeroLocus ℂ W \ zeroLocus ℂ J := ⟨fun p hp => RingHom.mem_ker.mp (hWle hp), hzJ⟩
    have hsub : zeroLocus ℂ W \ zeroLocus ℂ J ⊆ mcPts P := by
      rw [hmc]
      exact Set.sdiff_subset_sdiff_left (zeroLocus_anti_mono hWmin.1.2)
    have hpc : IsPreconnected (zeroLocus ℂ W \ zeroLocus ℂ J) := h _ W J hWmin.1.1
    have hpc' : IsPreconnected (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' (zeroLocus ℂ W \ zeroLocus ℂ J)) := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        Set.inter_eq_right.mpr hsub]
      exact hpc
    have hin := hpc'.subset_isClopen hA ⟨⟨z, hsub hzW⟩, hzW, hz⟩
    refine ⟨W, ?_, hzW⟩
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨hWmin, ⟨z, hzW⟩, fun y hy => hin (show (⟨y, hsub hy⟩ : mcPts P) ∈ _ from hy)⟩
  have hAU : A = ⋃ W ∈ S, (zeroLocus ℂ W \ zeroLocus ℂ J) := by
    ext z
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun hz => hcover z hz, fun ⟨W, hW, hz⟩ => (hS W hW).2.2 hz⟩
  refine ⟨S, fun W hW => (hS W hW).1, ?_, ?_⟩
  · ext z
    rw [hAU, hmc]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]
    constructor
    · rintro ⟨W, hW, hzW, hzJ⟩
      exact ⟨⟨fun p hp => hzW p ((hS W hW).1.1.2 hp), hzJ⟩, W, hW, hzW⟩
    · rintro ⟨⟨_, hzJ⟩, W, hW, hzW⟩
      exact ⟨W, hW, hzW, hzJ⟩
  · rw [hAU]
    ext f
    rw [mem_vanishingIdeal_iff]
    simp only [Submodule.mem_iInf]
    constructor
    · intro hf W hW
      have : W.IsPrime := (hS W hW).1.1.1
      rw [← vanishingIdeal_zeroLocus_diff_of_nonempty W J (hS W hW).2.1, mem_vanishingIdeal_iff]
      exact fun x hx => hf x (Set.mem_biUnion hW hx)
    · intro hf x hx
      obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp hx
      have : W.IsPrime := (hS W hW).1.1.1
      have hfW := hf W hW
      rw [← vanishingIdeal_zeroLocus_diff_of_nonempty W J (hS W hW).2.1, mem_vanishingIdeal_iff] at hfW
      exact hfW x hxW

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
