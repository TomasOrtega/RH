import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermitianPairingRationalValues
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

/- English proof (translation)
Take `⟨m, hm0, hm⟩` from `exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)`. Use `⟨(m * m).natAbs, Int.natAbs_pos.2 (mul_ne_zero hm0 hm0), fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `hm (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Use `⟨(m : 𝓞 K) * ⟨m • c i, h⟩, ?_⟩` and prove the remaining obligations. Establish `h2 : (((m * m).natAbs : ℕ) : K) = (m : K) * m`.

Rewrite using `[← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg m)]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h2]`. Express the relevant statement in the definitionally equal form `((m : 𝓞 K) : K) * (m • c i) = _`.

Simplify using `[mul_assoc]`.
-/
theorem exists_nat_common_denom {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] (c : ι → K) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, ∃ a : 𝓞 K, (a : K) = (k : K) * c i := by
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
  refine ⟨(m * m).natAbs, Int.natAbs_pos.2 (mul_ne_zero hm0 hm0), fun i => ?_⟩
  have h := hm (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨(m : 𝓞 K) * ⟨m • c i, h⟩, ?_⟩
  have h2 : (((m * m).natAbs : ℕ) : K) = (m : K) * m := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg m)]; push_cast; rfl
  rw [h2]
  change ((m : 𝓞 K) : K) * (m • c i) = _
  simp [mul_assoc]

/- English proof (translation)
Establish `h` using `(YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a) hy`. Conclude with `h`.
-/
theorem smul_mem_YYl (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (a : 𝓞 D.host.K)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ YYl D L L') : (a : D.host.K) • y ∈ YYl D L L' := by
  have h := (YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a) hy
  exact h

/- English proof (translation)
Take `⟨s, y, y', hy, hy', hexp⟩` from `GlobalTheory.HomDual.exists_dual_family_hom D (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'`. Establish `hc : ∀ i, ∃ c : Fin r → D.host.K, ∑ j, c j • b j = y i` using `fun i => (Submodule.mem_span_range_iff_exists_fun D.host.K).1 (by rw [hb.2]; trivial)`. Use `choose c hc using hc`. Take `⟨k, hk, hden⟩` from `exists_nat_common_denom (K := D.host.K) (ι := (Fin s × Fin r) ⊕ (Fin s × Fin r)) (Sum.elim (fun p => c p.1 p.2) (fun p => hYY D (b p.2) (y' p.1)))`. Use `choose a ha using hden`.

Use `⟨k, hk, fun x hx => ?_, fun j => ?_⟩` and prove the remaining obligations. Establish `hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i)` using `fun i => GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i) choose t ht using hi`. Use `⟨fun j => ∑ i, t i * a (Sum.inl (i, j)), ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [hexp x]`. Rewrite using `[← Nat.cast_smul_eq_nsmul D.host.K]`.

Simplify using `only [← hc, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`. Use `congr 1`.

Rewrite using `[RingOfIntegers.coe_eq_algebraMap, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ha, ht]`. Simplify using `only [Sum.elim_inl]`. Expand and normalize the polynomial expressions, which then agree.

Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Rewrite using `[hexp (b j), ← Nat.cast_smul_eq_nsmul D.host.K, Finset.smul_sum]`. Use `(YYl D L L').sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Use `ha (Sum.inr (i, j))` as an intermediate fact.

Simplify using `only [Sum.elim_inr] at this`. Rewrite using `[← this]`. Conclude with `smul_mem_YYl D L L' _ (hy i)`.
-/
theorem exists_comm_YYl (D : D7) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hb : OnB D b) (hL : SD D L) (hL' : SD D L') :
    ∃ k : ℕ, 0 < k ∧ Comm D b k (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  have hc : ∀ i, ∃ c : Fin r → D.host.K, ∑ j, c j • b j = y i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun D.host.K).1 (by rw [hb.2]; trivial)
  choose c hc using hc
  obtain ⟨k, hk, hden⟩ := exists_nat_common_denom (K := D.host.K) (ι := (Fin s × Fin r) ⊕ (Fin s × Fin r))
    (Sum.elim (fun p => c p.1 p.2) (fun p => hYY D (b p.2) (y' p.1)))
  choose a ha using hden
  refine ⟨k, hk, fun x hx => ?_, fun j => ?_⟩
  · have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine ⟨fun j => ∑ i, t i * a (Sum.inl (i, j)), ?_⟩
    conv_lhs => rw [hexp x]
    rw [← Nat.cast_smul_eq_nsmul D.host.K]
    simp only [← hc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [RingOfIntegers.coe_eq_algebraMap, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ha, ht]
    simp only [Sum.elim_inl]
    ring
  · apply AddSubgroup.subset_closure
    rw [hexp (b j), ← Nat.cast_smul_eq_nsmul D.host.K, Finset.smul_sum]
    refine (YYl D L L').sum_mem fun i _ => ?_
    rw [smul_smul]
    have := ha (Sum.inr (i, j))
    simp only [Sum.elim_inr] at this
    rw [← this]
    exact smul_mem_YYl D L L' _ (hy i)

end GlobalTheory.ThetaConj
