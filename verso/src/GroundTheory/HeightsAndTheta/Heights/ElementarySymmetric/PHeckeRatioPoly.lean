import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.HeckeRatioPoly
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.JPolyLeading
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.HeckeRatioPoleOrders
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PHeckeRatioInvariant
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PHeckeRatioExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PLevelOneQExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PJQExpansion
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PIntSeriesRing
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PIntSeriesInv
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PDeltaIntSeries
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PIntSeriesNorm
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PHeckeRatioHolo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm GroundTheory.Global.Elliptic Polynomial Filter Topology

noncomputable section

namespace HeckeRatioPoly

/- English proof (translation)
Take `⟨hH, hE⟩` from `HeckeRatioExpansion.proof IntSeriesRing.proof IntSeriesInv.proof DeltaIntSeries.proof (IntSeriesNorm.proof IntSeriesRing.proof) HeckeRatioHolo.proof p hp k`. Conclude with `LevelOneQExpansion.proof JQExpansion.proof _ hH (fun γ τ ↦ by simp only [HeckeRatioInvariant.proof p hp γ τ]) hE`.
-/
theorem exists_poly (p : ℕ) (hp : p.Prime) (k : ℕ) :
    ∃ Q : ℤ[X], ∀ τ : ℍ, (heckeRatios ⟨p, hp.pos⟩ τ).esymm k = aeval (modularJ τ) Q := by
  obtain ⟨hH, hE⟩ := HeckeRatioExpansion.proof IntSeriesRing.proof IntSeriesInv.proof
    DeltaIntSeries.proof (IntSeriesNorm.proof IntSeriesRing.proof) HeckeRatioHolo.proof p hp k
  exact LevelOneQExpansion.proof JQExpansion.proof _ hH
    (fun γ τ ↦ by simp only [HeckeRatioInvariant.proof p hp γ τ]) hE

/- English proof (translation)
Establish `hq` using `qParam_tendsto_atImInfty (h := 1) one_pos`. Use `⟨?_, fun hd ↦ ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `h1` using `(hq.pow (Q.natDegree - m)).mul h`.

Rewrite `h1` using `[zero_pow (by omega), zero_mul]`. Establish `h0 : (Q.leadingCoeff : ℂ) = 0` using `tendsto_nhds_unique (hA Q) (h1.congr fun τ ↦ by`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le])`. Establish `hQ : Q = 0` using `leadingCoeff_eq_zero.1 (by exact_mod_cast h0)`. Simplify using `[hQ] at hlt`.

Establish `h2` using `hA Q`. Rewrite `h2` using `[hd]`. Conclude with `tendsto_nhds_unique h2 h`.
-/
theorem natDegree_le (hA : JPolyLeading.Statement) {Q : ℤ[X]} {m : ℕ} {L : ℂ}
    (h : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ m * aeval (modularJ τ) Q)
      atImInfty (𝓝 L)) :
    Q.natDegree ≤ m ∧ (Q.natDegree = m → (Q.leadingCoeff : ℂ) = L) := by
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  refine ⟨?_, fun hd ↦ ?_⟩
  · by_contra hlt
    rw [not_le] at hlt
    have h1 := (hq.pow (Q.natDegree - m)).mul h
    rw [zero_pow (by omega), zero_mul] at h1
    have h0 : (Q.leadingCoeff : ℂ) = 0 := tendsto_nhds_unique (hA Q) (h1.congr fun τ ↦ by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le])
    have hQ : Q = 0 := leadingCoeff_eq_zero.1 (by exact_mod_cast h0)
    simp [hQ] at hlt
  · have h2 := hA Q
    rw [hd] at h2
    exact tendsto_nhds_unique h2 h

/- English proof (translation)
Establish `hq` using `qParam_tendsto_atImInfty (h := 1) one_pos`. Establish `h1` using `(hq.pow (m - Q.natDegree)).mul (hA Q)`. Rewrite `h1` using `[zero_pow (by omega), zero_mul]`. Conclude with `tendsto_nhds_unique h (h1.congr fun τ ↦ by`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le])`.
-/
theorem limit_eq_zero (hA : JPolyLeading.Statement) {Q : ℤ[X]} {m : ℕ} {L : ℂ}
    (h : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ m * aeval (modularJ τ) Q)
      atImInfty (𝓝 L)) (hlt : Q.natDegree < m) : L = 0 := by
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have h1 := (hq.pow (m - Q.natDegree)).mul (hA Q)
  rw [zero_pow (by omega), zero_mul] at h1
  exact tendsto_nhds_unique h (h1.congr fun τ ↦ by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le])

end HeckeRatioPoly

open HeckeRatioPoly in

/- English proof (translation)
Introduce `p hp hodd`. Use `choose Q hQ using exists_poly p hp`. Take `⟨h1, h2, h3⟩` from `hB p hp hodd`. Establish `hp3 : 3 ≤ p`. Use `hp.two_le` as an intermediate fact.

Break down `hodd with ⟨r, rfl⟩` into its components or cases. Use linear arithmetic over natural numbers and integers. Establish `ht : ∀ k {L : ℂ}, Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ (p - 1) * (heckeRatios ⟨p, hp.pos⟩ τ).esymm k) atImInfty (𝓝 L) → Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ (p - 1) * aeval (modularJ τ) (Q k)) atImInfty (𝓝 L)` using `fun k _ h ↦ h.congr fun τ ↦ by rw [hQ]`. Use `⟨Q, hQ, fun k hk ↦ ?_, ?_⟩` and prove the remaining obligations. Take `⟨hle, heq⟩` from `natDegree_le hA (ht k (h1 k hk))`.

Use `lt_of_le_of_ne hle fun hd ↦ ?_` and prove the remaining obligations. Establish `hQ0 : Q k = 0` using `leadingCoeff_eq_zero.1 (by exact_mod_cast heq hd)`. Rewrite `hd` using `[hQ0, natDegree_zero]`. Use linear arithmetic over natural numbers and integers. Establish `htp` using `ht p h2`.

Take `⟨hle, heq⟩` from `natDegree_le hA htp`. Establish `hd : (Q p).natDegree = p - 1` using `le_antisymm hle (not_lt.1 fun hlt ↦ one_ne_zero (limit_eq_zero hA htp hlt))`. Establish `hl : (Q p).leadingCoeff = 1` using `by exact_mod_cast heq hd`. Use `⟨hl, hd, ?_⟩` and prove the remaining obligations. Establish `ht3 : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ 0 * aeval (modularJ τ) (Q (p + 1))) atImInfty (𝓝 ((p : ℂ) ^ 12))` using `h3.congr fun τ ↦ by rw [hQ, pow_zero, one_mul]`.

Take `⟨hle3, heq3⟩` from `natDegree_le hA ht3`. Establish `hd3 : (Q (p + 1)).natDegree = 0` using `by omega`. Establish `hc` using `heq3 hd3`. Rewrite `hc` using `[leadingCoeff, hd3]`. Rewrite using `[eq_C_of_natDegree_eq_zero hd3]`.

Use `congr 1`. Conclude with `hc` after adjusting the coercions.
-/
theorem HeckeRatioPoly.proof (hA : JPolyLeading.Statement) (hB : HeckeRatioPoleOrders.Statement) :
    HeckeRatioPoly.Statement := by
  intro p hp hodd
  choose Q hQ using exists_poly p hp
  obtain ⟨h1, h2, h3⟩ := hB p hp hodd
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hodd with ⟨r, rfl⟩
    omega
  have ht : ∀ k {L : ℂ}, Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ (p - 1) *
      (heckeRatios ⟨p, hp.pos⟩ τ).esymm k) atImInfty (𝓝 L) →
      Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ (p - 1) * aeval (modularJ τ) (Q k))
        atImInfty (𝓝 L) := fun k _ h ↦ h.congr fun τ ↦ by rw [hQ]
  refine ⟨Q, hQ, fun k hk ↦ ?_, ?_⟩
  · obtain ⟨hle, heq⟩ := natDegree_le hA (ht k (h1 k hk))
    refine lt_of_le_of_ne hle fun hd ↦ ?_
    have hQ0 : Q k = 0 := leadingCoeff_eq_zero.1 (by exact_mod_cast heq hd)
    rw [hQ0, natDegree_zero] at hd
    omega
  · have htp := ht p h2
    obtain ⟨hle, heq⟩ := natDegree_le hA htp
    have hd : (Q p).natDegree = p - 1 :=
      le_antisymm hle (not_lt.1 fun hlt ↦ one_ne_zero (limit_eq_zero hA htp hlt))
    have hl : (Q p).leadingCoeff = 1 := by exact_mod_cast heq hd
    refine ⟨hl, hd, ?_⟩
    have ht3 : Tendsto (fun τ : ℍ ↦ Function.Periodic.qParam 1 τ ^ 0 *
        aeval (modularJ τ) (Q (p + 1))) atImInfty (𝓝 ((p : ℂ) ^ 12)) :=
      h3.congr fun τ ↦ by rw [hQ, pow_zero, one_mul]
    obtain ⟨hle3, heq3⟩ := natDegree_le hA ht3
    have hd3 : (Q (p + 1)).natDegree = 0 := by omega
    have hc := heq3 hd3
    rw [leadingCoeff, hd3] at hc
    rw [eq_C_of_natDegree_eq_zero hd3]
    congr 1
    exact_mod_cast hc

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
