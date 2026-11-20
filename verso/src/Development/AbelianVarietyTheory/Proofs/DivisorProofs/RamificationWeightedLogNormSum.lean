import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeAlgebraMap

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.FlatDegreeCompare

/- English proof (translation)
Introduce `k k' _ _ _ _ i`. Use `letI : Algebra k k' := i.toAlgebra`. Use `⟨fun 𝔓 => 𝔓.under (𝓞 k), fun 𝔓 => 𝔓.asIdeal.ramificationIdx (𝓞 k), fun 𝔓 z => ?_, fun 𝔭 => ?_⟩` and prove the remaining obligations. Establish `: 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 k)).asIdeal` using `⟨rfl⟩`. Establish `h` using `HeightOneSpectrum.valuation_liesOver k' (𝔓.under (𝓞 k)) 𝔓 z`.

Rewrite `h` using `[Ideal.ramificationIdx'_eq_ramificationIdx _ _ (𝔓.under (𝓞 k)).ne_bot]`. Conclude with `h.symm`. Establish `hs` using `GlobalTheory.Adelic.HeightExt.sum_locDeg (L := k') 𝔭`. Establish `hpos : 0 < Module.finrank k k'` using `Module.finrank_pos`. Use `⟨(GlobalTheory.Adelic.HeightExt.finite_fiber (L := k') 𝔭).toFinset, fun 𝔓 => Set.Finite.mem_toFinset _, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.nonempty_iff_ne_empty]`. Introduce `h0`. Rewrite `hs` using `[h0, Finset.sum_empty]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Module.finrank_mul_finrank ℚ k k', ← hs, Nat.cast_mul, _root_.mul_assoc, Nat.cast_sum, Finset.sum_mul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun 𝔓 h𝔓 => ?_` and prove the remaining obligations. Establish `hu : 𝔓.under (𝓞 k) = 𝔭` using `((GlobalTheory.Adelic.HeightExt.finite_fiber (L := k') 𝔭).mem_toFinset).1 h𝔓`. Establish `: 𝔓.asIdeal.LiesOver 𝔭.asIdeal` using `⟨(congrArg HeightOneSpectrum.asIdeal hu).symm⟩`. Establish `hn` using `Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver 𝔓.asIdeal 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot`.

Rewrite `hn` using `[Ideal.inertiaDeg'_eq_inertiaDeg]`. Rewrite using `[hn, GlobalTheory.Adelic.HeightExt.locDeg]`. Use `push_cast`. Rewrite using `[Real.log_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_under_valuation_sum_log_absNorm : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k'), ∃ (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ), (∀ 𝔓 (z : k), 𝔓.valuation k' (i z) = (π 𝔓).valuation k z ^ ε 𝔓) ∧ ∀ 𝔭, ∃ s : Finset (HeightOneSpectrum (𝓞 k')), (∀ 𝔓, 𝔓 ∈ s ↔ π 𝔓 = 𝔭) ∧ s.Nonempty ∧ (Module.finrank ℚ k : ℝ) * ∑ 𝔓 ∈ s, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) = (Module.finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) := by
  intro k k' _ _ _ _ i
  letI : Algebra k k' := i.toAlgebra
  refine ⟨fun 𝔓 => 𝔓.under (𝓞 k), fun 𝔓 => 𝔓.asIdeal.ramificationIdx (𝓞 k), fun 𝔓 z => ?_, fun 𝔭 => ?_⟩
  · have : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 k)).asIdeal := ⟨rfl⟩
    have h := HeightOneSpectrum.valuation_liesOver k' (𝔓.under (𝓞 k)) 𝔓 z
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (𝔓.under (𝓞 k)).ne_bot] at h
    exact h.symm
  · have hs := GlobalTheory.Adelic.HeightExt.sum_locDeg (L := k') 𝔭
    have hpos : 0 < Module.finrank k k' := Module.finrank_pos
    refine ⟨(GlobalTheory.Adelic.HeightExt.finite_fiber (L := k') 𝔭).toFinset, fun 𝔓 => Set.Finite.mem_toFinset _, ?_, ?_⟩
    · rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hs
      omega
    · rw [← Module.finrank_mul_finrank ℚ k k', ← hs, Nat.cast_mul, _root_.mul_assoc, Nat.cast_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun 𝔓 h𝔓 => ?_
      have hu : 𝔓.under (𝓞 k) = 𝔭 := ((GlobalTheory.Adelic.HeightExt.finite_fiber (L := k') 𝔭).mem_toFinset).1 h𝔓
      have : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hu).symm⟩
      have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver 𝔓.asIdeal 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot
      rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
      rw [hn, GlobalTheory.Adelic.HeightExt.locDeg]
      push_cast
      rw [Real.log_pow]
      ring

end GlobalTheory.FlatDegreeCompare
