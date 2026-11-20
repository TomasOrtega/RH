import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsHermitianLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentedBundleSectionsRationalFunctionsDict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.AmpleGen

/- English proof (translation)
Introduce `k _ X _ p D _ P hA`. Take `⟨c, hc, N, s, hs⟩` from `hA.exists_isGenerated_pow`. Establish `hrep : P.Rep 0 (c : ℤ) (P.A.pow c)`. Use `Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1` as an intermediate fact. Simplify using `using this`.

Take `⟨e, -, hrange, hnu, -⟩` from `RepDict.rep_dict k X p P 0 c (P.A.pow c) hrep`. Establish `hmem : ∀ i, e (s i) ∈ P.H 0 c` using `fun i => by`. Establish `: e (s i) ∈ Set.range e` using `⟨s i, rfl⟩`. Rewrite `this` using `[hrange]`. Conclude with `this`.

Establish `hne : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (e (s i)) ≠ 0`. Introduce `σ y`. Take `⟨i, hi⟩` from `exists_mem_ptsIn hs y`. Use `⟨i, fun h0 => ?_⟩` and prove the remaining obligations. Establish `h2` using `hnu (s i) σ y`.

Establish `hpick` using `mem_pick ((P.A.pow c).φ σ).isLB y`. Establish `hv` using `(secVal_ne_zero_iff (s i) hpick).2 hi`. Establish `hpos : ((P.A.pow c).φ σ).nsq (secVal p σ (s i)) y ≠ 0` using `mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hv)) (Real.exp_pos _).ne'`. Rewrite `h2` using `[h0]`. Conclude with `hpos (by rw [← h2]; ring)`.

Use `⟨c, hc, fun j => ⟨N, fun i => e (s i) ^ j, fun i => ?_, fun σ y => ?_⟩⟩` and prove the remaining obligations. Take `⟨h1, -⟩` from `NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j`. Establish `e1 : (j : ℤ) * 0 = 0` using `by ring`. Establish `e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ)` using `by push_cast; ring`. Rewrite `h1` using `[e1, e2]`.

Conclude with `h1`. Take `⟨i, hi⟩` from `hne σ y`. Take `⟨-, h2⟩` from `NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j`. Establish `e1 : (j : ℤ) * 0 = 0` using `by ring`. Establish `e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ)` using `by push_cast; ring`.

Establish `h3` using `h2 σ y`. Rewrite `h3` using `[e1, e2]`. Conclude with `⟨i, by rw [h3]; exact pow_ne_zero _ hi⟩`.
-/
theorem exists_genAt_mul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ j : ℕ, GenAt P (c₀ * j) := by
  intro k _ X _ p D _ P hA
  obtain ⟨c, hc, N, s, hs⟩ := hA.exists_isGenerated_pow
  have hrep : P.Rep 0 (c : ℤ) (P.A.pow c) := by
    have := Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1
    simpa using this
  obtain ⟨e, -, hrange, hnu, -⟩ := RepDict.rep_dict k X p P 0 c (P.A.pow c) hrep
  have hmem : ∀ i, e (s i) ∈ P.H 0 c := fun i => by
    have : e (s i) ∈ Set.range e := ⟨s i, rfl⟩
    rw [hrange] at this
    exact this
  have hne : ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, P.nu 0 c σ y (e (s i)) ≠ 0 := by
    intro σ y
    obtain ⟨i, hi⟩ := exists_mem_ptsIn hs y
    refine ⟨i, fun h0 => ?_⟩
    have h2 := hnu (s i) σ y
    have hpick := mem_pick ((P.A.pow c).φ σ).isLB y
    have hv := (secVal_ne_zero_iff (s i) hpick).2 hi
    have hpos : ((P.A.pow c).φ σ).nsq (secVal p σ (s i)) y ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 hv)) (Real.exp_pos _).ne'
    rw [h0] at h2
    exact hpos (by rw [← h2]; ring)
  refine ⟨c, hc, fun j => ⟨N, fun i => e (s i) ^ j, fun i => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨h1, -⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h1
    exact h1
  · obtain ⟨i, hi⟩ := hne σ y
    obtain ⟨-, h2⟩ := NuPow.pow_mem_H_and_nu_pow k X p P 0 c (e (s i)) (hmem i) j
    have e1 : (j : ℤ) * 0 = 0 := by ring
    have e2 : (j : ℤ) * c = ((c * j : ℕ) : ℤ) := by push_cast; ring
    have h3 := h2 σ y
    rw [e1, e2] at h3
    exact ⟨i, by rw [h3]; exact pow_ne_zero _ hi⟩

end GlobalTheory.HSNef.AmpleGen
