import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseVectorProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Use `⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Use `show z' p = (c p.1)⁻¹ * (c p.1 * z' p)`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]`.
-/
private theorem sameOrbit_symm_metric {K : Type} {ι : K → Type} {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  show z' p = (c p.1)⁻¹ * (c p.1 * z' p)
  rw [← mul_assoc, inv_mul_cancel₀ (hc p.1), one_mul]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h1`. Take `⟨d, hd, rfl⟩` from `h2`. Use `⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Use `show c p.1 * (d p.1 * z'' p) = c p.1 * d p.1 * z'' p`.

Rewrite using `[mul_assoc]`.
-/
private theorem sameOrbit_trans_metric {K : Type} {ι : K → Type} {z z' z'' : (Σ k, ι k) → ℂ}
    (h1 : SameOrbit z z') (h2 : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h1
  obtain ⟨d, hd, rfl⟩ := h2
  refine ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), ?_⟩
  funext p
  show c p.1 * (d p.1 * z'' p) = c p.1 * d p.1 * z'' p
  rw [mul_assoc]

/- English proof (translation)
Introduce `K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb z hz hzb`. Take `⟨hβmem, hβgood, hβc, hβorb⟩` from `bvec_good K ι Φ y Ψ N j M n BM l b hb`. Establish `h1 : SameOrbit (basePart M.blk z) (bvec BM l b)` using `sameOrbit_trans_metric hzb (sameOrbit_symm_metric hβorb)`. Take `⟨d, hd, hdz⟩` from `id h1`. Establish `hne : ∀ k, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0`.

Introduce `k`. Rewrite using `[hdz]`. Use `show d k * bvec BM l b ⟨k, (BM.F l).c k⟩ ≠ 0`. Rewrite using `[hβc k, mul_one]`. Conclude with `hd k`.

Take `⟨z₁, hz₁z, hz₁c⟩` from `GlobalTheory.CompanionTheory.Ar.PB.FibreCount.exists_normal_base M.blk (BM.F l).c z hne`. Establish `hb1 : SameOrbit (basePart M.blk z₁) (bvec BM l b)` using `sameOrbit_trans_metric (GlobalTheory.CompanionTheory.Ar.PB.FibreCount.basePart_orbit M.blk hz₁z) h1`. Establish `hbeq : basePart M.blk z₁ = bvec BM l b`. Take `⟨e, he, hez⟩` from `hb1`. Establish `he1 : ∀ k, e k = 1`.

Introduce `k`. Establish `hk` using `congrFun hez ⟨k, (BM.F l).c k⟩`. Establish `hk' : basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = e k * bvec BM l b ⟨k, (BM.F l).c k⟩` using `hk`. Rewrite `hk'` using `[hz₁c k, hβc k, mul_one]`. Conclude with `hk'.symm`.

Rewrite using `[hez]`. Use function extensionality and compare the values at `p`. Use `show e p.1 * bvec BM l b p = bvec BM l b p`. Rewrite using `[he1, one_mul]`. Establish `hz₁ : z₁ ∈ mcPts (mCoordIdeal y)`.

Take `⟨c, hc, hcz⟩` from `id hz₁z`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Take `⟨i, hi⟩` from `hz.1 k`. Use `⟨i, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcz]`. Conclude with `mul_ne_zero (hc k) hi`. Introduce `f hf`. Establish `hf' : f ∈ mCoordIdeal z₁`. Rewrite using `[GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit hz₁z]`.

Conclude with `GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hz hf`. Conclude with `eval_eq_zero_of_mem_mCoordIdeal hf'`. Establish `hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₁))`. Rewrite using `[hbeq]`. Conclude with `hβgood`.

Take `⟨h, hflag⟩` from `GlobalTheory.CompanionTheory.Ar.PB.CPts.flag_fwd M (BM.isFrame l) hz₁ hgood hz₁c`. Take `⟨_, hhb, hblocks⟩` from `hflag`. Use `⟨h, hhb, ?_⟩` and prove the remaining obligations. Establish `h2 : SameOrbit z₁ (flagPt M (BM.F l) (bvec BM l b) h)`. Apply `GlobalTheory.CompanionTheory.Ar.PB.FibreCount.sameOrbit_of_blocks M.blk` to reduce the goal to its premises.

Rewrite using `[basePart_flagPt, hbeq]`. Introduce `p k hpk`. Take `⟨a, ha, hza⟩` from `hblocks p k hpk`. Use `⟨a, ha, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[hza m, flagPt_step M (BM.F l) (bvec BM l b) h hpk m, hbeq]`.

Conclude with `sameOrbit_trans_metric (sameOrbit_symm_metric hz₁z) h2`.
-/
theorem exists_flagPt_of_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (l : Fin BM.q), ∀ b ∈ BM.O l, ∀ z ∈ mcPts (mCoordIdeal y), SameOrbit (basePart M.blk z) (BM.Rb.lift b b) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) ∧ SameOrbit z (FC.flagPt M (BM.F l) (FC.bvec BM l b) h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM l b hb z hz hzb
  obtain ⟨hβmem, hβgood, hβc, hβorb⟩ := bvec_good K ι Φ y Ψ N j M n BM l b hb
  have h1 : SameOrbit (basePart M.blk z) (bvec BM l b) :=
    sameOrbit_trans_metric hzb (sameOrbit_symm_metric hβorb)
  obtain ⟨d, hd, hdz⟩ := id h1
  have hne : ∀ k, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := by
    intro k
    rw [hdz]
    show d k * bvec BM l b ⟨k, (BM.F l).c k⟩ ≠ 0
    rw [hβc k, mul_one]
    exact hd k
  obtain ⟨z₁, hz₁z, hz₁c⟩ := GlobalTheory.CompanionTheory.Ar.PB.FibreCount.exists_normal_base M.blk (BM.F l).c z hne
  have hb1 : SameOrbit (basePart M.blk z₁) (bvec BM l b) :=
    sameOrbit_trans_metric (GlobalTheory.CompanionTheory.Ar.PB.FibreCount.basePart_orbit M.blk hz₁z) h1
  have hbeq : basePart M.blk z₁ = bvec BM l b := by
    obtain ⟨e, he, hez⟩ := hb1
    have he1 : ∀ k, e k = 1 := by
      intro k
      have hk := congrFun hez ⟨k, (BM.F l).c k⟩
      have hk' : basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = e k * bvec BM l b ⟨k, (BM.F l).c k⟩ := hk
      rw [hz₁c k, hβc k, mul_one] at hk'
      exact hk'.symm
    rw [hez]
    funext p
    show e p.1 * bvec BM l b p = bvec BM l b p
    rw [he1, one_mul]
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := by
    obtain ⟨c, hc, hcz⟩ := id hz₁z
    refine ⟨?_, ?_⟩
    · intro k
      obtain ⟨i, hi⟩ := hz.1 k
      refine ⟨i, ?_⟩
      rw [hcz]
      exact mul_ne_zero (hc k) hi
    · intro f hf
      have hf' : f ∈ mCoordIdeal z₁ := by
        rw [GlobalTheory.CompanionTheory.Ar.PB.FibreCount.mCoordIdeal_eq_of_orbit hz₁z]
        exact GlobalTheory.CompanionTheory.Ar.PB.CPts.mCoordIdeal_le hz hf
      exact eval_eq_zero_of_mem_mCoordIdeal hf'
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z₁)) := by
    rw [hbeq]
    exact hβgood
  obtain ⟨h, hflag⟩ := GlobalTheory.CompanionTheory.Ar.PB.CPts.flag_fwd M (BM.isFrame l) hz₁ hgood hz₁c
  obtain ⟨_, hhb, hblocks⟩ := hflag
  refine ⟨h, hhb, ?_⟩
  have h2 : SameOrbit z₁ (flagPt M (BM.F l) (bvec BM l b) h) := by
    apply GlobalTheory.CompanionTheory.Ar.PB.FibreCount.sameOrbit_of_blocks M.blk
    · rw [basePart_flagPt, hbeq]
    · intro p k hpk
      obtain ⟨a, ha, hza⟩ := hblocks p k hpk
      refine ⟨a, ha, fun m => ?_⟩
      rw [hza m, flagPt_step M (BM.F l) (bvec BM l b) h hpk m, hbeq]
  exact sameOrbit_trans_metric (sameOrbit_symm_metric hz₁z) h2

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
