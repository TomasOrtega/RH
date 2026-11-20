import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOfQBMemLatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLatticeStatement

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc Filter Topology

/- English proof (translation)
Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Establish `h0 : Tendsto (fun n : ℕ => (l : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0)`. Use `tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity) (inv_lt_one_of_one_lt₀ hl)` as an intermediate fact. Simplify using `using this`. Establish `hc : CauchySeq z` using `cauchySeq_of_le_tendsto_0' _ (fun n m hnm => by rw [dist_eq_norm]; exact h n m hnm) h0`.

Take `⟨y, hy⟩` from `cauchySeq_tendsto_of_complete hc`. Use `⟨y, fun n => ?_⟩` and prove the remaining obligations. Establish `h1 : ‖z n - y‖ ≤ (l : ℝ) ^ (-(n : ℤ))` using `le_of_tendsto ((tendsto_const_nhds.sub hy).norm) (eventually_atTop.2 ⟨n, fun m hm => h n m hm⟩)`. Rewrite `h1` using `[norm_sub_rev, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]`. Conclude with `h1`.
-/
theorem exists_padicInt_lim {l : ℕ} [Fact l.Prime] (z : ℕ → ℤ_[l])
    (h : ∀ n m, n ≤ m → ‖z n - z m‖ ≤ (l : ℝ) ^ (-(n : ℤ))) :
    ∃ y : ℤ_[l], ∀ n : ℕ, ∃ w : ℤ_[l], y - z n = (l : ℤ_[l]) ^ n * w := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : Tendsto (fun n : ℕ => (l : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    simpa using this
  have hc : CauchySeq z :=
    cauchySeq_of_le_tendsto_0' _ (fun n m hnm => by rw [dist_eq_norm]; exact h n m hnm) h0
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨y, fun n => ?_⟩
  have h1 : ‖z n - y‖ ≤ (l : ℝ) ^ (-(n : ℤ)) :=
    le_of_tendsto ((tendsto_const_nhds.sub hy).norm)
      (eventually_atTop.2 ⟨n, fun m hm => h n m hm⟩)
  rw [norm_sub_rev, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at h1
  exact h1

/- English proof (translation)
Use `choose z hz using hv`. Take `⟨y, hy⟩` from `exists_padicInt_lim z (fun n m hnm => by`. Establish `h1` using `sub_mem (hz n) (Lat_anti AI hnm (hz m))`. Rewrite `h1` using `[sub_sub_sub_cancel_right, ← map_sub]`. Conclude with `GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM _ h1)`.

Use `⟨y, GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI T M _ fun n => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hy n`. Establish `h2` using `io_mem_Lat AI M n (algebraMap ℤ_[l] (Ainf l) w)`. Rewrite `h2` using `[← map_natCast (algebraMap ℤ_[l] (Ainf l)), ← map_pow, ← map_mul, ← hw, io_zl AI T, PadicInt.coe_sub, map_sub]`. Use `add_mem h2 (hz n)` as an intermediate fact.

Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem nearZ_of_forall_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M : ℕ) (hM : 1 ≤ M) (v : P.R.BdR)
    (hv : ∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) : NearZ P M v := by
  choose z hz using hv
  obtain ⟨y, hy⟩ := exists_padicInt_lim z (fun n m hnm => by
    have h1 := sub_mem (hz n) (Lat_anti AI hnm (hz m))
    rw [sub_sub_sub_cancel_right, ← map_sub] at h1
    exact GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM _ h1)
  refine ⟨y, GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI T M _ fun n => ?_⟩
  obtain ⟨w, hw⟩ := hy n
  have h2 := io_mem_Lat AI M n (algebraMap ℤ_[l] (Ainf l) w)
  rw [← map_natCast (algebraMap ℤ_[l] (Ainf l)), ← map_pow, ← map_mul, ← hw, io_zl AI T,
    PadicInt.coe_sub, map_sub] at h2
  have := add_mem h2 (hz n)
  rwa [sub_add_sub_cancel] at this

end GlobalTheory.ExpImage
