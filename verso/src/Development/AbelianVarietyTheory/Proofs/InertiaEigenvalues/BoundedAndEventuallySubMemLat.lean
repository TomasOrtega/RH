import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitOfEventually

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

/- English proof (translation)
Take `⟨p, q, rfl⟩` from `Ideal.mem_span_pair.1 hx`. Rewrite using `[map_add, mul_comm p]`. Use `add_mem (io_mem_Lat AI M n p) (FilB_le_Lat AI ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Conclude with `FilB_zero_mul (io_mem AI q) (by simpa using FilB_pow (io_ξ_mem AI) M)`.
-/
theorem io_mem_Lat_of_mem_span {M n : ℕ} {x : Ainf l}
    (hx : x ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M}) : io AI x ∈ Lat AI M n := by
  obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.1 hx
  rw [map_add, mul_comm p]
  refine add_mem (io_mem_Lat AI M n p) (FilB_le_Lat AI ?_)
  rw [map_mul, map_pow]
  exact FilB_zero_mul (io_mem AI q) (by simpa using FilB_pow (io_ξ_mem AI) M)

/- English proof (translation)
Introduce `l _ P AI T b hb M n`. Take `⟨k, a, ha⟩` from `GlobalTheory.BdRQuot.exists_approx T M b hb`. Express the relevant statement in the definitionally equal form `(l : P.R.BdR) ^ k * b - io AI a ∈ FilB P (M : ℤ) at ha`. Prove the components needed by the constructor for the conclusion. Establish `h0 : (l : P.R.BdR) ^ k * b ∈ Lat AI M 0` using `⟨a, by simpa using ha⟩`.

Use `⟨n + k, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, mul_assoc]`. Conclude with `(pow_mul_mem_Lat_iff AI (k := n) (n := 0)).2 h0`. Use `filter_upwards [GlobalTheory.AinfCont.eventually_sub_mem AI (k + n) M a] with g hg`. Rewrite using `[← pow_mul_mem_Lat_iff AI (k := k)]`.

Establish `h1` using `io_mem_Lat_of_mem_span AI hg`. Establish `h2` using `FilB_le_Lat AI (n := k + n) (sub_mem (act_mem g ha) ha)`. Establish `h3` using `add_mem h1 h2`. Rewrite `h3` using `[map_sub, io_act, map_sub, map_mul, map_pow, map_natCast]`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bounded_and_eventually_sub_mem_Lat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (AI : LocAinf l P), LocTied l P AI → ∀ b ∈ FilB P 0, ∀ M n : ℕ,
    (∃ k : ℕ, (l : P.R.BdR) ^ k * b ∈ Lat AI M n) ∧
      ∀ᶠ σ in nhds (1 : GQ l), P.actQdR σ b - b ∈ Lat AI M n := by
  intro l _ P AI T b hb M n
  obtain ⟨k, a, ha⟩ := GlobalTheory.BdRQuot.exists_approx T M b hb
  change (l : P.R.BdR) ^ k * b - io AI a ∈ FilB P (M : ℤ) at ha
  constructor
  · have h0 : (l : P.R.BdR) ^ k * b ∈ Lat AI M 0 := ⟨a, by simpa using ha⟩
    refine ⟨n + k, ?_⟩
    rw [pow_add, mul_assoc]
    exact (pow_mul_mem_Lat_iff AI (k := n) (n := 0)).2 h0
  · filter_upwards [GlobalTheory.AinfCont.eventually_sub_mem AI (k + n) M a] with g hg
    rw [← pow_mul_mem_Lat_iff AI (k := k)]
    have h1 := io_mem_Lat_of_mem_span AI hg
    have h2 := FilB_le_Lat AI (n := k + n) (sub_mem (act_mem g ha) ha)
    have h3 := add_mem h1 h2
    rw [map_sub, io_act, map_sub, map_mul, map_pow, map_natCast] at h3
    convert h3 using 1
    ring

end GlobalTheory.ExpImage
