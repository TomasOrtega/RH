import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinfStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineXiPowSaturatedQuotientCompleteStatement

namespace GlobalTheory.ExpImage

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.MemLoc
open scoped Formalism.Per

/- English proof (translation)
Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]`. Use `H.haus _ fun n => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `h n`. Rewrite `hc` using `[← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hc, map_mul, map_pow, map_natCast]`.

Conclude with `dvd_mul_right _ _`.
-/
theorem dvd_of_isHausdorff {R : Type} [CommRing R] (p : ℕ) (x a : R)
    (H : IsHausdorff (Ideal.span {(p : R ⧸ Ideal.span {x})}) (R ⧸ Ideal.span {x}))
    (h : ∀ n : ℕ, ∃ c : R, x ∣ a - (p : R) ^ n * c) : x ∣ a := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  refine H.haus _ fun n => ?_
  obtain ⟨c, hc⟩ := h n
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hc
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    hc, map_mul, map_pow, map_natCast]
  exact dvd_mul_right _ _

/- English proof (translation)
Take `⟨-, h2, -⟩` from `GlobalTheory.T.deRham_fil_quotient_xi_power_ainf l P AI T (GlobalTheory.ThetaTie.thetaL T) M`. Take `⟨-, h3⟩` from `GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l AI.ε (GlobalTheory.ThetaTie.isEps AI) M`. Take `⟨a₀, ha₀⟩` from `hb 0`. Rewrite `ha₀` using `[pow_zero, one_mul]`. Establish `hd : AI.ξ ^ M ∣ a₀`.

Use `dvd_of_isHausdorff l _ _ h3.toIsHausdorff fun n => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hb n`. Use `⟨a, (h2 _).1 ?_⟩` and prove the remaining obligations. Use `sub_mem ha ha₀` as an intermediate fact. Rewrite using `[← io_apply, map_sub]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Use `add_mem ha₀ ((h2 a₀).2 hd)` as an intermediate fact. Rewrite `this` using `[← io_apply, sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem mem_FilB_of_forall_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M : ℕ) (b : P.R.BdR) (hb : ∀ n : ℕ, b ∈ Lat AI M n) :
    b ∈ FilB P (M : ℤ) := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.deRham_fil_quotient_xi_power_ainf l P AI T (GlobalTheory.ThetaTie.thetaL T) M
  obtain ⟨-, h3⟩ := GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l AI.ε (GlobalTheory.ThetaTie.isEps AI) M
  obtain ⟨a₀, ha₀⟩ := hb 0
  rw [pow_zero, one_mul] at ha₀
  have hd : AI.ξ ^ M ∣ a₀ := by
    refine dvd_of_isHausdorff l _ _ h3.toIsHausdorff fun n => ?_
    obtain ⟨a, ha⟩ := hb n
    refine ⟨a, (h2 _).1 ?_⟩
    have := sub_mem ha ha₀
    rw [← io_apply, map_sub]
    convert this using 1
    ring
  have := add_mem ha₀ ((h2 a₀).2 hd)
  rwa [← io_apply, sub_add_cancel] at this

end GlobalTheory.ExpImage
