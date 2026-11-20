import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorLength
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartDivisorComponents
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSectionLength
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSectionLengthSum
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLocalSectionLengthSum
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPiQuotCokerFiniteLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn divSupp IsHorizontal multAt mcPts)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartIdeal segreChartComponents localMult mem_segreChartComponents)

variable {K : Type*} [Fintype K] {ι : K → Type*}

/- English proof (translation)
Introduce and unpack `f ⟨e, he⟩`. Rewrite `he`, the goal using `[segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]`. Introduce `x hx`. Establish `h` using `he x hx`. Rewrite `h` using `[map_pow]`.

Conclude with `eq_zero_of_pow_eq_zero h`.
-/
theorem segreChartIdeal_isRadical (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    (segreChartIdeal P σ i).IsRadical := by
  rintro f ⟨e, he⟩
  rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff] at he ⊢
  intro x hx
  have h := he x hx
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

/- English proof (translation)
Apply `MvPolynomial.vanishingIdeal_anti_mono` to reduce the goal to its premises. Introduce and unpack `x ⟨z, ⟨hz0, hz⟩, hzi, rfl⟩`. Conclude with `⟨z, ⟨hz0, fun f hf => hz f (h hf)⟩, hzi, rfl⟩`.
-/
theorem segreChartIdeal_mono {P W : Ideal (MRing ι)} (h : P ≤ W) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : segreChartIdeal P σ i ≤ segreChartIdeal W σ i := by
  apply MvPolynomial.vanishingIdeal_anti_mono
  rintro x ⟨z, ⟨hz0, hz⟩, hzi, rfl⟩
  exact ⟨z, ⟨hz0, fun f hf => hz f (h hf)⟩, hzi, rfl⟩

/- English proof (translation)
Introduce `K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW'`. Establish `hcomp` using `(hComp K ι P n m σ i A s hP hs).1`. Establish `hnot` using `hNotMem K ι P (n + 1) m σ i A s hP hs`. Establish `hW'min : W' ∈ (segreChartIdeal W σ i).minimalPrimes` using `mem_segreChartComponents.1 hW'`. Establish `hW'p : W'.IsPrime` using `hW'min.1.1`.

Establish `hIW' : segreChartIdeal P σ i ≤ W'` using `(segreChartIdeal_mono (le_sup_left.trans hW.1.1.2) σ i).trans hW'min.1.2`. Establish `hJW : ∀ J ∈ (segreChartIdeal P σ i).minimalPrimes, J ≤ W' → W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes` using `fun J hJ hJW' => (hcomp J (mem_segreChartComponents.2 hJ) W').2 ⟨hJW', W, ⟨hW, hWh⟩, hW'⟩`. Establish `hmin : W' ∈ (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}).minimalPrimes`. Use `⟨⟨hW'p, sup_le hIW' ?_⟩, fun Q hQ hQW' => ?_⟩` and prove the remaining obligations. Take `⟨J, hJ, hJW'⟩` from `Ideal.exists_minimalPrimes_le hIW'`.

Conclude with `le_sup_right.trans (hJW J hJ hJW').1.2`. Use `hQ.1` as an intermediate fact. Take `⟨J, hJ, hJQ⟩` from `Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.2)`. Conclude with `(hJW J hJ (hJQ.trans hQW')).2 ⟨hQ.1, sup_le hJQ (le_sup_right.trans hQ.2)⟩ hQW'`. Establish `key` using `GroundTheory.Heights₂.Heights.SectionLengthSum.proof (GroundTheory.Heights₂.Heights.LocalSectionLengthSum.proof GroundTheory.Heights₂.Heights.PiQuotCokerFiniteLength.proof) (MvPolynomial (Fin m) ℂ) (segreChartIdeal P σ i) W' (chartSection σ i s) (segreChartIdeal_isRadical P σ i) …`.

Rewrite using `[← hLen K ι P n m σ i A s hP hs W hW hWh W' hW', key]`. Both sides reduce to the same expression.
-/
theorem ChartDivisorLength.proof (hNotMem : ChartSectionNotMem.Statement) (hComp : ChartDivisorComponents.Statement)
    (hLen : ChartSectionLength.Statement) : ChartDivisorLength.Statement := by
  intro K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW'
  have hcomp := (hComp K ι P n m σ i A s hP hs).1
  have hnot := hNotMem K ι P (n + 1) m σ i A s hP hs
  have hW'min : W' ∈ (segreChartIdeal W σ i).minimalPrimes := mem_segreChartComponents.1 hW'
  have hW'p : W'.IsPrime := hW'min.1.1
  have hIW' : segreChartIdeal P σ i ≤ W' :=
    (segreChartIdeal_mono (le_sup_left.trans hW.1.1.2) σ i).trans hW'min.1.2
  have hJW : ∀ J ∈ (segreChartIdeal P σ i).minimalPrimes, J ≤ W' →
      W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes := fun J hJ hJW' =>
    (hcomp J (mem_segreChartComponents.2 hJ) W').2 ⟨hJW', W, ⟨hW, hWh⟩, hW'⟩
  have hmin : W' ∈ (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}).minimalPrimes := by
    refine ⟨⟨hW'p, sup_le hIW' ?_⟩, fun Q hQ hQW' => ?_⟩
    · obtain ⟨J, hJ, hJW'⟩ := Ideal.exists_minimalPrimes_le hIW'
      exact le_sup_right.trans (hJW J hJ hJW').1.2
    · have := hQ.1
      obtain ⟨J, hJ, hJQ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.2)
      exact (hJW J hJ (hJQ.trans hQW')).2 ⟨hQ.1, sup_le hJQ (le_sup_right.trans hQ.2)⟩ hQW'
  have key := GroundTheory.Heights₂.Heights.SectionLengthSum.proof
    (GroundTheory.Heights₂.Heights.LocalSectionLengthSum.proof GroundTheory.Heights₂.Heights.PiQuotCokerFiniteLength.proof)
    (MvPolynomial (Fin m) ℂ) (segreChartIdeal P σ i) W' (chartSection σ i s) (segreChartIdeal_isRadical P σ i)
    (fun J hJ => hnot J (mem_segreChartComponents.2 hJ)) hmin hJW
  rw [← hLen K ι P n m σ i A s hP hs W hW hWh W' hW', key]
  rfl

end GroundTheory.Heights₂.Heights.Targets
