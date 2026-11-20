import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DivIntoDual
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.LocInt

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`. Conclude with `hs w.asIdeal.zero_mem`. Establish `hJ : (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0`. Rewrite using `[ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis.

Unfold `vw`. Rewrite using `[← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ]`. Establish `hm : Associates.mk (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0` using `by rwa [ne_eq, Associates.mk_eq_zero]`. Assume the negation of the conclusion as `h`. Establish `h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal (𝓞 K))).factors`.

Apply `Nat.one_le_iff_ne_zero.2` to reduce the goal to its premises. Introduce `h0`. Conclude with `h (by rw [h0]; rfl)`. Rewrite `h1` using `[← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one, Associates.mk_le_mk_iff_dvd, Ideal.dvd_span_singleton]`. Conclude with `hs h1`.
-/
theorem vw_eq_zero_of_notMem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  classical
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs w.asIdeal.zero_mem
  have hJ : (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w hJ]
  have hm : Associates.mk (Ideal.span {s} : Ideal (𝓞 K)) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  by_contra h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {s} : Ideal (𝓞 K))).factors := by
    apply Nat.one_le_iff_ne_zero.2
    intro h0
    exact h (by rw [h0]; rfl)
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_span_singleton] at h1
  exact hs h1

/- English proof (translation)
Use `(Submodule.span_le.2 ?_ : nabStd K lam ≤ _) hF` and prove the remaining obligations. Introduce and unpack `P ⟨G, hG, rfl⟩`. Use `choose Q _ hQ using fun τ => Submodule.mem_map.1 (hG τ)`. Use `⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb (𝓞 K) τ (Q τ), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `MvPolynomial.map (algebraMap (𝓞 K) K) _ = _`.

Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← hQ τ]`. Simplify using `only [Formalism.GradedWeylDivisibility.blockEmb]`. Conclude with `map_rename _ _ _`.
-/
theorem exists_map_eq_of_mem_nabStd {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {F : Pol K ι n}
    (hF : F ∈ nabStd K lam) : F ∈ LinearMap.range (toK K (ι × Fin n × Fin n)) := by
  refine (Submodule.span_le.2 ?_ : nabStd K lam ≤ _) hF
  rintro P ⟨G, hG, rfl⟩
  choose Q _ hQ using fun τ => Submodule.mem_map.1 (hG τ)
  refine ⟨∏ τ, Formalism.GradedWeylDivisibility.blockEmb (𝓞 K) τ (Q τ), ?_⟩
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← hQ τ]
  simp only [Formalism.GradedWeylDivisibility.blockEmb]
  exact map_rename _ _ _

/- English proof (translation)
Introduce `K _ _ _`. Use `⟨fun a h => ?_, fun ι _ n lam w F hF mo => ?_⟩` and prove the remaining obligations. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Conclude with `zero_mem _`.

Conclude with `DualLatticeDivisor.mem_range_of_vw_nonneg a ha h`. Take `⟨s, hs, hsF⟩` from `hF`. Take `⟨Q, hQ⟩` from `exists_map_eq_of_mem_nabStd lam hsF`. Distinguish the cases in `hc : coeff mo F = 0`. Rewrite using `[hc, ValuationRepresentative.vw_zero]`.

Establish `hs' : s ∉ w.asIdeal` using `hs`. Establish `hs0 : (s : K) ≠ 0`. Introduce `h0`. Establish `: s = 0` using `RingOfIntegers.ext h0`. Conclude with `hs' (this ▸ w.asIdeal.zero_mem)`.

Establish `hco : (s : K) * coeff mo F = ((coeff mo Q : 𝓞 K) : K)`. Establish `h1` using `congrArg (coeff mo) hQ`. Rewrite `h1` using `[coeff_smul]`. Establish `h2 : coeff mo (toK K _ Q) = ((coeff mo Q : 𝓞 K) : K)` using `coeff_map _ _ _`. Rewrite using `[← h2, h1, Algebra.smul_def]`.

Establish `h3` using `ValuationRepresentative.vw_int_nonneg w (coeff mo Q)`. Rewrite `h3` using `[← hco, ValuationRepresentative.vw_mul w _ _ hs0 hc, vw_eq_zero_of_notMem w hs', zero_add]`. Then use the resulting hypothesis.
-/
theorem localIntegrality : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], (∀ a : K, (∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vw w a) → a ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (w : HeightOneSpectrum (𝓞 K)) (F : Pol K ι n), F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → ∀ mo, 0 ≤ vw w (coeff mo F) := by
  intro K _ _ _
  refine ⟨fun a h => ?_, fun ι _ n lam w F hF mo => ?_⟩
  · by_cases ha : a = 0
    · subst ha
      exact zero_mem _
    · exact DualLatticeDivisor.mem_range_of_vw_nonneg a ha h
  · obtain ⟨s, hs, hsF⟩ := hF
    obtain ⟨Q, hQ⟩ := exists_map_eq_of_mem_nabStd lam hsF
    by_cases hc : coeff mo F = 0
    · rw [hc, ValuationRepresentative.vw_zero]
    have hs' : s ∉ w.asIdeal := hs
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      have : s = 0 := RingOfIntegers.ext h0
      exact hs' (this ▸ w.asIdeal.zero_mem)
    have hco : (s : K) * coeff mo F = ((coeff mo Q : 𝓞 K) : K) := by
      have h1 := congrArg (coeff mo) hQ
      rw [coeff_smul] at h1
      have h2 : coeff mo (toK K _ Q) = ((coeff mo Q : 𝓞 K) : K) := coeff_map _ _ _
      rw [← h2, h1, Algebra.smul_def]
    have h3 := ValuationRepresentative.vw_int_nonneg w (coeff mo Q)
    rwa [← hco, ValuationRepresentative.vw_mul w _ _ hs0 hc, vw_eq_zero_of_notMem w hs', zero_add] at h3

end GlobalTheory.LocInt
