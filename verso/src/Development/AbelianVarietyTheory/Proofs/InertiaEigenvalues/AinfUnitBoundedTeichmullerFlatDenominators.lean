import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneSurjectiveWittTilt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.BddDen

variable {l : ℕ} [hl : Fact l.Prime]

abbrev redMap {K : FinExt l} (bk : BK K) : bk.S →+* (OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) :=
  (Ideal.Quotient.mk _).comp ((Per.θ l).comp bk.ev)

/- English proof (translation)
Establish `h : (redMap bk).comp (Polynomial.coeToPowerSeries.ringHom) = Polynomial.eval₂RingHom ((redMap bk).comp PowerSeries.C) (redMap bk X)` using `Polynomial.ringHom_ext (fun a => by simp) (by simp)`. Conclude with `congrArg (fun f => f p) h`.
-/
theorem redMap_coe {K : FinExt l} (bk : BK K) (p : Polynomial (Wq l bk.a)) :
    redMap bk (p : bk.S) = p.eval₂ ((redMap bk).comp PowerSeries.C) (redMap bk X) := by
  have h : (redMap bk).comp (Polynomial.coeToPowerSeries.ringHom) =
      Polynomial.eval₂RingHom ((redMap bk).comp PowerSeries.C) (redMap bk X) :=
    Polynomial.ringHom_ext (fun a => by simp) (by simp)
  exact congrArg (fun f => f p) h

/- English proof (translation)
Rewrite using `[BK.E, redMap_coe, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree, map_one, one_mul, add_eq_right]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `bk.dvd_coeff i (Finset.mem_range.1 hi)`. Establish `hl0 : ((l : ℕ) : OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mem_span_singleton_self _`. Rewrite using `[RingHom.comp_apply, hc, map_mul, map_mul, map_natCast, map_natCast, hl0, zero_mul, zero_mul]`.
-/
theorem redMap_E {K : FinExt l} (bk : BK K) : redMap bk bk.E = redMap bk X ^ bk.Ep.natDegree := by
  rw [BK.E, redMap_coe, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree,
    map_one, one_mul, add_eq_right]
  refine Finset.sum_eq_zero fun i hi => ?_
  obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  have hl0 : ((l : ℕ) : OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.comp_apply, hc, map_mul, map_mul, map_natCast, map_natCast, hl0, zero_mul, zero_mul]

/- English proof (translation)
Introduce `hu`. Establish `h0 : redMap bk bk.E = 0`. Establish `hk : bk.ev bk.E ∈ RingHom.ker (Per.θ l)` using `bk.span_ev ▸ Ideal.mem_span_singleton_self _`. Rewrite `hk` using `[RingHom.mem_ker]`. Simplify using `only [redMap, RingHom.comp_apply, hk, map_zero]`.

Rewrite `h0` using `[redMap_E, redMap, RingHom.comp_apply, RingHom.comp_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Establish `hX : IsUnit (bk.ev X)` using `bk.ev_X ▸ hu.map (WittVector.teichmuller l)`. Conclude with `PI.ArtSch.OC_l_not_unit l (isUnit_of_dvd_unit h0 ((hX.map (Per.θ l)).pow _))`.
-/
theorem flat_not_isUnit {K : FinExt l} (bk : BK K) : ¬ IsUnit bk.flat := by
  intro hu
  have h0 : redMap bk bk.E = 0 := by
    have hk : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker] at hk
    simp only [redMap, RingHom.comp_apply, hk, map_zero]
  rw [redMap_E, redMap, RingHom.comp_apply, RingHom.comp_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at h0
  have hX : IsUnit (bk.ev X) := bk.ev_X ▸ hu.map (WittVector.teichmuller l)
  exact PI.ArtSch.OC_l_not_unit l (isUnit_of_dvd_unit h0 ((hX.map (Per.θ l)).pow _))

/- English proof (translation)
Introduce `l _ K bk a ha n`. Establish `ha0 : a.coeff 0 ≠ 0`. Introduce `h`. Establish `h1` using `ha.map (WittVector.constantCoeff (p := l) (R := Cb l))`. Rewrite `h1` using `[WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, h, map_zero]`.

Conclude with `not_isUnit_zero h1`. Establish `hv1 : PI.ArtSch.valb l bk.flat < 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `flat_not_isUnit bk (isUnit_of_dvd_one (GlobalTheory.ArtinSchreierTilt.tiltDiv l 1 bk.flat (by rw [map_one]; exact h)))`.

Establish `hv0 : 0 < PI.ArtSch.valb l (a.coeff 0)`. Rewrite using `[pos_iff_ne_zero]`. Conclude with `fun h => ha0 ((PreTilt.map_eq_zero (PadicComplexInt.integers l)).1 h)`. Take `⟨m₀, hm₀⟩` from `exists_pow_lt_of_lt_one hv0 hv1`. Take `⟨c, hc⟩` from `GlobalTheory.ArtinSchreierTilt.tiltDiv l (bk.flat ^ m₀) (a.coeff 0) (by rw [map_pow]; exact hm₀.le)`.

Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : (l : Ainf l) ∣ a - WittVector.teichmuller l (a.coeff 0) := by`. Rewrite using `[← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]`. Simplify using `[WittVector.constantCoeff_apply]`. Establish `hxy : WittVector.teichmuller l c * a = bk.ev X ^ m₀ + (l : Ainf l) * (WittVector.teichmuller l c * b)`. Establish `ha' : a = WittVector.teichmuller l (a.coeff 0) + (l : Ainf l) * b` using `by linear_combination hb`.

Establish `ht : WittVector.teichmuller l c * WittVector.teichmuller l (a.coeff 0) = bk.ev X ^ m₀`. Rewrite using `[bk.ev_X, ← map_pow, hc, map_mul, mul_comm]`. Rewrite using `[ha', mul_add, ht]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `geom_sum₂_mul (bk.ev X ^ m₀) (-((l : Ainf l) * (WittVector.teichmuller l c * b))) n`.

Use `⟨m₀ * n, WittVector.teichmuller l c * ∑ i ∈ Finset.range n, (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i), -((-(WittVector.teichmuller l c * b)) ^ n), ?_⟩` and prove the remaining obligations. Rewrite using `[pow_mul]`. Take the linear combination `(∑ i ∈ Finset.range n, (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i)) * hxy + h2`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), IsUnit (inclW l a) →
    ∀ n : ℕ, ∃ (m : ℕ) (t : Ainf l), (l : Ainf l) ^ n ∣ t * a - bk.ev X ^ m := by
  intro l _ K bk a ha n
  have ha0 : a.coeff 0 ≠ 0 := by
    intro h
    have h1 := ha.map (WittVector.constantCoeff (p := l) (R := Cb l))
    rw [WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, h, map_zero] at h1
    exact not_isUnit_zero h1
  have hv1 : PI.ArtSch.valb l bk.flat < 1 := by
    by_contra h
    push_neg at h
    exact flat_not_isUnit bk (isUnit_of_dvd_one
      (GlobalTheory.ArtinSchreierTilt.tiltDiv l 1 bk.flat (by rw [map_one]; exact h)))
  have hv0 : 0 < PI.ArtSch.valb l (a.coeff 0) := by
    rw [pos_iff_ne_zero]
    exact fun h => ha0 ((PreTilt.map_eq_zero (PadicComplexInt.integers l)).1 h)
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hv0 hv1
  obtain ⟨c, hc⟩ := GlobalTheory.ArtinSchreierTilt.tiltDiv l (bk.flat ^ m₀) (a.coeff 0) (by rw [map_pow]; exact hm₀.le)
  obtain ⟨b, hb⟩ : (l : Ainf l) ∣ a - WittVector.teichmuller l (a.coeff 0) := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply]
  have hxy : WittVector.teichmuller l c * a =
      bk.ev X ^ m₀ + (l : Ainf l) * (WittVector.teichmuller l c * b) := by
    have ha' : a = WittVector.teichmuller l (a.coeff 0) + (l : Ainf l) * b := by linear_combination hb
    have ht : WittVector.teichmuller l c * WittVector.teichmuller l (a.coeff 0) = bk.ev X ^ m₀ := by
      rw [bk.ev_X, ← map_pow, hc, map_mul, mul_comm]
    rw [ha', mul_add, ht]
    ring
  have h2 := geom_sum₂_mul (bk.ev X ^ m₀) (-((l : Ainf l) * (WittVector.teichmuller l c * b))) n
  refine ⟨m₀ * n, WittVector.teichmuller l c * ∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i),
    -((-(WittVector.teichmuller l c * b)) ^ n), ?_⟩
  rw [pow_mul]
  linear_combination (∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i)) * hxy + h2

end GlobalTheory.BSP.BddDen
