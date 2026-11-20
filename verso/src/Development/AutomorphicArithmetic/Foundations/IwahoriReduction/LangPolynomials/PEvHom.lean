import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitBallSubring
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

/- English proof (translation)
Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_of_le_one_left (by positivity) (hf _)`.
-/
private theorem term_le {R K : Type} [CommRing R] [NormedField K] (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1) (t : K)
    (h : PowerSeries R) (i : ℕ) : ‖f (h.coeff i) * t ^ i‖ ≤ ‖t‖ ^ i := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) (hf _)

/- English proof (translation)
The claim follows from `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_le f hf t h) (summable_geometric_of_lt_one (norm_nonneg _) ht)`.
-/
private theorem summ {R K : Type} [CommRing R] [NormedField K] (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1) (t : K) (ht : ‖t‖ < 1)
    (h : PowerSeries R) : Summable fun i => ‖f (h.coeff i) * t ^ i‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (term_le f hf t h)
    (summable_geometric_of_lt_one (norm_nonneg _) ht)

/- English proof (translation)
Use `⟨{ toFun := fun h => ∑' i, f (h.coeff i) * t ^ i map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun _ => rfl⟩` and prove the remaining obligations. Rewrite using `[tsum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `b hb`. Simplify using `[PowerSeries.coeff_one, hb]`.

Introduce `a b`. Rewrite using `[tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summ f hf t ht a) (summ f hf t ht b)]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_mul, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_mul, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Introduce `a b`. Rewrite using `[← Summable.tsum_add (summ f hf t ht a).of_norm (summ f hf t ht b).of_norm]`.

Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[map_add, map_add, add_mul]`.
-/
private theorem exE {R K : Type} [CommRing R] [NormedField K] [CompleteSpace K] (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1)
    (t : K) (ht : ‖t‖ < 1) : ∃ E : PowerSeries R →+* K, ∀ h, E h = ∑' i, f (h.coeff i) * t ^ i := by
  refine ⟨{ toFun := fun h => ∑' i, f (h.coeff i) * t ^ i
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun _ => rfl⟩
  · rw [tsum_eq_single 0]
    · simp
    · intro b hb; simp [PowerSeries.coeff_one, hb]
  · intro a b
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summ f hf t ht a) (summ f hf t ht b)]
    refine tsum_congr fun n => ?_
    rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_mul, pow_add]; ring
  · simp
  · intro a b
    rw [← Summable.tsum_add (summ f hf t ht a).of_norm (summ f hf t ht b).of_norm]
    refine tsum_congr fun n => ?_
    rw [map_add, map_add, add_mul]

/- English proof (translation)
Rewrite using `[← (summ f hf t ht h).of_norm.sum_add_tsum_nat_add N, add_sub_cancel_left]`. Use `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_` and prove the remaining obligations. Conclude with `(term_le f hf t h _).trans (pow_le_pow_of_le_one (norm_nonneg _) ht.le (by omega))`.
-/
private theorem tail {R K : Type} [CommRing R] [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (f : R →+* K) (hf : ∀ x, ‖f x‖ ≤ 1) (t : K) (ht : ‖t‖ < 1) (h : PowerSeries R) (N : ℕ) :
    ‖(∑' i, f (h.coeff i) * t ^ i) - ∑ i ∈ Finset.range N, f (h.coeff i) * t ^ i‖ ≤ ‖t‖ ^ N := by
  rw [← (summ f hf t ht h).of_norm.sum_add_tsum_nat_add N, add_sub_cancel_left]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun i => ?_
  exact (term_le f hf t h _).trans (pow_le_pow_of_le_one (norm_nonneg _) ht.le (by omega))

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh18.rootb l m hl h2 z hz`.
-/
private theorem rootb {K : Type} [NormedField K] [IsUltrametricDist K] (l m : ℕ) (hl : l.Prime) (h2 : l ≠ 2)
    (z : K) (hz : z ^ l ^ m = 1) : ‖z - 1‖ ^ l ^ m ≤ ‖(l : K)‖ :=
  _root_.UpperTheory.Reformulated.B.Qh18.rootb l m hl h2 z hz

/- English proof (translation)
Introduce `l hl h2 Ω _ _ _ A _ j Φ m hm z hz`. Establish `hb` using `rootb l m hl.out h2 z hz.pow_eq_one`. Establish `hl1 : ‖(l : ℂ_[l])‖ < 1`. Establish `: (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap']`.

Conclude with `Padic.norm_p_lt_one`. Establish `ht : ‖z - 1‖ < 1`. Assume the negation of the conclusion as `hc`. Conclude with `absurd (hb.trans_lt hl1) (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))`. Take `⟨E, hE⟩` from `exE Φ.jh Φ.jh_le (z - 1) ht`.

Establish `hC : ∀ x, E (PowerSeries.C x) = Φ.jh x`. Introduce `x`. Rewrite using `[hE, tsum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `b hb`.

Simplify using `[PowerSeries.coeff_C, hb]`. Establish `hX : E (1 + PowerSeries.X) = z`. Rewrite using `[map_add, map_one, hE, tsum_eq_single 1]`. Simplify using the standard rewrite rules. Introduce `b hb`.

Simplify using `[PowerSeries.coeff_X, hb]`. Establish `hcyc : E (GlobalTheory.Col.cyc Φ.R l m) = 0`. Establish `: E.comp PowerSeries.C = Φ.jh` using `RingHom.ext hC`. Rewrite using `[GlobalTheory.Col.cyc, Polynomial.hom_eval₂, this, hX, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `hz.isRoot_cyclotomic (pow_pos hl.out.pos m)`.

Use `⟨Ideal.Quotient.lift _ E (fun a ha => ?_), fun y => ?_, hC, hX, fun h => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Rewrite using `[map_mul, hcyc, mul_zero]`. Take `⟨h, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Use `tail Φ.jh Φ.jh_le (z - 1) ht h 0` as an intermediate fact.

Rewrite using `[Ideal.Quotient.lift_mk, hE]`. Simplify using `using this`. Rewrite using `[Ideal.Quotient.lift_mk, hE]`. Use `(tail Φ.jh Φ.jh_le (z - 1) ht h _).trans ?_` and prove the remaining obligations. Establish `hle : l ^ m * m ≤ l ^ (3 * m)`.

Rewrite using `[show 3 * m = m + 2 * m by ring, pow_add]`. Conclude with `Nat.mul_le_mul_left _ (le_trans (by omega) (Nat.lt_pow_self hl.out.one_lt).le)`. Use `(pow_le_pow_of_le_one (norm_nonneg _) ht.le hle).trans ?_` and prove the remaining obligations. Rewrite using `[pow_mul, norm_pow]`. Conclude with `pow_le_pow_left₀ (by positivity) hb m`.
-/
theorem UpperTheory.Kd.C7.pEvHom :
    UpperTheory.Kd.C7.SEvHom := by
  intro l hl h2 Ω _ _ _ A _ j Φ m hm z hz
  have hb := rootb l m hl.out h2 z hz.pow_eq_one
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have : (l : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have ht : ‖z - 1‖ < 1 := by
    by_contra hc
    exact absurd (hb.trans_lt hl1) (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))
  obtain ⟨E, hE⟩ := exE Φ.jh Φ.jh_le (z - 1) ht
  have hC : ∀ x, E (PowerSeries.C x) = Φ.jh x := by
    intro x
    rw [hE, tsum_eq_single 0]
    · simp
    · intro b hb; simp [PowerSeries.coeff_C, hb]
  have hX : E (1 + PowerSeries.X) = z := by
    rw [map_add, map_one, hE, tsum_eq_single 1]
    · simp
    · intro b hb; simp [PowerSeries.coeff_X, hb]
  have hcyc : E (GlobalTheory.Col.cyc Φ.R l m) = 0 := by
    have : E.comp PowerSeries.C = Φ.jh := RingHom.ext hC
    rw [GlobalTheory.Col.cyc, Polynomial.hom_eval₂, this, hX, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hz.isRoot_cyclotomic (pow_pos hl.out.pos m)
  refine ⟨Ideal.Quotient.lift _ E (fun a ha => ?_), fun y => ?_, hC, hX, fun h => ?_⟩
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hcyc, mul_zero]
  · obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := tail Φ.jh Φ.jh_le (z - 1) ht h 0
    rw [Ideal.Quotient.lift_mk, hE]
    simpa using this
  · rw [Ideal.Quotient.lift_mk, hE]
    refine (tail Φ.jh Φ.jh_le (z - 1) ht h _).trans ?_
    have hle : l ^ m * m ≤ l ^ (3 * m) := by
      rw [show 3 * m = m + 2 * m by ring, pow_add]
      exact Nat.mul_le_mul_left _ (le_trans (by omega) (Nat.lt_pow_self hl.out.one_lt).le)
    refine (pow_le_pow_of_le_one (norm_nonneg _) ht.le hle).trans ?_
    rw [pow_mul, norm_pow]
    exact pow_le_pow_left₀ (by positivity) hb m
