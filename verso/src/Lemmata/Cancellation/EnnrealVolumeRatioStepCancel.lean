import Mathlib

universe u_1 u_2

namespace Bl.VolumeRatioCancellation

/- English proof (translation)
Establish `h'` using `mul_le_mul_left h z⁻¹`. Simplify `h'` using `[mul_assoc, mul_inv_cancel₀ hz]`.
-/
private lemma ennreal_volume_ratio_step_cancel {u w z : WithZero (Multiplicative ℤ)} (hz : z ≠ 0)
    (h : u * z ≤ w * z) : u ≤ w := by
  have h' := mul_le_mul_left h z⁻¹
  simpa [mul_assoc, mul_inv_cancel₀ hz] using h'

/- English proof (translation)
Introduce `R _ _ K _ _ _ T a c hc`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors R) T a`. Establish `hd0 : (b : R) ≠ 0` using `nonZeroDivisors.coe_ne_zero b`. Establish `hdK : algebraMap R K (b : R) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd0`. Establish `hb' : ∀ i ∈ T, ∃ r : R, algebraMap R K r = algebraMap R K (b : R) * a i`.

Introduce `i hi`. Take `⟨r, hr⟩` from `hb i hi`. Conclude with `⟨r, by rw [hr, Algebra.smul_def]⟩`. Use `choose! x hx using hb'`. Establish `hspan : Ideal.span {(b : R)} ≠ 0`.

Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Use `set S := (Ideal.finite_factors hspan).toFinset with hS`. Set `N : IsDedekindDomain.HeightOneSpectrum R → ℕ` to `fun p => (WithZero.log (p.valuation K (c p) * p.intValuation (b : R))).natAbs`. Set `m : IsDedekindDomain.HeightOneSpectrum R → ℕ` to `fun q => multiplicity q.asIdeal (Ideal.span {(b : R)})`. Set `e : IsDedekindDomain.HeightOneSpectrum R → ℕ` to `fun q => if q ∈ T then N q else m q`.

Set `xx : (T ∪ S : Finset _) → R` to `fun i => if i.1 ∈ T then x i.1 else 0`. Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := T ∪ S) (fun q => q.asIdeal) e (fun q _ => q.prime) (fun q _ q' _ hne h => hne (IsDedekindDomain.HeightOneSpectrum.ext h)) xx`. Use `⟨algebraMap R K y / algebraMap R K (b : R), ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Establish `h1` using `hy p (Finset.mem_union_left _ hp)`.

Simplify using `only [xx, e, hp, if_true] at h1`. Establish `h2` using `(p.intValuation_le_pow_iff_mem _ _).mpr h1`. Establish `hcv : p.valuation K (c p) ≠ 0` using `by simpa using hc p hp`. Establish `hγ : p.valuation K (c p) * p.intValuation (b : R) ≠ 0` using `mul_ne_zero hcv (p.intValuation_ne_zero _ hd0)`. Establish `h3 : WithZero.exp (-((N p : ℕ) : ℤ)) ≤ p.valuation K (c p) * p.intValuation (b : R)` using `by conv_rhs => rw [← WithZero.exp_log hγ]`.

Rewrite using `[WithZero.exp_le_exp]`. Simplify using `only [N]`. Use linear arithmetic over natural numbers and integers. Establish `key : (algebraMap R K y / algebraMap R K (b : R) - a p) * algebraMap R K (b : R) = algebraMap R K (y - x p)`. Rewrite using `[map_sub, hx p hp, sub_mul, div_mul_cancel₀ _ hdK]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : p.valuation K (algebraMap R K y / algebraMap R K (b : R) - a p) * p.intValuation (b : R) ≤ p.valuation K (c p) * p.intValuation (b : R)`. Establish `vb : p.valuation K (algebraMap R K (b : R)) = p.intValuation (b : R)`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Establish `e1 : p.valuation K (algebraMap R K y / algebraMap R K (b : R) - a p) * p.intValuation (b : R) = p.intValuation (y - x p)`.

Rewrite using `[← vb, ← map_mul, key, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Rewrite using `[e1]`. Conclude with `h2.trans h3`. Conclude with `ennreal_volume_ratio_step_cancel (p.intValuation_ne_zero _ hd0) h4`. Introduce `q hq`.

Establish `key : (algebraMap R K y / algebraMap R K (b : R)) * algebraMap R K (b : R) = algebraMap R K y` using `div_mul_cancel₀ _ hdK`. Establish `h5 : q.intValuation y ≤ q.intValuation (b : R)`. Distinguish the cases in `hqS : q ∈ S`. Establish `h1` using `hy q (Finset.mem_union_right _ hqS)`. Simplify using `only [xx, e, hq, if_false, sub_zero] at h1`.

Rewrite using `[q.intValuation_eq_exp_neg_multiplicity hd0]`. Conclude with `(q.intValuation_le_pow_iff_mem _ _).mpr h1`. Establish `hnd : ¬ q.asIdeal ∣ Ideal.span {(b : R)}`. Simplify `hqS` using `[hS]`. Establish `hone : q.intValuation (b : R) = 1`.

Use `le_antisymm (q.intValuation_le_one _) (not_lt.mp ?_)` and prove the remaining obligations. Rewrite using `[q.intValuation_lt_one_iff_dvd]`. Conclude with `hnd`. Rewrite using `[hone]`. Conclude with `q.intValuation_le_one _`.

Establish `h4 : q.valuation K (algebraMap R K y / algebraMap R K (b : R)) * q.intValuation (b : R) ≤ 1 * q.intValuation (b : R)`. Establish `vb : q.valuation K (algebraMap R K (b : R)) = q.intValuation (b : R)`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Establish `e1 : q.valuation K (algebraMap R K y / algebraMap R K (b : R)) * q.intValuation (b : R) = q.intValuation y`. Rewrite using `[← vb, ← map_mul, key, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`.

Rewrite using `[e1, one_mul]`. Conclude with `h5`. Conclude with `ennreal_volume_ratio_step_cancel (q.intValuation_ne_zero _ hd0) h4`.
-/
theorem goal1 :
  ∀ {R : Type u_1} [inst : CommRing.{u_1} R] [inst_1 : IsDedekindDomain.{u_1} R] {K : Type u_2} [inst_2 : Field.{u_2} K]
  [inst_3 : Algebra.{u_1, u_2} R K] [inst_4 : IsFractionRing.{u_1, u_2} R K]
  (T : Finset.{u_1} (IsDedekindDomain.HeightOneSpectrum.{u_1} R))
  (a c : IsDedekindDomain.HeightOneSpectrum.{u_1} R → K),
  (∀ (p : IsDedekindDomain.HeightOneSpectrum.{u_1} R), Membership.mem.{u_1, u_1} T p → Ne.{u_2 + 1} (c p) 0) →
    Exists.{u_2 + 1} fun (t : K) ↦
      And
        (∀ (p : IsDedekindDomain.HeightOneSpectrum.{u_1} R),
          Membership.mem.{u_1, u_1} T p →
            LE.le.{0}
              (DFunLike.coe.{u_2 + 1, u_2 + 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{u_1, u_2} K p)
                (HSub.hSub.{u_2, u_2, u_2} t (a p)))
              (DFunLike.coe.{u_2 + 1, u_2 + 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{u_1, u_2} K p) (c p)))
        (∀ (p : IsDedekindDomain.HeightOneSpectrum.{u_1} R),
          Not (Membership.mem.{u_1, u_1} T p) →
            LE.le.{0}
              (DFunLike.coe.{u_2 + 1, u_2 + 1, 1} (IsDedekindDomain.HeightOneSpectrum.valuation.{u_1, u_2} K p) t) 1) := by
  intro R _ _ K _ _ _ T a c hc
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) T a
  have hd0 : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hdK : algebraMap R K (b : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd0
  have hb' : ∀ i ∈ T, ∃ r : R, algebraMap R K r = algebraMap R K (b : R) * a i := by
    intro i hi
    obtain ⟨r, hr⟩ := hb i hi
    exact ⟨r, by rw [hr, Algebra.smul_def]⟩
  choose! x hx using hb'
  have hspan : Ideal.span {(b : R)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  set S := (Ideal.finite_factors hspan).toFinset with hS
  let N : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun p =>
    (WithZero.log (p.valuation K (c p) * p.intValuation (b : R))).natAbs
  let m : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun q =>
    multiplicity q.asIdeal (Ideal.span {(b : R)})
  let e : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun q => if q ∈ T then N q else m q
  let xx : (T ∪ S : Finset _) → R := fun i => if i.1 ∈ T then x i.1 else 0
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T ∪ S)
    (fun q => q.asIdeal) e (fun q _ => q.prime)
    (fun q _ q' _ hne h => hne (IsDedekindDomain.HeightOneSpectrum.ext h)) xx
  refine ⟨algebraMap R K y / algebraMap R K (b : R), ?_, ?_⟩
  · intro p hp
    have h1 := hy p (Finset.mem_union_left _ hp)
    simp only [xx, e, hp, if_true] at h1
    have h2 := (p.intValuation_le_pow_iff_mem _ _).mpr h1
    have hcv : p.valuation K (c p) ≠ 0 := by simpa using hc p hp
    have hγ : p.valuation K (c p) * p.intValuation (b : R) ≠ 0 :=
      mul_ne_zero hcv (p.intValuation_ne_zero _ hd0)
    have h3 : WithZero.exp (-((N p : ℕ) : ℤ)) ≤ p.valuation K (c p) * p.intValuation (b : R) := by
      conv_rhs => rw [← WithZero.exp_log hγ]
      rw [WithZero.exp_le_exp]
      simp only [N]
      omega
    have key : (algebraMap R K y / algebraMap R K (b : R) - a p) * algebraMap R K (b : R)
        = algebraMap R K (y - x p) := by
      rw [map_sub, hx p hp, sub_mul, div_mul_cancel₀ _ hdK]; ring
    have h4 : p.valuation K (algebraMap R K y / algebraMap R K (b : R) - a p) * p.intValuation (b : R)
        ≤ p.valuation K (c p) * p.intValuation (b : R) := by
      have vb : p.valuation K (algebraMap R K (b : R)) = p.intValuation (b : R) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      have e1 : p.valuation K (algebraMap R K y / algebraMap R K (b : R) - a p) * p.intValuation (b : R)
          = p.intValuation (y - x p) := by
        rw [← vb, ← map_mul, key, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      rw [e1]
      exact h2.trans h3
    exact ennreal_volume_ratio_step_cancel (p.intValuation_ne_zero _ hd0) h4
  · intro q hq
    have key : (algebraMap R K y / algebraMap R K (b : R)) * algebraMap R K (b : R)
        = algebraMap R K y := div_mul_cancel₀ _ hdK
    have h5 : q.intValuation y ≤ q.intValuation (b : R) := by
      by_cases hqS : q ∈ S
      · have h1 := hy q (Finset.mem_union_right _ hqS)
        simp only [xx, e, hq, if_false, sub_zero] at h1
        rw [q.intValuation_eq_exp_neg_multiplicity hd0]
        exact (q.intValuation_le_pow_iff_mem _ _).mpr h1
      · have hnd : ¬ q.asIdeal ∣ Ideal.span {(b : R)} := by
          simpa [hS] using hqS
        have hone : q.intValuation (b : R) = 1 := by
          refine le_antisymm (q.intValuation_le_one _) (not_lt.mp ?_)
          rw [q.intValuation_lt_one_iff_dvd]
          exact hnd
        rw [hone]
        exact q.intValuation_le_one _
    have h4 : q.valuation K (algebraMap R K y / algebraMap R K (b : R)) * q.intValuation (b : R)
        ≤ 1 * q.intValuation (b : R) := by
      have vb : q.valuation K (algebraMap R K (b : R)) = q.intValuation (b : R) := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      have e1 : q.valuation K (algebraMap R K y / algebraMap R K (b : R)) * q.intValuation (b : R)
          = q.intValuation y := by
        rw [← vb, ← map_mul, key, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      rw [e1, one_mul]
      exact h5
    exact ennreal_volume_ratio_step_cancel (q.intValuation_ne_zero _ hd0) h4

end Bl.VolumeRatioCancellation
