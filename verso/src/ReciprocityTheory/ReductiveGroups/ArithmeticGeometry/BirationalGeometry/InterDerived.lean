import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use extensionality with `W`. Simplify using `only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]`. Introduce `hW`. Establish `hp` using `hW.1`. Establish `htop : (⊤ : Ideal (MRing ι)) ≤ W`.

Establish `h2` using `hp.2`. Rewrite `h2` using `[Ideal.span_singleton_one, sup_top_eq]`. Then use the resulting hypothesis. Conclude with `fun _ => hp.1.ne_top (top_le_iff.1 htop)`.
-/
theorem divSupp_one (P : Ideal (MRing ι)) : divSupp P 1 = ∅ := by
  ext W
  simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hW
  have hp := hW.1
  have htop : (⊤ : Ideal (MRing ι)) ≤ W := by
    have h2 := hp.2
    rwa [Ideal.span_singleton_one, sup_top_eq] at h2
  exact fun _ => hp.1.ne_top (top_le_iff.1 htop)

/- English proof (translation)
Simplify using `[logNorm, HermLine.ofWeight, Real.exp_neg, Real.log_exp]`.
-/
theorem logNorm_ofWeight_one (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) (z : (Σ k, ι k) → ℂ) :
    logNorm (HermLine.ofWeight u hu) 1 z = u z := by
  simp [logNorm, HermLine.ofWeight, Real.exp_neg, Real.log_exp]

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[MvPolynomial.support_one]`. Simplify using `only [Finset.mem_singleton] at hm`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
  intro m hm k
  rw [MvPolynomial.support_one] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  simp

/- English proof (translation)
Introduce `K _ ι _ I hI P n L A u hu hP hL hA hsm`. Establish `hB : IsSmoothHerm (HermLine.ofWeight u hu)` using `by show ContDiffOn ℝ _ (fun z => Real.exp (-u z)) _`. Conclude with `hsm.neg.exp`. Establish `h1 : (1 : MRing ι) ∉ P` using `fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)`. Establish `hlog : logNorm (HermLine.ofWeight u hu) 1 = u` using `funext (logNorm_ofWeight_one u hu)`.

Establish `hrec : recR I P L (HermLine.ofWeight u hu) 1 = -ptsIntegral P (pot L) u`. Unfold `recR`. Rewrite using `[divSupp_one]`. Simplify using `only [finsum_mem_empty, zero_sub, arInt, hlog]`. Both sides reduce to the same expression.

Rewrite using `[hI.2.1 P n L A _ hP hL hA hB, hI.2.2 P n L _ 1 (fun _ => 0) hP hL hB (fun _ => rfl) isMultiHomog_one h1, hrec]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem metricChange : MetricChangeStatement := by
  intro K _ ι _ I hI P n L A u hu hP hL hA hsm
  have hB : IsSmoothHerm (HermLine.ofWeight u hu) := by
    show ContDiffOn ℝ _ (fun z => Real.exp (-u z)) _
    exact hsm.neg.exp
  have h1 : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hlog : logNorm (HermLine.ofWeight u hu) 1 = u := funext (logNorm_ofWeight_one u hu)
  have hrec : recR I P L (HermLine.ofWeight u hu) 1 = -ptsIntegral P (pot L) u := by
    unfold recR
    rw [divSupp_one]
    simp only [finsum_mem_empty, zero_sub, arInt, hlog]
    rfl
  rw [hI.2.1 P n L A _ hP hL hA hB,
    hI.2.2 P n L _ 1 (fun _ => 0) hP hL hB (fun _ => rfl) isMultiHomog_one h1, hrec]
  ring

end ReciprocityTheory.ChartRestriction.G.Geo
