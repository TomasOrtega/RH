import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField IsDedekindDomain

namespace BeSumPf

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Unfold `vla`. Conclude with `Associates.count_ne_zero_iff_dvd hI la.irreducible`.
-/
theorem vla_ne_zero_iff (la : HeightOneSpectrum (𝓞 K)) {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    vla la I ≠ 0 ↔ la.asIdeal ∣ I := by
    unfold vla
    exact Associates.count_ne_zero_iff_dvd hI la.irreducible

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem maxPow_eq (v : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) :
    v.maxPowDividing I = v.asIdeal ^ vla v I := rfl

/- English proof (translation)
Establish `hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I) ⊆ ↑s`. Introduce `v hv`. Apply `hs` to reduce the goal to its premises. Introduce `h0`. Conclude with `hv (by show v.maxPowDividing I = 1; rw [maxPow_eq, h0, pow_zero])`.

Establish `hfac : ∏ v ∈ s, v.maxPowDividing I = I`. Rewrite using `[← finprod_eq_prod_of_mulSupport_subset _ hsub]`. Conclude with `Ideal.finprod_heightOneSpectrum_factorization hI`. Establish `hN : (Ideal.absNorm I : ℝ) = ∏ v ∈ s, ((Ideal.absNorm v.asIdeal : ℝ)) ^ vla v I` using `by conv_lhs => rw [← hfac]`. Rewrite using `[map_prod, Nat.cast_prod]`.

Use `Finset.prod_congr rfl (fun v _ => ?_)` and prove the remaining obligations. Rewrite using `[maxPow_eq, map_pow, Nat.cast_pow]`. Rewrite using `[hN, Real.log_prod]`. Use `Finset.sum_congr rfl (fun v _ => ?_)` and prove the remaining obligations. Rewrite using `[Real.log_pow]`.

Introduce `v _`. Apply `pow_ne_zero` to reduce the goal to its premises. Conclude with `Nat.cast_ne_zero.mpr (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)`.
-/
theorem sum_vla_log_fin (I : Ideal (𝓞 K)) (hI : I ≠ 0) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ v, vla v I ≠ 0 → v ∈ s) :
    ∑ v ∈ s, (vla v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) = Real.log (Ideal.absNorm I : ℝ) := by
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I) ⊆ ↑s := by
    intro v hv
    apply hs
    intro h0
    exact hv (by show v.maxPowDividing I = 1; rw [maxPow_eq, h0, pow_zero])
  have hfac : ∏ v ∈ s, v.maxPowDividing I = I := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsub]
    exact Ideal.finprod_heightOneSpectrum_factorization hI
  have hN : (Ideal.absNorm I : ℝ) = ∏ v ∈ s, ((Ideal.absNorm v.asIdeal : ℝ)) ^ vla v I := by
    conv_lhs => rw [← hfac]
    rw [map_prod, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [maxPow_eq, map_pow, Nat.cast_pow]
  rw [hN, Real.log_prod]
  · refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Real.log_pow]
  · intro v _
    apply pow_ne_zero
    exact Nat.cast_ne_zero.mpr (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)

/- English proof (translation)
Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `h : ((n' : 𝓞 K)) = algebraMap ℤ (𝓞 K) (n' : ℤ)` using `by simp`. Rewrite using `[h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]`. Simplify using `[Int.natAbs_pow]`.
-/
theorem absNorm_span_nat (n' : ℕ) :
    Ideal.absNorm (Ideal.span {(n' : 𝓞 K)}) = n' ^ Module.finrank ℚ K := by
  rw [Ideal.absNorm_span_singleton]
  have h : ((n' : 𝓞 K)) = algebraMap ℤ (𝓞 K) (n' : ℤ) := by simp
  rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
  simp [Int.natAbs_pow]

end BeSumPf

open BeSumPf in
/- English proof (translation)
Introduce `E K _ _ _ _ n' A hn`. Establish `hspan : ∀ k : ℕ, k ≠ 0 → Ideal.span {(k : 𝓞 K)} ≠ 0`. Introduce `k hk`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hk` after adjusting the coercions.

Establish `hd0 : (discr E).natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)`. Establish `hI1 : discAt E K ≠ 0` using `hspan _ hd0`. Establish `hI2 : Ideal.span {(n' : 𝓞 K)} ≠ 0` using `hspan _ hn.ne'`. Establish `hfin` using `(Ideal.finite_factors hI1).union (Ideal.finite_factors hI2)`. Establish `hsupp : Function.support (beOf E (K` using `K) n' A) ⊆ {v | v.asIdeal ∣ discAt E K} ∪ {v | v.asIdeal ∣ Ideal.span {(n' : 𝓞 K)}} := by`.

Introduce `v hv`. Rewrite `hv` using `[Function.mem_support]`. Assume the negation of the conclusion as `hc`. Apply `hv` to reduce the goal to its premises. Establish `h1 : vla v (discAt E K) = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hc (Or.inl ((vla_ne_zero_iff v hI1).mp h))`. Establish `h2 : vla v (Ideal.span {(n' : 𝓞 K)}) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hc (Or.inr ((vla_ne_zero_iff v hI2).mp h))`.

Simplify using `[beOf, mOf, h1, h2]`. Use `⟨hfin.subset hsupp, ?_⟩` and prove the remaining obligations. Establish `hs1 : ∀ v, vla v (discAt E K) ≠ 0 → v ∈ hfin.toFinset` using `fun v h => by`. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Or.inl ((vla_ne_zero_iff v hI1).mp h)`.

Establish `hs2 : ∀ v, vla v (Ideal.span {(n' : 𝓞 K)}) ≠ 0 → v ∈ hfin.toFinset` using `fun v h => by`. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Or.inr ((vla_ne_zero_iff v hI2).mp h)`. Establish `hsum : ∑ᶠ la, beOf E (K` using `K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ) = ∑ la ∈ hfin.toFinset, beOf E (K := K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ) := by`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises.

Introduce `v hv`. Rewrite using `[Finset.mem_coe, Set.Finite.mem_toFinset]`. Apply `hsupp` to reduce the goal to its premises. Rewrite `hv`, the goal using `[Function.mem_support]`. Introduce `h`.

Apply `hv` to reduce the goal to its premises. Rewrite using `[h, zero_mul]`. Rewrite using `[hsum]`. Establish `hK : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Rewrite using `[div_le_iff₀ hK]`.

Establish `hle : ∑ la ∈ hfin.toFinset, beOf E (K` using `K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ) ≤ (A : ℝ) * (∑ la ∈ hfin.toFinset, (vla la (discAt E K) : ℝ) * Real.log (Ideal.absNorm la.asIdeal : ℝ) + ∑ la ∈ hfin.toFinset, (vla la (Ideal.span {(n' : 𝓞 K)}) : ℝ) * Real.log (Ideal.absNorm la.asIdeal : ℝ)) := by`. Rewrite using `[← Finset.sum_add_distrib, Finset.mul_sum]`. Use `Finset.sum_le_sum (fun v _ => ?_)` and prove the remaining obligations. Establish `hl : 0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ)` using `Real.log_natCast_nonneg _`. Establish `hm : (mOf E n' v : ℝ) ≤ (vla v (discAt E K) : ℝ) + (vla v (Ideal.span {(n' : 𝓞 K)}) : ℝ)`.

Unfold `mOf`. Use `push_cast`. Conclude with `max_le_add_of_nonneg (by positivity) (by positivity)`. Unfold `beOf`. Combine the equalities or inequalities in the displayed calculation.

Use `hle.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[sum_vla_log_fin _ hI1 _ hs1, sum_vla_log_fin _ hI2 _ hs2]`. Establish `e1 : Ideal.absNorm (discAt E K) = (discr E).natAbs ^ Module.finrank ℚ K` using `absNorm_span_nat (discr E).natAbs`. Rewrite using `[e1, absNorm_span_nat n', Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]`. Establish `e2 : (((discr E).natAbs : ℕ) : ℝ) = |((discr E : ℤ) : ℝ)|`.

Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem beSum_holds : BeSumStatement := by
  intro E K _ _ _ _ n' A hn
  have hspan : ∀ k : ℕ, k ≠ 0 → Ideal.span {(k : 𝓞 K)} ≠ 0 := by
    intro k hk
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk
  have hd0 : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have hI1 : discAt E K ≠ 0 := hspan _ hd0
  have hI2 : Ideal.span {(n' : 𝓞 K)} ≠ 0 := hspan _ hn.ne'
  have hfin := (Ideal.finite_factors hI1).union (Ideal.finite_factors hI2)
  have hsupp : Function.support (beOf E (K := K) n' A) ⊆
      {v | v.asIdeal ∣ discAt E K} ∪ {v | v.asIdeal ∣ Ideal.span {(n' : 𝓞 K)}} := by
    intro v hv
    rw [Function.mem_support] at hv
    by_contra hc
    apply hv
    have h1 : vla v (discAt E K) = 0 := by
      by_contra h
      exact hc (Or.inl ((vla_ne_zero_iff v hI1).mp h))
    have h2 : vla v (Ideal.span {(n' : 𝓞 K)}) = 0 := by
      by_contra h
      exact hc (Or.inr ((vla_ne_zero_iff v hI2).mp h))
    simp [beOf, mOf, h1, h2]
  refine ⟨hfin.subset hsupp, ?_⟩
  have hs1 : ∀ v, vla v (discAt E K) ≠ 0 → v ∈ hfin.toFinset := fun v h => by
    rw [Set.Finite.mem_toFinset]
    exact Or.inl ((vla_ne_zero_iff v hI1).mp h)
  have hs2 : ∀ v, vla v (Ideal.span {(n' : 𝓞 K)}) ≠ 0 → v ∈ hfin.toFinset := fun v h => by
    rw [Set.Finite.mem_toFinset]
    exact Or.inr ((vla_ne_zero_iff v hI2).mp h)
  have hsum : ∑ᶠ la, beOf E (K := K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ) =
      ∑ la ∈ hfin.toFinset, beOf E (K := K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro v hv
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    apply hsupp
    rw [Function.mem_support] at hv ⊢
    intro h
    apply hv
    rw [h, zero_mul]
  rw [hsum]
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  rw [div_le_iff₀ hK]
  have hle : ∑ la ∈ hfin.toFinset, beOf E (K := K) n' A la * Real.log (Ideal.absNorm la.asIdeal : ℝ) ≤
      (A : ℝ) * (∑ la ∈ hfin.toFinset, (vla la (discAt E K) : ℝ) * Real.log (Ideal.absNorm la.asIdeal : ℝ) +
        ∑ la ∈ hfin.toFinset, (vla la (Ideal.span {(n' : 𝓞 K)}) : ℝ) *
          Real.log (Ideal.absNorm la.asIdeal : ℝ)) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum (fun v _ => ?_)
    have hl : 0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) := Real.log_natCast_nonneg _
    have hm : (mOf E n' v : ℝ) ≤ (vla v (discAt E K) : ℝ) + (vla v (Ideal.span {(n' : 𝓞 K)}) : ℝ) := by
      unfold mOf
      push_cast
      exact max_le_add_of_nonneg (by positivity) (by positivity)
    unfold beOf
    calc (A : ℝ) * (mOf E n' v : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)
        ≤ (A : ℝ) * ((vla v (discAt E K) : ℝ) + (vla v (Ideal.span {(n' : 𝓞 K)}) : ℝ)) *
            Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg A)) hl
      _ = _ := by ring
  refine hle.trans (le_of_eq ?_)
  rw [sum_vla_log_fin _ hI1 _ hs1, sum_vla_log_fin _ hI2 _ hs2]
  have e1 : Ideal.absNorm (discAt E K) = (discr E).natAbs ^ Module.finrank ℚ K :=
    absNorm_span_nat (discr E).natAbs
  rw [e1, absNorm_span_nat n', Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
  have e2 : (((discr E).natAbs : ℕ) : ℝ) = |((discr E : ℤ) : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [e2]
  ring

end Formalism.L2.Pj.QAt
