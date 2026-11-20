import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt

open MvPolynomial

/- English proof (translation)
Use `by_contra! h`. Rewrite `hf` using `[hmon.as_sum]`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C] at hf`. Establish `hsum : x ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i` using `eq_neg_of_add_eq_zero_left hf`. Establish `hpos : 0 < f.natDegree`.

Break down `Nat.eq_zero_or_pos f.natDegree with h0 | h0` into its components or cases. Rewrite `hsum` using `[h0]`. Simplify using `at hsum`. Conclude with `h0`. Establish `hle : ‖∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ (f.natDegree - 1)`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Establish `hi' : i ≤ f.natDegree - 1`. Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Combine the equalities or inequalities in the displayed calculation. Establish `h1 : ‖x‖ ^ f.natDegree ≤ ‖x‖ ^ (f.natDegree - 1)`. Rewrite using `[← norm_pow, hsum, norm_neg]`. Conclude with `hle`. Establish `h2 : ‖x‖ ^ (f.natDegree - 1) < ‖x‖ ^ f.natDegree` using `pow_lt_pow_right₀ h (by omega)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_one_of_monic_eval₂ {𝕜 : Type} [NormedField 𝕜] [IsUltrametricDist 𝕜] {R : Type} [CommRing R]
    (φ : R →+* 𝕜) (hφ : ∀ r, ‖φ r‖ ≤ 1) {f : Polynomial R} (hmon : f.Monic) {x : 𝕜}
    (hf : f.eval₂ φ x = 0) : ‖x‖ ≤ 1 := by
  by_contra! h
  rw [hmon.as_sum] at hf
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at hf
  have hsum : x ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left hf
  have hpos : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
    · rw [h0] at hsum
      simp at hsum
    · exact h0
  have hle : ‖∑ i ∈ Finset.range f.natDegree, φ (f.coeff i) * x ^ i‖ ≤ ‖x‖ ^ (f.natDegree - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun i hi => ?_
    rw [norm_mul, norm_pow]
    have hi' : i ≤ f.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖φ (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (f.natDegree - 1) :=
          mul_le_mul (hφ _) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = ‖x‖ ^ (f.natDegree - 1) := one_mul _
  have h1 : ‖x‖ ^ f.natDegree ≤ ‖x‖ ^ (f.natDegree - 1) := by
    rw [← norm_pow, hsum, norm_neg]
    exact hle
  have h2 : ‖x‖ ^ (f.natDegree - 1) < ‖x‖ ^ f.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

section Ring

variable {Ω : Type} [Field Ω] {𝕜 : Type} [NormedField 𝕜] [IsUltrametricDist 𝕜]

def unitBall (A : Subring Ω) (ev : A →+* 𝕜) : Subring Ω where
  carrier := {x | ∃ h : x ∈ A, ‖ev ⟨x, h⟩‖ ≤ 1}
  mul_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have e : (⟨a * b, A.mul_mem ha hb⟩ : A) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul, norm_mul]
    exact mul_le_one₀ ha1 (norm_nonneg _) hb1
  one_mem' := by
    refine ⟨A.one_mem, ?_⟩
    have e : (⟨1, A.one_mem⟩ : A) = 1 := rfl
    rw [e, map_one, norm_one]
  add_mem' := by
    rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    refine ⟨A.add_mem ha hb, ?_⟩
    have e : (⟨a + b, A.add_mem ha hb⟩ : A) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha1 hb1)
  zero_mem' := by
    refine ⟨A.zero_mem, ?_⟩
    have e : (⟨0, A.zero_mem⟩ : A) = 0 := rfl
    rw [e, map_zero, norm_zero]
    exact zero_le_one
  neg_mem' := by
    rintro a ⟨ha, ha1⟩
    refine ⟨A.neg_mem ha, ?_⟩
    have e : (⟨-a, A.neg_mem ha⟩ : A) = -⟨a, ha⟩ := rfl
    rw [e, map_neg, norm_neg]
    exact ha1

/- English proof (translation)
Take `⟨f, hmon, hf⟩` from `ht`. Set `ψ : R →+* A` to `{ toFun := fun r => ⟨r, (hR r r.2).1⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `h1 : f.eval₂ ψ ⟨t, hb⟩ = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(Polynomial.hom_eval₂ f ψ A.subtype ⟨t, hb⟩).trans hf`.

Establish `h2 : f.eval₂ (ev.comp ψ) (ev ⟨t, hb⟩) = 0`. Rewrite using `[← Polynomial.hom_eval₂, h1, map_zero]`. Conclude with `norm_le_one_of_monic_eval₂ (ev.comp ψ) (fun r => (hR r r.2).2) hmon h2`.
-/
theorem norm_ev_le_one (A : Subring Ω) (ev : A →+* 𝕜) (R : Subalgebra ℤ Ω)
    (hR : ∀ x ∈ R, ∃ h : x ∈ A, ‖ev ⟨x, h⟩‖ ≤ 1) {t : Ω} (ht : t ∈ integralClosure R Ω) (hb : t ∈ A) :
    ‖ev ⟨t, hb⟩‖ ≤ 1 := by
  obtain ⟨f, hmon, hf⟩ := ht
  let ψ : R →+* A :=
    { toFun := fun r => ⟨r, (hR r r.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h1 : f.eval₂ ψ ⟨t, hb⟩ = 0 := by
    apply Subtype.ext
    exact (Polynomial.hom_eval₂ f ψ A.subtype ⟨t, hb⟩).trans hf
  have h2 : f.eval₂ (ev.comp ψ) (ev ⟨t, hb⟩) = 0 := by
    rw [← Polynomial.hom_eval₂, h1, map_zero]
  exact norm_le_one_of_monic_eval₂ (ev.comp ψ) (fun r => (hR r r.2).2) hmon h2

end Ring

section Pt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {y : (Σ k, ι k) → Ω} {𝕜 : Type} [Field 𝕜] {z : (Σ k, ι k) → 𝕜}

/- English proof (translation)
Introduce `m hm b`. Rewrite `hm` using `[support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Distinguish the cases in `hb : b = k`. Substitute `hb` using the available equality.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`.

Conclude with `hj (by simpa using h.symm)`. Simplify using the standard rewrite rules. Rewrite using `[Pi.single_eq_of_ne hb]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `h`. Conclude with `hb (congrArg Sigma.fst h).symm`.
-/
theorem isMultiHomog_X_single [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm b
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases hb : b = k
  · subst hb
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hj (by simpa using h.symm)
    · simp
  · rw [Pi.single_eq_of_ne hb]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hb (congrArg Sigma.fst h).symm

/- English proof (translation)
Use `⟨Pi.single k 1, 0, X ⟨k, i⟩, 1, isMultiHomog_X_single k i, ?_, fun b => ?_, by simp, by simp, by simp⟩` and prove the remaining obligations. Conclude with `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one`. Distinguish the cases in `hb : b = k`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_eq_of_ne hb]`.
-/
theorem hasVal_coord [DecidableEq K] (k : K) (i : ι k) :
    Small.HasVal y (Pi.single k 1) (y ⟨k, i⟩) z (z ⟨k, i⟩) := by
  refine ⟨Pi.single k 1, 0, X ⟨k, i⟩, 1, isMultiHomog_X_single k i, ?_, fun b => ?_, by simp, by simp, by simp⟩
  · exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one
  · by_cases hb : b = k
    · subst hb
      simp
    · simp [Pi.single_eq_of_ne hb]

/- English proof (translation)
Use `⟨Pi.single k 1, Pi.single k 1, X ⟨k, i⟩, X ⟨k, c⟩, isMultiHomog_X_single k i, isMultiHomog_X_single k c, fun b => by simp, ?_, by simpa using hz, ?_⟩` and prove the remaining obligations. Simplify using `only [aeval_X]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [aeval_X]`. Clear the denominators using the available nonvanishing facts.
-/
theorem hasVal_ratio_coord {k : K} (i c : ι k) (hy : y ⟨k, c⟩ ≠ 0) (hz : z ⟨k, c⟩ ≠ 0) :
    Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c⟩) z (z ⟨k, i⟩ / z ⟨k, c⟩) := by
  classical
  refine ⟨Pi.single k 1, Pi.single k 1, X ⟨k, i⟩, X ⟨k, c⟩, isMultiHomog_X_single k i, isMultiHomog_X_single k c,
    fun b => by simp, ?_, by simpa using hz, ?_⟩
  · simp only [aeval_X]
    field_simp
  · simp only [aeval_X]
    field_simp

/- English proof (translation)
Introduce `h0`. Establish `hm : (X p : MRing ι) ∈ mCoordIdeal y` using `by show mConeMap y (X p) = 0`. Simplify using `[mConeMap, h0]`. Conclude with `h (by simpa using hz.2 _ hm)`.
-/
theorem coord_ne_zero (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) (p : Σ k, ι k) (h : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  have hm : (X p : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (X p) = 0
    simp [mConeMap, h0]
  exact h (by simpa using hz.2 _ hm)

end Pt

/- English proof (translation)
Introduce `K _ ι _ Ω _ y 𝕜 _ _ z hz A ev a s hs H`. Establish `hc : ∀ k, ∃ c : ι k, ∀ i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c⟩‖` using `fun k => by`. Take `⟨i0, -⟩` from `hz.1 k`. Use `haveI : Nonempty (ι k) := ⟨i0⟩`. Conclude with `Finite.exists_max (fun i => ‖z ⟨k, i⟩‖)`.

Use `choose c hc using hc`. Establish `hzc : ∀ k, z ⟨k, c k⟩ ≠ 0` using `fun k h0 => by`. Take `⟨i0, hi0⟩` from `hz.1 k`. Establish `h1` using `hc k i0`. Rewrite `h1` using `[h0, norm_zero]`.

Conclude with `hi0 (norm_le_zero_iff.1 h1)`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => coord_ne_zero hz _ (hzc k)`. Take `⟨hr, hb, hv⟩` from `H c hyc`. Establish `hle : chartRingZ y c ≤ subalgebraOfSubring (unitBall A ev)`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨k, i⟩, rfl⟩`. Take `⟨hb', hv'⟩` from `hr k i`. Establish `e` using `Small.ReadFinTest.hasVal_unique hz hv' (hasVal_ratio_coord i (c k) (hyc k) (hzc k))`. Use `⟨hb', ?_⟩` and prove the remaining obligations. Rewrite using `[e, norm_div]`.

Conclude with `div_le_one_of_le₀ (hc k i) (norm_nonneg _)`. Establish `hn : ‖ev ⟨_, hb⟩‖ ≤ 1` using `norm_ev_le_one A ev _ (fun x hx => hle hx) (hs c hyc) hb`. Use `⟨ev ⟨_, hb⟩ * ∏ k, z ⟨k, c k⟩ ^ a k, ?_, ?_⟩` and prove the remaining obligations. Establish `hp : ∀ k ∈ (Finset.univ : Finset K), Small.HasVal y (a k • (Pi.single k 1 : K → ℤ)) (y ⟨k, c k⟩ ^ a k) z (z ⟨k, c k⟩ ^ a k)` using `fun k _ => hv_zpow hz (hasVal_coord k (c k)) (hyc k) (hzc k) (a k)`. Establish `h3` using `hv_mul hv (hv_prod Finset.univ hp)`.

Establish `e1 : (0 : K → ℤ) + ∑ k, a k • (Pi.single k 1 : K → ℤ) = a`. Use function extensionality and compare the values at `b`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `e2 : (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ a k = s`. Rewrite using `[mul_assoc, ← Finset.prod_mul_distrib]`.

Establish `: ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) * y ⟨k, c k⟩ ^ a k = 1` using `fun k => by`. Rewrite using `[← zpow_add₀ (hyc k)]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_congr rfl fun k _ => this k, Finset.prod_const_one, mul_one]`. Rewrite `h3` using `[e1, e2]`.

Conclude with `h3`. Establish `hm : Small.supMet a z = ∏ k, ‖z ⟨k, c k⟩‖ ^ a k`. Unfold `Small.supMet`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (hc k)) (norm_le_pi_norm (fun i => z ⟨k, i⟩) (c k))]`.

Rewrite using `[norm_mul, norm_prod, hm]`. Simplify using `only [norm_zpow]`. Conclude with `mul_le_of_le_one_left (Finset.prod_nonneg fun k _ => by positivity) hn`.
-/
theorem exists_hasVal_norm_le_supMet :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (𝕜 : Type) [NormedField 𝕜] [IsUltrametricDist 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → ∀ (A : Subring Ω) (ev : A →+* 𝕜) (a : K → ℤ), ∀ s ∈ chartLatNm y a 1, (∀ (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (∀ k i, ∃ hb : y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A, Small.HasVal y 0 (y ⟨k, i⟩ / y ⟨k, c k⟩) z (ev ⟨_, hb⟩)) ∧ ∃ hb : s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) ∈ A, Small.HasVal y 0 (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) z (ev ⟨_, hb⟩)) → ∃ w, Small.HasVal y a s z w ∧ ‖w‖ ≤ Small.supMet a z := by
  classical
  intro K _ ι _ Ω _ y 𝕜 _ _ z hz A ev a s hs H
  have hc : ∀ k, ∃ c : ι k, ∀ i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c⟩‖ := fun k => by
    obtain ⟨i0, -⟩ := hz.1 k
    haveI : Nonempty (ι k) := ⟨i0⟩
    exact Finite.exists_max (fun i => ‖z ⟨k, i⟩‖)
  choose c hc using hc
  have hzc : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have h1 := hc k i0
    rw [h0, norm_zero] at h1
    exact hi0 (norm_le_zero_iff.1 h1)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => coord_ne_zero hz _ (hzc k)
  obtain ⟨hr, hb, hv⟩ := H c hyc
  have hle : chartRingZ y c ≤ subalgebraOfSubring (unitBall A ev) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    obtain ⟨hb', hv'⟩ := hr k i
    have e := Small.ReadFinTest.hasVal_unique hz hv' (hasVal_ratio_coord i (c k) (hyc k) (hzc k))
    refine ⟨hb', ?_⟩
    rw [e, norm_div]
    exact div_le_one_of_le₀ (hc k i) (norm_nonneg _)
  have hn : ‖ev ⟨_, hb⟩‖ ≤ 1 := norm_ev_le_one A ev _ (fun x hx => hle hx) (hs c hyc) hb
  refine ⟨ev ⟨_, hb⟩ * ∏ k, z ⟨k, c k⟩ ^ a k, ?_, ?_⟩
  · have hp : ∀ k ∈ (Finset.univ : Finset K), Small.HasVal y (a k • (Pi.single k 1 : K → ℤ)) (y ⟨k, c k⟩ ^ a k) z
        (z ⟨k, c k⟩ ^ a k) := fun k _ => hv_zpow hz (hasVal_coord k (c k)) (hyc k) (hzc k) (a k)
    have h3 := hv_mul hv (hv_prod Finset.univ hp)
    have e1 : (0 : K → ℤ) + ∑ k, a k • (Pi.single k 1 : K → ℤ) = a := by
      funext b
      simp [Finset.sum_apply, Pi.single_apply]
    have e2 : (s * ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ a k = s := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      have : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a k)) * y ⟨k, c k⟩ ^ a k = 1 := fun k => by
        rw [← zpow_add₀ (hyc k)]
        simp
      rw [Finset.prod_congr rfl fun k _ => this k, Finset.prod_const_one, mul_one]
    rw [e1, e2] at h3
    exact h3
  · have hm : Small.supMet a z = ∏ k, ‖z ⟨k, c k⟩‖ ^ a k := by
      unfold Small.supMet
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (hc k))
        (norm_le_pi_norm (fun i => z ⟨k, i⟩) (c k))]
    rw [norm_mul, norm_prod, hm]
    simp only [norm_zpow]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun k _ => by positivity) hn

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ChartPt
