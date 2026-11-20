import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodB

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkWt : (Σ k, ι k) → (K →₀ ℕ) := fun p => Finsupp.single p.1 1

def oneK : K →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply, Fintype.sum_sigma]`. Use `(Finset.sum_eq_single k ?_ ?_).trans ?_` and prove the remaining obligations. Introduce `k' _ hk'`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Simplify using `[blkWt, Finsupp.single_apply, hk']`.

Simplify using the standard rewrite rules. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[blkWt]`.
-/
theorem weight_blkWt_apply (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blkWt (ι := ι)) m k = ∑ i, m ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply,
    Fintype.sum_sigma]
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [blkWt, Finsupp.single_apply, hk']
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [blkWt]

/- English proof (translation)
Introduce `d hd`. Establish `hd' : d ∈ f.support`. Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h`. Apply `hd` to reduce the goal to its premises.

Simplify using `[qmap, MvPolynomial.coeff_map, h]`. Use extensionality with `k`. Rewrite using `[weight_blkWt_apply, hf d hd' k]`. Simplify using the standard rewrite rules.
-/
theorem isWeightedHomogeneous_qmap (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (qmap f) (Finsupp.equivFunOnFinite.symm a) := by
  intro d hd
  have hd' : d ∈ f.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hd
    simp [qmap, MvPolynomial.coeff_map, h]
  ext k
  rw [weight_blkWt_apply, hf d hd' k]
  simp

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hP`. Rewrite using `[qIdeal, Ideal.map_span]`. Apply `Ideal.homogeneous_span` to reduce the goal to its premises. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hS f hf`.

Conclude with `⟨_, (mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_qmap f a ha)⟩`.
-/
theorem qIdeal_isHomogeneous (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) :
    (qIdeal P).IsHomogeneous (weightedHomogeneousSubmodule ℚ (blkWt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hP
  rw [qIdeal, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨_, (mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_qmap f a ha)⟩

def segMon (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℚ := ∏ k, X ⟨k, i k⟩

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℚ)) (fun k => blkWt (ι := ι) ⟨k, i k⟩) (fun k _ => isWeightedHomogeneous_X ℚ _ _)`. Establish `e : (∑ k ∈ Finset.univ, blkWt (ι` using `ι) ⟨k, i k⟩) = oneK := by`. Use extensionality with `k`. Rewrite using `[Finsupp.finset_sum_apply]`. Simplify using `only [blkWt, oneK, Finsupp.single_apply, Finsupp.coe_equivFunOnFinite_symm]`.

Simplify using the standard rewrite rules. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem segMon_isWeightedHomogeneous (i : (k : K) → ι k) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (segMon i) oneK := by
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℚ)) (fun k => blkWt (ι := ι) ⟨k, i k⟩)
    (fun k _ => isWeightedHomogeneous_X ℚ _ _)
  have e : (∑ k ∈ Finset.univ, blkWt (ι := ι) ⟨k, i k⟩) = oneK := by
    ext k
    rw [Finsupp.finset_sum_apply]
    simp only [blkWt, oneK, Finsupp.single_apply, Finsupp.coe_equivFunOnFinite_symm]
    simp
  rw [e] at h
  exact h

/- English proof (translation)
Rewrite using `[aeval_monomial, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]`. Establish `h0 : IsWeightedHomogeneous (blkWt (ι` using `ι)) (algebraMap ℚ (MvPolynomial (Σ k, ι k) ℚ) c) 0 := by`. Rewrite using `[MvPolynomial.algebraMap_eq]`. Conclude with `isWeightedHomogeneous_C _ _`. Establish `h1` using `h0.mul (IsWeightedHomogeneous.prod n.support (fun e => yt e ^ n e) (fun e => n e • w' e) (fun e _ => (hy e).pow (n e)))`.

Simplify using `using h1`.
-/
private theorem aeval_of_isWeightedHomogeneous_blkWt {E : Type*} (w' : E → (K →₀ ℕ))
    (yt : E → MvPolynomial (Σ k, ι k) ℚ)
    (hy : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (w' e)) (n : E →₀ ℕ) (c : ℚ) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (aeval yt (monomial n c)) (Finsupp.weight w' n) := by
  classical
  rw [aeval_monomial, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
  have h0 : IsWeightedHomogeneous (blkWt (ι := ι))
      (algebraMap ℚ (MvPolynomial (Σ k, ι k) ℚ) c) 0 := by
    rw [MvPolynomial.algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  have h1 := h0.mul (IsWeightedHomogeneous.prod n.support (fun e => yt e ^ n e)
    (fun e => n e • w' e) (fun e _ => (hy e).pow (n e)))
  simpa using h1

/- English proof (translation)
Proceed by induction on `H using MvPolynomial.induction_on' with`. Consider the case `monomial n c`. Distinguish the cases in `h : Finsupp.weight w' n = δ`. Substitute `h` using the available equality. Rewrite using `[(aeval_of_isWeightedHomogeneous_blkWt w' yt hy n c).weightedHomogeneousComponent_same, (isWeightedHomogeneous_monomial w' n c rfl).weightedHomogeneousComponent_same]`.

Rewrite using `[(aeval_of_isWeightedHomogeneous_blkWt w' yt hy n c).weightedHomogeneousComponent_ne δ (Ne.symm h), (isWeightedHomogeneous_monomial w' n c rfl).weightedHomogeneousComponent_ne δ (Ne.symm h), map_zero]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
-/
theorem component_aeval {E : Type*} (w' : E → (K →₀ ℕ))
    (yt : E → MvPolynomial (Σ k, ι k) ℚ)
    (hy : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (w' e)) (H : MvPolynomial E ℚ)
    (δ : K →₀ ℕ) :
    weightedHomogeneousComponent (blkWt (ι := ι)) δ (aeval yt H) =
      aeval yt (weightedHomogeneousComponent w' δ H) := by
  induction H using MvPolynomial.induction_on' with
  | monomial n c =>
    by_cases h : Finsupp.weight w' n = δ
    · subst h
      rw [(aeval_of_isWeightedHomogeneous_blkWt w' yt hy n c).weightedHomogeneousComponent_same,
        (isWeightedHomogeneous_monomial w' n c rfl).weightedHomogeneousComponent_same]
    · rw [(aeval_of_isWeightedHomogeneous_blkWt w' yt hy n c).weightedHomogeneousComponent_ne δ (Ne.symm h),
        (isWeightedHomogeneous_monomial w' n c rfl).weightedHomogeneousComponent_ne δ (Ne.symm h),
        map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

variable (k0 : K)

def sWt (r : ℕ) : Fin r ⊕ {k // k ≠ k0} → (K →₀ ℕ) :=
  Sum.elim (fun _ => oneK) (fun k' => Finsupp.single k'.1 1)

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply, Fintype.sum_sum_type]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `[sWt, oneK]`. Distinguish the cases in `h : k = k0`.

Substitute `h` using the available equality. Rewrite using `[dif_pos rfl]`. Use `Finset.sum_eq_zero fun k' _ => ?_` and prove the remaining obligations. Simplify using `[sWt, Finsupp.single_apply, k'.2]`. Rewrite using `[dif_neg h, Finset.sum_eq_single ⟨k, h⟩]`.

Simplify using `[sWt]`. Introduce `k' _ hk'`. Establish `: k'.1 ≠ k` using `fun e => hk' (Subtype.ext e)`. Simplify using `[sWt, Finsupp.single_apply, this]`. Simplify using the standard rewrite rules.
-/
theorem weight_sWt_apply {r : ℕ} (n : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ) (k : K) :
    Finsupp.weight (sWt k0 r) n k =
      (∑ j, n (Sum.inl j)) + (if h : k = k0 then 0 else n (Sum.inr ⟨k, h⟩)) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finset_sum_apply,
    Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [sWt, oneK]
  · by_cases h : k = k0
    · subst h
      rw [dif_pos rfl]
      refine Finset.sum_eq_zero fun k' _ => ?_
      simp [sWt, Finsupp.single_apply, k'.2]
    · rw [dif_neg h, Finset.sum_eq_single ⟨k, h⟩]
      · simp [sWt]
      · intro k' _ hk'
        have : k'.1 ≠ k := fun e => hk' (Subtype.ext e)
        simp [sWt, Finsupp.single_apply, this]
      · simp

/- English proof (translation)
Establish `h0 : Finsupp.weight (sWt k0 r) n k0 = Finsupp.weight (sWt k0 r) n0 k0` using `by rw [h]`. Establish `h1 : Finsupp.weight (sWt k0 r) n k'.1 = Finsupp.weight (sWt k0 r) n0 k'.1` using `by rw [h]`. Rewrite `h0` using `[weight_sWt_apply, weight_sWt_apply, dif_pos rfl, dif_pos rfl]`. Rewrite `h1` using `[weight_sWt_apply, weight_sWt_apply, dif_neg k'.2, dif_neg k'.2, Subtype.coe_eta]`. Use linear arithmetic over natural numbers and integers.
-/
theorem inr_eq_of_weight_eq {r : ℕ} {n n0 : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ}
    (h : Finsupp.weight (sWt k0 r) n = Finsupp.weight (sWt k0 r) n0) (k' : {k // k ≠ k0}) :
    n (Sum.inr k') = n0 (Sum.inr k') := by
  have h0 : Finsupp.weight (sWt k0 r) n k0 = Finsupp.weight (sWt k0 r) n0 k0 := by rw [h]
  have h1 : Finsupp.weight (sWt k0 r) n k'.1 = Finsupp.weight (sWt k0 r) n0 k'.1 := by rw [h]
  rw [weight_sWt_apply, weight_sWt_apply, dif_pos rfl, dif_pos rfl] at h0
  rw [weight_sWt_apply, weight_sWt_apply, dif_neg k'.2, dif_neg k'.2, Subtype.coe_eta] at h1
  omega

/- English proof (translation)
Establish `hw : ∀ n ∈ H.support, ∀ k', n (Sum.inr k') = n0 (Sum.inr k')` using `fun n hn k' => inr_eq_of_weight_eq k0 ((hH (mem_support_iff.mp hn)).trans (hH (mem_support_iff.mp hn0)).symm) k'`. Rewrite using `[aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_sum_type, Fintype.prod_sum_type]`. Establish `hp : ∏ k', b k' ^ n (Sum.inr k') = ∏ k', b k' ^ n0 (Sum.inr k')` using `Finset.prod_congr rfl fun k' _ => by rw [hw n hn k']`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_pow, Finset.prod_const_one, mul_one, hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_sumElim_factor {S : Type*} [CommRing S] [Algebra ℚ S] {r : ℕ}
    {H : MvPolynomial (Fin r ⊕ {k // k ≠ k0}) ℚ} {δ : K →₀ ℕ}
    (hH : IsWeightedHomogeneous (sWt k0 r) H δ) {n0 : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ}
    (hn0 : n0 ∈ H.support) (a : Fin r → S) (b : {k // k ≠ k0} → S) :
    aeval (Sum.elim a b) H = (∏ k', b k' ^ n0 (Sum.inr k')) * aeval (Sum.elim a 1) H := by
  classical
  have hw : ∀ n ∈ H.support, ∀ k', n (Sum.inr k') = n0 (Sum.inr k') := fun n hn k' =>
    inr_eq_of_weight_eq k0
      ((hH (mem_support_iff.mp hn)).trans (hH (mem_support_iff.mp hn0)).symm) k'
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  have hp : ∏ k', b k' ^ n (Sum.inr k') = ∏ k', b k' ^ n0 (Sum.inr k') :=
    Finset.prod_congr rfl fun k' _ => by rw [hw n hn k']
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_pow, Finset.prod_const_one, mul_one, hp]
  ring

end

end ReciprocityTheory.ChartRestriction.G.Geo
