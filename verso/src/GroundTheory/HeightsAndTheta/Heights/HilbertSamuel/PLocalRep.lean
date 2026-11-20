import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocalRep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocalRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Take `⟨m1, hm1, m2, hm2, rfl⟩` from `Finset.mem_add.mp (MvPolynomial.support_mul f g hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]`.
-/
theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hf m h k`. Conclude with `hg m h k`.
-/
theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Establish `: m = 0`. Assume the negation of the conclusion as `h`. Conclude with `(mem_support_iff.mp hm) (by rw [coeff_C, if_neg (Ne.symm h)])`. Substitute `this` using the available equality.

Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    exact (mem_support_iff.mp hm) (by rw [coeff_C, if_neg (Ne.symm h)])
  subst this
  simp

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k'`. Rewrite `hm` using `[MvPolynomial.support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Distinguish the cases in `h : k' = k`. Substitute `h` using the available equality.

Simplify using `[Finsupp.single_apply]`. Establish `: ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩` using `fun j e => h (congrArg Sigma.fst e).symm`. Simplify using `[h]`.
-/
theorem isMultiHomog_X [DecidableEq K] (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]

/- English proof (translation)
Establish `key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ e k) (∑ k ∈ s, e k • Pi.single k 1)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isMultiHomog_C (ι := ι) 1`. Consider the case `insert k s hk ih`.

Rewrite using `[Finset.prod_insert hk, Finset.sum_insert hk]`. Use `isMultiHomog_mul ?_ ih` and prove the remaining obligations. Proceed by induction on `e k with`. Consider the case `zero => simpa using isMultiHomog_C (ι := ι) 1`. Consider the case `succ m ihm`.

Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `isMultiHomog_mul ihm (isMultiHomog_X k (c k))`. Establish `h : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e`. Use extensionality with `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Use `key Finset.univ` as an intermediate fact. Rewrite `this` using `[h]`. Then use the resulting hypothesis.
-/
theorem isMultiHomog_chartMono (c : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k) e := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ e k)
      (∑ k ∈ s, e k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_C (ι := ι) 1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      refine isMultiHomog_mul ?_ ih
      induction e k with
      | zero => simpa using isMultiHomog_C (ι := ι) 1
      | succ m ihm =>
        rw [pow_succ, succ_nsmul]
        exact isMultiHomog_mul ihm (isMultiHomog_X k (c k))
  have h : (∑ k, e k • (Pi.single k 1 : K → ℕ)) = e := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [h] at this

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem u hu`. Take `⟨⟨k, i⟩, rfl⟩` from `hu`. Use `⟨Pi.single k 1, X ⟨k, i⟩, isMultiHomog_X k i, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_X, Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (by simp)]`.

Simplify using `only [Pi.single_eq_same, pow_one]`. Conclude with `(div_mul_cancel₀ _ (hc k)).symm`. Consider the case `algebraMap r`. Conclude with `⟨0, C r, isMultiHomog_C r, by simp⟩`. Consider the case `add u v _ _ hu hv`.

Take `⟨N₁, H₁, h₁, e₁⟩` from `hu`. Take `⟨N₂, H₂, h₂, e₂⟩` from `hv`. Use `⟨N₁ + N₂, H₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₂ k + H₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₁ k, isMultiHomog_add (isMultiHomog_mul h₁ (isMultiHomog_chartMono c N₂)) (add_comm N₂ N₁ ▸ isMultiHomog_mul h₂ (isMultiHomog_chartMono c N₁)), ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_prod, map_pow, aeval_X, e₁, e₂, Pi.add_apply, pow_add, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `mul u v _ _ hu hv`. Take `⟨N₁, H₁, h₁, e₁⟩` from `hu`. Take `⟨N₂, H₂, h₂, e₂⟩` from `hv`. Use `⟨N₁ + N₂, H₁ * H₂, isMultiHomog_mul h₁ h₂, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, e₁, e₂, Pi.add_apply, pow_add, Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (N : K → ℕ) (H : MRing ι), IsMultiHomog H N ∧ aeval y H = x * ∏ k, y ⟨k, c k⟩ ^ N k := by
  classical
  induction hx using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hu
    refine ⟨Pi.single k 1, X ⟨k, i⟩, isMultiHomog_X k i, ?_⟩
    rw [aeval_X, Finset.prod_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    simp only [Pi.single_eq_same, pow_one]
    exact (div_mul_cancel₀ _ (hc k)).symm
  | algebraMap r =>
    exact ⟨0, C r, isMultiHomog_C r, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₂ k + H₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ N₁ k,
      isMultiHomog_add (isMultiHomog_mul h₁ (isMultiHomog_chartMono c N₂))
        (add_comm N₂ N₁ ▸ isMultiHomog_mul h₂ (isMultiHomog_chartMono c N₁)), ?_⟩
    simp only [map_add, map_mul, map_prod, map_pow, aeval_X, e₁, e₂, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨N₁, H₁, h₁, e₁⟩ := hu
    obtain ⟨N₂, H₂, h₂, e₂⟩ := hv
    refine ⟨N₁ + N₂, H₁ * H₂, isMultiHomog_mul h₁ h₂, ?_⟩
    simp only [map_mul, e₁, e₂, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring

/- English proof (translation)
Introduce `K _ ι _ Ω _ y a n s z hs hz`. Use `choose c hzc using hz.1`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Introduce `k h0`. Apply `hzc k` to reduce the goal to its premises.

Establish `hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y` using `by show mConeMap y (X ⟨k, c k⟩) = 0`. Simplify using `[mConeMap, h0]`. Simplify using `using hz.2 _ hmem`. Take `⟨N, H, hH, he⟩` from `exists_form_of_mem_chartRingZ y c hyc (hs c hyc)`. Use `⟨N + fun k => ((n : ℤ) * a k).toNat, N + fun k => (-((n : ℤ) * a k)).toNat, H * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ ((n : ℤ) * a k).toNat, ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N + fun k => (-((n : ℤ) * a k)).toNat) k, isMultiHomog_mul hH (isMultiHomog_chartMono c _), isMultiHomog_chartMono c …` and prove the remaining obligations.

Simplify using `only [Pi.add_apply]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Simplify using `only [map_mul, map_prod, map_pow, aeval_X]`. Rewrite using `[he, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]`. Use `congr 1`. Simplify using `only [Pi.add_apply]`.

Use `push_cast`. Use linear arithmetic over natural numbers and integers. Simplify using `only [map_prod, map_pow, map_X, eval_X]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k)`.
-/
theorem proof : LocalRep.Statement := by
  intro K _ ι _ Ω _ y a n s z hs hz
  classical
  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  obtain ⟨N, H, hH, he⟩ := exists_form_of_mem_chartRingZ y c hyc (hs c hyc)
  refine ⟨N + fun k => ((n : ℤ) * a k).toNat, N + fun k => (-((n : ℤ) * a k)).toNat,
    H * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ ((n : ℤ) * a k).toNat,
    ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N + fun k => (-((n : ℤ) * a k)).toNat) k,
    isMultiHomog_mul hH (isMultiHomog_chartMono c _), isMultiHomog_chartMono c _, fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X]
    rw [he, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    omega
  · simp only [map_prod, map_pow, map_X, eval_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k)

end LocalRep

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
