import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter.AvoidRing

noncomputable section

namespace LocRingPow

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

open Classical in

def multiDegWeight (ι : K → Type*) : (Σ k, ι k) → (K → ℕ) := fun p k => if p.1 = k then 1 else 0

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[← weight_blockWeight k m, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, multiDegWeight, blockWeight]`.
-/
theorem weight_multiDegWeight (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (multiDegWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by
  classical
  funext k
  rw [← weight_blockWeight k m, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
    Finset.sum_apply]
  simp only [Pi.smul_apply, multiDegWeight, blockWeight]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Rewrite using `[weight_multiDegWeight]`. Use function extensionality and compare the values at `k`. Conclude with `h d (mem_support_iff.mpr hd) k`.

Introduce `h m hm k`. Use `h (mem_support_iff.mp hm)` as an intermediate fact. Rewrite `this` using `[weight_multiDegWeight]`. Conclude with `congrFun this k`.
-/
theorem isMultiHomog_iff {f : MRing ι} {a : K → ℕ} :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (multiDegWeight ι) f a := by
  constructor
  · intro h d hd
    rw [weight_multiDegWeight]
    funext k
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    rw [weight_multiDegWeight] at this
    exact congrFun this k

/- English proof (translation)
Take `⟨g, hg, hgc⟩` from `exists_blockComponent (isHomogeneous_of_isMultiHomogIdeal hJ) D Finset.univ hf`. Use `hg using 1` and compare the differences between its conclusion and the goal. Use extensionality with `m`. Rewrite using `[coeff_weightedHomogeneousComponent, hgc, weight_multiDegWeight]`. Distinguish the cases in `h : ∀ k, ∑ i, m ⟨k, i⟩ = D k`.

Simplify using `[h]`. Simplify using `[h, funext_iff]`.
-/
theorem component_mem [DecidableEq K] {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    (hf : f ∈ J) (D : K → ℕ) : weightedHomogeneousComponent (multiDegWeight ι) D f ∈ J := by
  obtain ⟨g, hg, hgc⟩ := exists_blockComponent (isHomogeneous_of_isMultiHomogIdeal hJ) D Finset.univ hf
  convert hg using 1
  ext m
  rw [coeff_weightedHomogeneousComponent, hgc, weight_multiDegWeight]
  by_cases h : ∀ k, ∑ i, m ⟨k, i⟩ = D k
  · simp [h]
  · simp [h, funext_iff]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`. Apply `hf` to reduce the goal to its premises. Rewrite using `[← sum_weightedHomogeneousComponent (w := multiDegWeight ι) (φ := f), finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]`. Conclude with `Ideal.sum_mem _ fun D _ => h D`.
-/
theorem exists_component_not_mem {J : Ideal (MRing ι)} {f : MRing ι} (hf : f ∉ J) :
    ∃ D : K → ℕ, weightedHomogeneousComponent (multiDegWeight ι) D f ∉ J := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hf
  rw [← sum_weightedHomogeneousComponent (w := multiDegWeight ι) (φ := f),
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  exact Ideal.sum_mem _ fun D _ => h D

attribute [local instance] MvPolynomial.weightedGradedAlgebra

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]`. Conclude with `DirectSum.coe_decompose_mul_add_of_right_mem (weightedHomogeneousSubmodule ℤ (multiDegWeight ι)) ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg)`.
-/
theorem component_mul_right [DecidableEq K] {f g : MRing ι} {i j : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) :
    weightedHomogeneousComponent (multiDegWeight ι) (i + j) (f * g) =
      weightedHomogeneousComponent (multiDegWeight ι) i f * g := by
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_add_of_right_mem (weightedHomogeneousSubmodule ℤ (multiDegWeight ι))
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg)

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Rewrite using `[← weightedDecomposition.decompose'_apply]`. Conclude with `DirectSum.coe_decompose_mul_of_right_mem_of_not_le (weightedHomogeneousSubmodule ℤ (multiDegWeight ι)) ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg) h`.
-/
theorem component_mul_of_not_le [DecidableEq K] {f g : MRing ι} {j n : K → ℕ}
    (hg : IsWeightedHomogeneous (multiDegWeight ι) g j) (h : ¬ j ≤ n) :
    weightedHomogeneousComponent (multiDegWeight ι) n (f * g) = 0 := by
  rw [← weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_not_le (weightedHomogeneousSubmodule ℤ (multiDegWeight ι))
    ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hg) h

end LocRingPow

open LocRingPow in

/- English proof (translation)
Introduce `K _ ι _ P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hy`. Use `hPp` as an intermediate fact. Take `⟨hWmin, -⟩` from `hW`. Establish `hWp : W.IsPrime` using `hWmin.1.1`. Establish `hPW : P ≤ W` using `le_sup_left.trans hWmin.1.2`.

Choose the witnesses or unpack the hypotheses as in `⟨n, d, hdW, hd⟩ : ∃ n : ℕ, ∃ d ∉ W, d * u ^ n ∈ P ⊔ Ideal.span {s} := by`. Establish `hrad` using `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W _ hWmin`. Establish `hu' : algebraMap (MRing ι) (Localization.AtPrime W) u ∈ ((P ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).radical` using `hrad ▸ Ideal.mem_map_of_mem _ huW`. Take `⟨n, hn⟩` from `hu'`. Rewrite `hn` using `[← map_pow, IsLocalization.mem_map_algebraMap_iff W.primeCompl]`.

Take `⟨⟨⟨i, hi⟩, ⟨c, hc⟩⟩, he⟩` from `hn`. Rewrite `he` using `[← map_mul, IsLocalization.eq_iff_exists W.primeCompl]`. Take `⟨⟨e, he'⟩, hee⟩` from `he`. Use `⟨n, e * c, W.primeCompl.mul_mem he' hc, ?_⟩` and prove the remaining obligations. Establish `: e * c * u ^ n = e * (u ^ n * c)` using `by ring`.

Rewrite using `[this, hee]`. Conclude with `Ideal.mul_mem_left _ _ hi`. Take `⟨e, he⟩` from `exists_component_not_mem hdW`. Use `set ce := weightedHomogeneousComponent (multiDegWeight ι) e d with hce_def`. Establish `hce : IsMultiHomog ce e` using `isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)`.

Take `⟨p, hp, q, hq, hpq⟩` from `Submodule.mem_sup.mp hd`. Take `⟨g, rfl⟩` from `Ideal.mem_span_singleton'.mp hq`. Use `set D : K → ℕ := e + n • b with hD`. Establish `h1 : weightedHomogeneousComponent (multiDegWeight ι) D (d * u ^ n) = ce * u ^ n` using `component_mul_right (isMultiHomog_iff.mp (isMultiHomog_pow hu n))`. Choose the witnesses or unpack the hypotheses as in `⟨G, hG, hGs⟩ : ∃ G : MRing ι, IsMultiHomog (G * t) D ∧ weightedHomogeneousComponent (multiDegWeight ι) D (g * s) = G * s := by`.

Distinguish the cases in `hle : a ≤ D`. Use `⟨weightedHomogeneousComponent (multiDegWeight ι) (D - a) g, ?_, ?_⟩` and prove the remaining obligations. Use `isMultiHomog_mul (isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous (D - a) g)) ht` as an intermediate fact. Rewrite `this` using `[tsub_add_cancel_of_le hle]`. Then use the resulting hypothesis. Use `conv_lhs => rw [← tsub_add_cancel_of_le hle]`.

Conclude with `component_mul_right (isMultiHomog_iff.mp hs)`. Conclude with `⟨0, fun m hm => by simp at hm, by rw [zero_mul]; exact component_mul_of_not_le (isMultiHomog_iff.mp hs) hle⟩`. Establish `hrel : ce * u ^ n - G * s ∈ P`. Use `component_mem hPh hp D` as an intermediate fact. Rewrite `this` using `[← add_sub_cancel_right p (g * s), hpq, map_sub, h1, hGs]`. Then use the resulting hypothesis.

Establish `hden : ce * v ^ n ∉ W` using `fun h => (hWp.mem_or_mem h).elim he fun h => hvW (hWp.mem_of_pow_mem _ h)`. Establish `hdenP : Ideal.Quotient.mk P (ce * v ^ n) ∈ nonZeroDivisors (MRing ι ⧸ P)` using `mem_nonZeroDivisors_of_ne_zero fun h => hden (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))`. Use `⟨n, IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (G * t)) ⟨_, hdenP⟩, Subring.subset_closure ⟨G * t, ce * v ^ n, D, hdenP, hden, hG, isMultiHomog_mul hce (isMultiHomog_pow hv n), rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hne : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (ce * v ^ n)) ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdenP`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises.

Rewrite using `[mul_assoc x, IsLocalization.mk'_spec]`. Establish `key` using `congrArg (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))) (Ideal.Quotient.eq.mpr hrel)`. Simplify using `only [map_mul, map_pow] at key hx hy ⊢`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hx]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem LocRingPow.proof : LocRingPow.Statement := by
  classical
  intro K _ ι _ P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hy
  have := hPp
  obtain ⟨hWmin, -⟩ := hW
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2

  obtain ⟨n, d, hdW, hd⟩ : ∃ n : ℕ, ∃ d ∉ W, d * u ^ n ∈ P ⊔ Ideal.span {s} := by
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W _ hWmin
    have hu' : algebraMap (MRing ι) (Localization.AtPrime W) u ∈
        ((P ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).radical :=
      hrad ▸ Ideal.mem_map_of_mem _ huW
    obtain ⟨n, hn⟩ := hu'
    rw [← map_pow, IsLocalization.mem_map_algebraMap_iff W.primeCompl] at hn
    obtain ⟨⟨⟨i, hi⟩, ⟨c, hc⟩⟩, he⟩ := hn
    rw [← map_mul, IsLocalization.eq_iff_exists W.primeCompl] at he
    obtain ⟨⟨e, he'⟩, hee⟩ := he
    refine ⟨n, e * c, W.primeCompl.mul_mem he' hc, ?_⟩
    have : e * c * u ^ n = e * (u ^ n * c) := by ring
    rw [this, hee]
    exact Ideal.mul_mem_left _ _ hi

  obtain ⟨e, he⟩ := exists_component_not_mem hdW
  set ce := weightedHomogeneousComponent (multiDegWeight ι) e d with hce_def
  have hce : IsMultiHomog ce e :=
    isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hd
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hq

  set D : K → ℕ := e + n • b with hD
  have h1 : weightedHomogeneousComponent (multiDegWeight ι) D (d * u ^ n) = ce * u ^ n :=
    component_mul_right (isMultiHomog_iff.mp (isMultiHomog_pow hu n))
  obtain ⟨G, hG, hGs⟩ : ∃ G : MRing ι, IsMultiHomog (G * t) D ∧
      weightedHomogeneousComponent (multiDegWeight ι) D (g * s) = G * s := by
    by_cases hle : a ≤ D
    · refine ⟨weightedHomogeneousComponent (multiDegWeight ι) (D - a) g, ?_, ?_⟩
      · have := isMultiHomog_mul
          (isMultiHomog_iff.mpr (weightedHomogeneousComponent_isWeightedHomogeneous (D - a) g)) ht
        rwa [tsub_add_cancel_of_le hle] at this
      · conv_lhs => rw [← tsub_add_cancel_of_le hle]
        exact component_mul_right (isMultiHomog_iff.mp hs)
    · exact ⟨0, fun m hm => by simp at hm,
        by rw [zero_mul]; exact component_mul_of_not_le (isMultiHomog_iff.mp hs) hle⟩
  have hrel : ce * u ^ n - G * s ∈ P := by
    have := component_mem hPh hp D
    rwa [← add_sub_cancel_right p (g * s), hpq, map_sub, h1, hGs] at this

  have hden : ce * v ^ n ∉ W := fun h =>
    (hWp.mem_or_mem h).elim he fun h => hvW (hWp.mem_of_pow_mem _ h)
  have hdenP : Ideal.Quotient.mk P (ce * v ^ n) ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hden (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  refine ⟨n, IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (G * t)) ⟨_, hdenP⟩,
    Subring.subset_closure ⟨G * t, ce * v ^ n, D, hdenP, hden, hG, isMultiHomog_mul hce (isMultiHomog_pow hv n), rfl⟩,
    ?_⟩
  have hne : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (ce * v ^ n)) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdenP
  apply mul_right_cancel₀ hne
  rw [mul_assoc x, IsLocalization.mk'_spec]
  have key := congrArg (algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))) (Ideal.Quotient.eq.mpr hrel)
  simp only [map_mul, map_pow] at key hx hy ⊢
  calc y ^ n * (algebraMap _ _ (Ideal.Quotient.mk P ce) * algebraMap _ _ (Ideal.Quotient.mk P v) ^ n)
      = algebraMap _ _ (Ideal.Quotient.mk P ce) * (y * algebraMap _ _ (Ideal.Quotient.mk P v)) ^ n := by ring
    _ = algebraMap _ _ (Ideal.Quotient.mk P ce) * algebraMap _ _ (Ideal.Quotient.mk P u) ^ n := by rw [hy]
    _ = algebraMap _ _ (Ideal.Quotient.mk P G) * algebraMap _ _ (Ideal.Quotient.mk P s) := key
    _ = x * (algebraMap _ _ (Ideal.Quotient.mk P G) * algebraMap _ _ (Ideal.Quotient.mk P t)) := by
        rw [← hx]; ring

end

end GroundTheory.Heights₂.Heights.Inter
