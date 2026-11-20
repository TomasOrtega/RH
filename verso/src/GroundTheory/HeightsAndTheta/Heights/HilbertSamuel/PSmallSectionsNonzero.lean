import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionsNonzero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SmallSectionsNonzero

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Take `⟨m₁, hm₁, m₂, hm₂, rfl⟩` from `Finset.mem_add.mp (support_mul g h hm)`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]`. Rewrite using `[hg m₁ hm₁ k, hh m₂ hm₂ k]`.
-/
theorem isMultiHomog_mul {g h : MRing ι} {a b : K → ℕ} (hg : IsMultiHomog g a)
    (hh : IsMultiHomog h b) : IsMultiHomog (g * h) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul g h hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hg m₁ hm₁ k, hh m₂ hm₂ k]

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm`. Break down `Finset.mem_union.mp (support_sub _ g h hm) with hm | hm` into its components or cases. Conclude with `hg m hm`. Conclude with `hh m hm`.
-/
theorem isMultiHomog_sub {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) : IsMultiHomog (g - h) d := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_sub _ g h hm) with hm | hm
  · exact hg m hm
  · exact hh m hm

omit [Fintype K] in

/- English proof (translation)
Introduce `m hm k`. Rewrite using `[Finset.mem_singleton.mp (support_monomial_subset hm)]`.
-/
theorem isMultiHomog_monomial (e : (Σ k, ι k) →₀ ℕ) (r : ℤ) :
    IsMultiHomog (monomial e r : MRing ι) (fun k => ∑ i, e ⟨k, i⟩) := by
  classical
  intro m hm k
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]

omit [Fintype K] in
open Classical in

/- English proof (translation)
Distinguish the cases in `h : k' = k`. Substitute `h` using the available equality. Simplify using `[Finsupp.single_apply]`. Rewrite using `[if_neg h]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `he`. Conclude with `h (Sigma.mk.inj_iff.mp he).1`.
-/
theorem sum_single_apply (k' : K) (j : ι k') (b : ℕ) (k : K) :
    ∑ i, (Finsupp.single (⟨k', j⟩ : Σ k, ι k) b) ⟨k, i⟩ = if k' = k then b else 0 := by
  classical
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro he
    exact h (Sigma.mk.inj_iff.mp he).1

def chartMono (c : ∀ k, ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

/- English proof (translation)
Establish `h : chartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)`. Rewrite using `[chartMono, monomial_sum_one]`. Conclude with `Finset.prod_congr rfl fun k _ => X_pow_eq_monomial`. Establish `hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d`. Use function extensionality and compare the values at `k`.

Simplify using `only [Finsupp.finsetSum_apply]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [sum_single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[h]`. Establish `hm` using `isMultiHomog_monomial (ι := ι) (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)`.

Rewrite `hm` using `[hd]`. Conclude with `hm`.
-/
theorem isMultiHomog_chartMono (c : ∀ k, ι k) (d : K → ℕ) : IsMultiHomog (chartMono c d) d := by
  classical
  have h : chartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
    rw [chartMono, monomial_sum_one]
    exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
  have hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d := by
    funext k
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  have hm := isMultiHomog_monomial (ι := ι) (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)
  rw [hd] at hm
  exact hm

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Simplify using `[chartMono, map_prod]`.
-/
theorem aeval_chartMono (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (chartMono c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [chartMono, map_prod]

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Simplify using `[chartMono, map_prod]`.
-/
theorem eval_chartMono (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k) (d : K → ℕ) :
    eval z (map (Int.castRingHom ℂ) (chartMono c d)) = ∏ k, z ⟨k, c k⟩ ^ d k := by
  simp [chartMono, map_prod]

/- English proof (translation)
Use `show g ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hg, h0, map_zero, zero_mul]`.
-/
theorem mem_mCoordIdeal_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hg, h0, map_zero, zero_mul]

/- English proof (translation)
Establish `hX` using `isMultiHomog_monomial (ι := ι) (Finsupp.single p 1) 1`. Rewrite `hX` using `[← X]`. Conclude with `mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])`.
-/
theorem X_mem_mCoordIdeal (y : (Σ k, ι k) → Ω) (p : Σ k, ι k) (h0 : y p = 0) :
    (X p : MRing ι) ∈ mCoordIdeal y := by
  have hX := isMultiHomog_monomial (ι := ι) (Finsupp.single p 1) 1
  rw [← X] at hX
  exact mem_mCoordIdeal_of_aeval_eq_zero y hX (by rw [aeval_X, h0])

/- English proof (translation)
Establish `hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k = (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k` using `fun δ₁ δ₂ => by`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`. Rewrite `hx` using `[chartRingZ]`. Proceed by induction on `hx using Algebra.adjoin_induction with`.

Consider the case `mem x hx`. Take `⟨p, rfl⟩` from `hx`. Take `⟨k₀, j⟩` from `p`. Use `⟨fun k => ∑ i, (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) ⟨k, i⟩, X ⟨k₀, j⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) 1`.

Rewrite `h` using `[← X]`. Then use the resulting hypothesis. Establish `h1 : ∏ k, y ⟨k, c k⟩ ^ (∑ i, (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) ⟨k, i⟩) = y ⟨k₀, c k₀⟩`. Simplify using `only [sum_single_apply]`. Rewrite using `[Finset.prod_eq_single k₀ (fun k _ hk => by rw [if_neg (Ne.symm hk), pow_zero]) (fun h => absurd (Finset.mem_univ _) h)]`. Simplify using the standard rewrite rules.

Rewrite using `[aeval_X, h1, div_mul_cancel₀ _ (hc k₀)]`. Consider the case `algebraMap r`. Use `⟨fun _ => 0, C r, ?_, by simp⟩` and prove the remaining obligations. Establish `h` using `isMultiHomog_monomial (ι := ι) 0 r`. Simplify using `using h`.

Consider the case `add x w _ _ hx hw`. Take `⟨δ₁, e₁, h₁, v₁⟩` from `hx`. Take `⟨δ₂, e₂, h₂, v₂⟩` from `hw`. Use `⟨δ₁ + δ₂, e₁ * chartMono c δ₂ + e₂ * chartMono c δ₁, ?_, ?_⟩` and prove the remaining obligations. Introduce `m hm`.

Break down `Finset.mem_union.mp (support_add hm) with hm | hm` into its components or cases. Conclude with `isMultiHomog_mul h₁ (isMultiHomog_chartMono c δ₂) m hm`. Rewrite using `[add_comm δ₁]`. Conclude with `isMultiHomog_mul h₂ (isMultiHomog_chartMono c δ₁) m hm`. Rewrite using `[map_add, map_mul, map_mul, v₁, v₂, aeval_chartMono, aeval_chartMono, hpow]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x w _ _ hx hw`. Take `⟨δ₁, e₁, h₁, v₁⟩` from `hx`. Take `⟨δ₂, e₂, h₂, v₂⟩` from `hw`. Use `⟨δ₁ + δ₂, e₁ * e₂, isMultiHomog_mul h₁ h₂, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, v₁, v₂, hpow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_form_of_mem_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧ aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  classical
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨k₀, j⟩ := p
    refine ⟨fun k => ∑ i, (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) ⟨k, i⟩, X ⟨k₀, j⟩, ?_, ?_⟩
    · have h := isMultiHomog_monomial (ι := ι) (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) 1
      rwa [← X] at h
    · have h1 : ∏ k, y ⟨k, c k⟩ ^ (∑ i, (Finsupp.single (⟨k₀, j⟩ : Σ k, ι k) 1) ⟨k, i⟩) = y ⟨k₀, c k₀⟩ := by
        simp only [sum_single_apply]
        rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [if_neg (Ne.symm hk), pow_zero])
          (fun h => absurd (Finset.mem_univ _) h)]
        simp
      rw [aeval_X, h1, div_mul_cancel₀ _ (hc k₀)]
  | algebraMap r =>
    refine ⟨fun _ => 0, C r, ?_, by simp⟩
    have h := isMultiHomog_monomial (ι := ι) 0 r
    simpa using h
  | add x w _ _ hx hw =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hw
    refine ⟨δ₁ + δ₂, e₁ * chartMono c δ₂ + e₂ * chartMono c δ₁, ?_, ?_⟩
    · intro m hm
      rcases Finset.mem_union.mp (support_add hm) with hm | hm
      · exact isMultiHomog_mul h₁ (isMultiHomog_chartMono c δ₂) m hm
      · rw [add_comm δ₁]
        exact isMultiHomog_mul h₂ (isMultiHomog_chartMono c δ₁) m hm
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_chartMono, aeval_chartMono, hpow]
      ring
  | mul x w _ _ hx hw =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hw
    refine ⟨δ₁ + δ₂, e₁ * e₂, isMultiHomog_mul h₁ h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring

/- English proof (translation)
Establish `hx : s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) ∈ chartRingZ y c` using `hs c hc`. Take `⟨δ, e, he, hv⟩` from `exists_form_of_mem_chartRingZ y c hc hx`. Use `set ex : K → ℕ := fun k => ((n : ℤ) * a k + ((n : ℤ) * a k).natAbs).toNat with hex`. Establish `hexk : ∀ k, (ex k : ℤ) = (n : ℤ) * a k + ((n : ℤ) * a k).natAbs` using `fun k => by`. Rewrite using `[hex]`.

Conclude with `Int.toNat_of_nonneg (by omega)`. Use `⟨fun k => δ k + ((n : ℤ) * a k).natAbs, δ + ex, e * chartMono c ex, isMultiHomog_mul he (isMultiHomog_chartMono c ex), fun k => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Nat.cast_add, hexk k]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, hv, aeval_chartMono, aeval_chartMono, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`.

Use `congr 1`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h0` using `hc k`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0, hexk k]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_chartForm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLat y a n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (N dg : K → ℕ) (g : MRing ι), IsMultiHomog g dg ∧ (∀ k, (dg k : ℤ) = N k + n * a k) ∧
      aeval y g = s * aeval y (chartMono c N) := by
  have hx : s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) ∈ chartRingZ y c := hs c hc
  obtain ⟨δ, e, he, hv⟩ := exists_form_of_mem_chartRingZ y c hc hx
  set ex : K → ℕ := fun k => ((n : ℤ) * a k + ((n : ℤ) * a k).natAbs).toNat with hex
  have hexk : ∀ k, (ex k : ℤ) = (n : ℤ) * a k + ((n : ℤ) * a k).natAbs := fun k => by
    rw [hex]
    exact Int.toNat_of_nonneg (by omega)
  refine ⟨fun k => δ k + ((n : ℤ) * a k).natAbs, δ + ex, e * chartMono c ex,
    isMultiHomog_mul he (isMultiHomog_chartMono c ex), fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Nat.cast_add, hexk k]
    ring
  · rw [map_mul, hv, aeval_chartMono, aeval_chartMono, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 := hc k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0, hexk k]
    congr 1
    push_cast
    ring

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `c _`. Simplify using `only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]`. Conclude with `one_mem _`.
-/
theorem one_mem_chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) : (1 : Ω) ∈ chartLat y a 0 := by
  intro c _
  simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, Finset.prod_const_one, mul_one]
  exact one_mem _

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `c hc`. Establish `h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) = (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ (hc k)]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) = (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]`. Conclude with `mul_mem (hs c hc) (ht c hc)`.
-/
theorem mul_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact mul_mem (hs c hc) (ht c hc)

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
The claim follows from `| 0 => by rw [pow_zero]; exact one_mem_chartLat y a | j + 1 => by rw [pow_succ]; exact mul_mem_chartLat (pow_mem_chartLat hw j) hw`.
-/
theorem pow_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {w : Ω} (hw : w ∈ chartLat y a 1) :
    ∀ j : ℕ, w ^ j ∈ chartLat y a j
  | 0 => by rw [pow_zero]; exact one_mem_chartLat y a
  | j + 1 => by rw [pow_succ]; exact mul_mem_chartLat (pow_mem_chartLat hw j) hw

/- English proof (translation)
Introduce `dg dh g h z hg hh hdeg he hz`. Establish `hd : dg = dh` using `funext fun k => by simpa using hdeg k`. Substitute `hd` using the available equality. Establish `hmem` using `mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_sub hg hh) (by rw [map_sub, he, one_mul, sub_self])`. Establish `hz0` using `hz.2 _ hmem`.

Simplify using `only [map_sub] at hz0`. Rewrite `hz0` using `[sub_eq_zero]`. Rewrite using `[hz0, pow_zero, mul_one]`.
-/
theorem isSmallH_one (y : (Σ k, ι k) → Ω) (A : HermLine ι) : IsSmallH (mCoordIdeal y) y A 0 1 := by
  intro dg dh g h z hg hh hdeg he hz
  have hd : dg = dh := funext fun k => by simpa using hdeg k
  subst hd
  have hmem := mem_mCoordIdeal_of_aeval_eq_zero y (isMultiHomog_sub hg hh) (by rw [map_sub, he, one_mul, sub_self])
  have hz0 := hz.2 _ hmem
  simp only [map_sub] at hz0
  rw [sub_eq_zero] at hz0
  rw [hz0, pow_zero, mul_one]

/- English proof (translation)
Introduce `dg dh g h z hg hh hdeg he hz`. Use `choose c hc using hz.1`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k h0 => by`. Establish `hz0` using `hz.2 _ (X_mem_mCoordIdeal y ⟨k, c k⟩ h0)`. Simplify using `only [map_X, eval_X] at hz0`.

Conclude with `hc k hz0`. Take `⟨N, dgs, gs, hgs, hdgs, hvs⟩` from `exists_chartForm y A.a n hs c hy`. Take `⟨M, dgt, gt, hgt, hdgt, hvt⟩` from `exists_chartForm y A.a m ht c hy`. Establish `bs` using `hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz`. Establish `bt` using `hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz`.

Establish `hdeq : dgs + dgt + dh = dg + (N + M)`. Use function extensionality and compare the values at `k`. Establish `e1` using `hdgs k`. Establish `e2` using `hdgt k`. Establish `e3` using `hdeg k`.

Simplify using `only [Pi.add_apply]`. Establish `: ((dgs k + dgt k + dh k : ℕ) : ℤ) = ((dg k + (N k + M k) : ℕ) : ℤ)`. Move the coercions through the operations in `at e3 ⊢`. Take the linear combination `e1 + e2 - e3`. Conclude with `this` after adjusting the coercions.

Establish `hF : IsMultiHomog (gs * gt * h - g * chartMono c (N + M)) (dgs + dgt + dh)`. Use `isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs hgt) hh) ?_` and prove the remaining obligations. Rewrite using `[hdeq]`. Conclude with `isMultiHomog_mul hg (isMultiHomog_chartMono c (N + M))`. Establish `hmono : ∀ (w : (Σ k, ι k) → Ω), aeval w (chartMono c (N + M)) = aeval w (chartMono c N) * aeval w (chartMono c M)` using `fun w => by`.

Rewrite using `[aeval_chartMono, aeval_chartMono, aeval_chartMono, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`. Establish `hF0 : aeval y (gs * gt * h - g * chartMono c (N + M)) = 0`. Rewrite using `[map_sub, map_mul, map_mul, map_mul, hvs, hvt, he, hmono]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hz0` using `hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)`. Simplify using `only [map_sub, map_mul] at hz0`. Rewrite `hz0` using `[sub_eq_zero]`. Use `set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev`. Establish `hmz : ev (chartMono c (N + M)) = ev (chartMono c N) * ev (chartMono c M)`.

Simplify using `only [hev, eval_chartMono, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`. Establish `hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖`. Apply the tactic sequence `refine mul_pos (norm_pos_iff.mpr ?_) (norm_pos_iff.mpr ?_) <;>`. Simplify using `only [hev, eval_chartMono]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)`. Establish `key : ‖ev g‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) = ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖`. Rewrite using `[← norm_mul, ← hmz, ← norm_mul, ← norm_mul, ← norm_mul]`. Conclude with `congrArg norm hz0.symm`. Establish `hprod : ‖ev gs‖ * ‖ev gt‖ ≤ (‖ev (chartMono c N)‖ * A.h z ^ n) * (‖ev (chartMono c M)‖ * A.h z ^ m)` using `mul_le_mul bs bt (norm_nonneg _) ((norm_nonneg _).trans bs)`.

Use `le_of_mul_le_mul_right ?_ hpos` and prove the remaining obligations. Rewrite using `[key]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isSmallH_mul {y : (Σ k, ι k) → Ω} {A : HermLine ι} {n m : ℕ} {s t : Ω}
    (hs : s ∈ chartLat y A.a n) (ht : t ∈ chartLat y A.a m)
    (hbs : IsSmallH (mCoordIdeal y) y A n s) (hbt : IsSmallH (mCoordIdeal y) y A m t) :
    IsSmallH (mCoordIdeal y) y A (n + m) (s * t) := by
  intro dg dh g h z hg hh hdeg he hz
  choose c hc using hz.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    have hz0 := hz.2 _ (X_mem_mCoordIdeal y ⟨k, c k⟩ h0)
    simp only [map_X, eval_X] at hz0
    exact hc k hz0
  obtain ⟨N, dgs, gs, hgs, hdgs, hvs⟩ := exists_chartForm y A.a n hs c hy
  obtain ⟨M, dgt, gt, hgt, hdgt, hvt⟩ := exists_chartForm y A.a m ht c hy
  have bs := hbs dgs N gs (chartMono c N) z hgs (isMultiHomog_chartMono c N) hdgs hvs hz
  have bt := hbt dgt M gt (chartMono c M) z hgt (isMultiHomog_chartMono c M) hdgt hvt hz

  have hdeq : dgs + dgt + dh = dg + (N + M) := by
    funext k
    have e1 := hdgs k
    have e2 := hdgt k
    have e3 := hdeg k
    simp only [Pi.add_apply]
    have : ((dgs k + dgt k + dh k : ℕ) : ℤ) = ((dg k + (N k + M k) : ℕ) : ℤ) := by
      push_cast at e3 ⊢
      linear_combination e1 + e2 - e3
    exact_mod_cast this
  have hF : IsMultiHomog (gs * gt * h - g * chartMono c (N + M)) (dgs + dgt + dh) := by
    refine isMultiHomog_sub (isMultiHomog_mul (isMultiHomog_mul hgs hgt) hh) ?_
    rw [hdeq]
    exact isMultiHomog_mul hg (isMultiHomog_chartMono c (N + M))
  have hmono : ∀ (w : (Σ k, ι k) → Ω), aeval w (chartMono c (N + M)) =
      aeval w (chartMono c N) * aeval w (chartMono c M) := fun w => by
    rw [aeval_chartMono, aeval_chartMono, aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hF0 : aeval y (gs * gt * h - g * chartMono c (N + M)) = 0 := by
    rw [map_sub, map_mul, map_mul, map_mul, hvs, hvt, he, hmono]
    ring
  have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF hF0)
  simp only [map_sub, map_mul] at hz0
  rw [sub_eq_zero] at hz0

  set ev : MRing ι → ℂ := fun f => eval z (map (Int.castRingHom ℂ) f) with hev
  have hmz : ev (chartMono c (N + M)) = ev (chartMono c N) * ev (chartMono c M) := by
    simp only [hev, eval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hpos : 0 < ‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖ := by
    refine mul_pos (norm_pos_iff.mpr ?_) (norm_pos_iff.mpr ?_) <;>
    · simp only [hev, eval_chartMono]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have key : ‖ev g‖ * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) =
      ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖ := by
    rw [← norm_mul, ← hmz, ← norm_mul, ← norm_mul, ← norm_mul]
    exact congrArg norm hz0.symm
  have hprod : ‖ev gs‖ * ‖ev gt‖ ≤
      (‖ev (chartMono c N)‖ * A.h z ^ n) * (‖ev (chartMono c M)‖ * A.h z ^ m) :=
    mul_le_mul bs bt (norm_nonneg _) ((norm_nonneg _).trans bs)
  refine le_of_mul_le_mul_right ?_ hpos
  rw [key]
  calc ‖ev gs‖ * ‖ev gt‖ * ‖ev h‖
      ≤ (‖ev (chartMono c N)‖ * A.h z ^ n) * (‖ev (chartMono c M)‖ * A.h z ^ m) * ‖ev h‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ‖ev h‖ * A.h z ^ (n + m) * (‖ev (chartMono c N)‖ * ‖ev (chartMono c M)‖) := by
        rw [pow_add]
        ring

/- English proof (translation)
The claim follows from `| 0 => by rw [pow_zero]; exact isSmallH_one y A | j + 1 => by rw [pow_succ] exact isSmallH_mul (pow_mem_chartLat hw j) hw (isSmallH_pow hw hs j) hs`.
-/
theorem isSmallH_pow {y : (Σ k, ι k) → Ω} {A : HermLine ι} {w : Ω} (hw : w ∈ chartLat y A.a 1)
    (hs : IsSmallH (mCoordIdeal y) y A 1 w) : ∀ j : ℕ, IsSmallH (mCoordIdeal y) y A j (w ^ j)
  | 0 => by rw [pow_zero]; exact isSmallH_one y A
  | j + 1 => by
    rw [pow_succ]
    exact isSmallH_mul (pow_mem_chartLat hw j) hw (isSmallH_pow hw hs j) hs

end SmallSectionsNonzero

open SmallSectionsNonzero in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D A P0 har _ hA j`. Take `⟨q, w, hw, hgen, hsm⟩` from `hA.gen`. Use `choose c hc using har.2.1.2.2`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k h0 => hc k (X_mem_mCoordIdeal y ⟨k, c k⟩ h0)`. Take `⟨u, -, hsum⟩` from `hgen c hy`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, w i ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Simplify using `only [not_exists, not_not] at hne`. Simplify using `[hne] at hsum`. Conclude with `⟨w i ^ j, pow_mem_chartLat (hw i) j, pow_ne_zero j hi, isSmallH_pow (hw i) (hsm i) j⟩`.
-/
theorem SmallSectionsNonzero.proof : SmallSectionsNonzero.Statement := by
  intro K _ ι _ Ω _ y D A P0 har _ hA j
  obtain ⟨q, w, hw, hgen, hsm⟩ := hA.gen

  choose c hc using har.2.1.2.2
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (X_mem_mCoordIdeal y ⟨k, c k⟩ h0)

  obtain ⟨u, -, hsum⟩ := hgen c hy
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    simp [hne] at hsum
  exact ⟨w i ^ j, pow_mem_chartLat (hw i) j, pow_ne_zero j hi, isSmallH_pow (hw i) (hsm i) j⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
