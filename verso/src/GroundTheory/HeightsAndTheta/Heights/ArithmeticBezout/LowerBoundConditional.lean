import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowDegree
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def BaseChangeLogBound.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e δ : ℕ) (h : HermNorm n)
    (I : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → K)
    (σ : K →+* ℂ),
    IsProjPrime I → IsChowForm I (e + 1) f → IsMultiHomog δ f → linForm u ∉ I →
      cycleIntegral h (fundCycle (I.map (MvPolynomial.map σ))) e (fsLog h fun j => σ (u j)) ≤
        δ * Real.log (h.norm fun j => σ (u j))

/- English proof (translation)
Assemble the required witnesses or components as `⟨isProjPrime_point ℚ, isChowForm_point ℚ, isMultiHomog_point ℚ, linForm_one_not_mem_point ℚ⟩`.
-/
theorem BaseChangeLogBound.hypotheses_inhabited :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℚ) ∧
      linForm (fun _ => (1 : ℚ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ⟨isProjPrime_point ℚ, isChowForm_point ℚ, isMultiHomog_point ℚ, linForm_one_not_mem_point ℚ⟩

section Lemmas

variable {R : Type*} [CommRing R]

/- English proof (translation)
Rewrite using `[f.as_sum, map_sum]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `d hd`. Rewrite using `[bind₁_monomial]`. Establish `hw : Finsupp.weight w d = m` using `hf (mem_support_iff.mp hd)`.

Establish `h1 : IsWeightedHomogeneous w' (∏ x ∈ d.support, φ x ^ d x) (∑ x ∈ d.support, d x * w x)` using `IsWeightedHomogeneous.prod _ _ _ fun x _ => by`. Simplify `(hφ x).pow (d x)` using `[mul_comm]`. Establish `h2` using `h1.C_mul (coeff d f)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← hw, Finsupp.weight_apply, Finsupp.sum]`.

Simplify using `[smul_eq_mul]`.
-/
theorem IsWeightedHomogeneous.bind₁ {σ τ : Type*} {w : σ → ℕ} {w' : τ → ℕ} {f : MvPolynomial σ R}
    {m : ℕ} (hf : IsWeightedHomogeneous w f m) (φ : σ → MvPolynomial τ R)
    (hφ : ∀ x, IsWeightedHomogeneous w' (φ x) (w x)) :
    IsWeightedHomogeneous w' (bind₁ φ f) m := by
  classical
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro d hd
  rw [bind₁_monomial]
  have hw : Finsupp.weight w d = m := hf (mem_support_iff.mp hd)
  have h1 : IsWeightedHomogeneous w' (∏ x ∈ d.support, φ x ^ d x) (∑ x ∈ d.support, d x * w x) :=
    IsWeightedHomogeneous.prod _ _ _ fun x _ => by
      simpa [mul_comm] using (hφ x).pow (d x)
  have h2 := h1.C_mul (coeff d f)
  convert h2 using 1
  rw [← hw, Finsupp.weight_apply, Finsupp.sum]
  simp [smul_eq_mul]

variable {k n : ℕ}

/- English proof (translation)
Rewrite `hf`, the goal using `[isMultiHomog_iff]`. Introduce `i`. Use `IsWeightedHomogeneous.bind₁ (hf i.succ) _ fun x => ?_` and prove the remaining obligations. Take `⟨a, j⟩` from `x`. Proceed by induction on `a using Fin.cases with`.

Consider the case `zero`. Establish `: inGroup (n` using `n) i.succ ((0 : Fin (k + 1)), j) = 0 := by`. Simplify using `[inGroup, (Fin.succ_ne_zero i).symm]`. Rewrite using `[this]`. Conclude with `isWeightedHomogeneous_C _ _`.

Consider the case `succ a`. Establish `: inGroup (n` using `n) i.succ (a.succ, j) = inGroup (n := n) i (a, j) := by`. Simplify using `[inGroup, Fin.succ_inj]`. Rewrite using `[this]`. Conclude with `isWeightedHomogeneous_X R _ (a, j)`.
-/
theorem IsMultiHomog.specFirst {δ : ℕ} {f : MvPolynomial (Fin (k + 1) × Fin n) R}
    (hf : IsMultiHomog δ f) (u : Fin n → R) : IsMultiHomog δ (specFirst f u) := by
  rw [isMultiHomog_iff] at hf ⊢
  intro i
  refine IsWeightedHomogeneous.bind₁ (hf i.succ) _ fun x => ?_
  obtain ⟨a, j⟩ := x
  induction a using Fin.cases with
  | zero =>
    have : inGroup (n := n) i.succ ((0 : Fin (k + 1)), j) = 0 := by
      simp [inGroup, (Fin.succ_ne_zero i).symm]
    rw [this]
    exact isWeightedHomogeneous_C _ _
  | succ a =>
    have : inGroup (n := n) i.succ (a.succ, j) = inGroup (n := n) i (a, j) := by
      simp [inGroup, Fin.succ_inj]
    rw [this]
    exact isWeightedHomogeneous_X R _ (a, j)

/- English proof (translation)
Introduce `d hd`. Rewrite `hd` using `[coeff_map]`. Conclude with `hf fun h => hd (by rw [h, map_zero])`.
-/
theorem IsWeightedHomogeneous.map' {σ S : Type*} [CommSemiring S] {w : σ → ℕ} {f : MvPolynomial σ R}
    {m : ℕ} (hf : IsWeightedHomogeneous w f m) (φ : R →+* S) :
    IsWeightedHomogeneous w (MvPolynomial.map φ f) m := by
  intro d hd
  rw [coeff_map] at hd
  exact hf fun h => hd (by rw [h, map_zero])

end Lemmas

section Components

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i r hr`. Use `h r hr i` as an intermediate fact. Rewrite `this` using `[← decomposition.decompose'_apply]`. Then use the resulting hypothesis. Introduce `h f hf d`.

Conclude with `homogeneousComponent_mem_of_mem h hf d`.
-/
theorem isHomogIdeal_iff (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  constructor
  · intro h i r hr
    have := h r hr i
    rwa [← decomposition.decompose'_apply] at this
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d

/- English proof (translation)
Rewrite `hI`, the goal using `[isHomogIdeal_iff]`. Use `hI.sup (Ideal.homogeneous_span _ _ fun x hx => ?_)` and prove the remaining obligations. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Use `⟨1, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_homogeneousSubmodule]`. Conclude with `IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _`.
-/
theorem isHomogIdeal_sup_span_linForm {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsHomogIdeal I)
    (u : Fin n → R) : IsHomogIdeal (I ⊔ Ideal.span {linForm u}) := by
  rw [isHomogIdeal_iff] at hI ⊢
  refine hI.sup (Ideal.homogeneous_span _ _ fun x hx => ?_)
  rw [Set.mem_singleton_iff] at hx
  subst hx
  refine ⟨1, ?_⟩
  rw [mem_homogeneousSubmodule]
  exact IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _

variable [IsNoetherianRing R]

/- English proof (translation)
Establish `hval : (fundCycle J) W ≠ 0` using `Finsupp.mem_support_iff.mp hW`. Establish `hrel : W ∈ relComps J`. Assume the negation of the conclusion as `h`. Apply `hval` to reduce the goal to its premises. Unfold `fundCycle`.

Rewrite using `[Finsupp.onFinset_apply, if_neg h]`. Take `⟨hmin, hW'⟩` from `hrel`. Establish `hprime : W.IsPrime` using `hmin.1.1`. Establish `hJh` using `(isHomogIdeal_iff J).mp hJ`. Use `⟨hprime, (isHomogIdeal_iff W).mpr ?_, hW'⟩` and prove the remaining obligations.

Use `set core := (W.homogeneousCore (homogeneousSubmodule (Fin n) R)).toIdeal`. Establish `hcore_prime : core.IsPrime` using `hprime.homogeneousCore`. Establish `hJcore : J ≤ core`. Rewrite using `[← hJh.toIdeal_homogeneousCore_eq_self]`. Conclude with `Ideal.homogeneousCore_mono _ hmin.1.2`.

Establish `hle : core ≤ W` using `Ideal.toIdeal_homogeneousCore_le _ _`. Establish `heq : core = W` using `le_antisymm hle (hmin.2 ⟨hcore_prime, hJcore⟩ hle)`. Rewrite using `[Ideal.IsHomogeneous.iff_eq]`. Conclude with `heq`.
-/
theorem isProjPrime_of_mem_support_fundCycle {J : Ideal (MvPolynomial (Fin n) R)} (hJ : IsHomogIdeal J)
    {W : Ideal (MvPolynomial (Fin n) R)} (hW : W ∈ (fundCycle J).support) : IsProjPrime W := by
  classical
  have hval : (fundCycle J) W ≠ 0 := Finsupp.mem_support_iff.mp hW
  have hrel : W ∈ relComps J := by
    by_contra h
    apply hval
    unfold fundCycle
    rw [Finsupp.onFinset_apply, if_neg h]
  obtain ⟨hmin, hW'⟩ := hrel
  have hprime : W.IsPrime := hmin.1.1
  have hJh := (isHomogIdeal_iff J).mp hJ
  refine ⟨hprime, (isHomogIdeal_iff W).mpr ?_, hW'⟩
  set core := (W.homogeneousCore (homogeneousSubmodule (Fin n) R)).toIdeal
  have hcore_prime : core.IsPrime := hprime.homogeneousCore
  have hJcore : J ≤ core := by
    rw [← hJh.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hmin.1.2
  have hle : core ≤ W := Ideal.toIdeal_homogeneousCore_le _ _
  have heq : core = W := le_antisymm hle (hmin.2 ⟨hcore_prime, hJcore⟩ hle)
  rw [Ideal.IsHomogeneous.iff_eq]
  exact heq

/- English proof (translation)
The claim follows from `isProjPrime_of_mem_support_fundCycle (isHomogIdeal_sup_span_linForm hI.isHomog u) hW`.
-/
theorem isProjPrime_of_mem_support_divCycle {I : Ideal (MvPolynomial (Fin n) R)} (hI : IsProjPrime I)
    (u : Fin n → R) {W : Ideal (MvPolynomial (Fin n) R)} (hW : W ∈ (divCycle I u).support) :
    IsProjPrime W :=
  isProjPrime_of_mem_support_fundCycle (isHomogIdeal_sup_span_linForm hI.isHomog u) hW

end Components

section Height

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Simplify using `[chowHt]`.
-/
theorem chowHt_zero_groups (H : ArchData K n) (δ : ℕ) (g : MvPolynomial (Fin 0 × Fin n) K) :
    chowHt H 0 δ g = chowHt H 0 0 g := by
  simp [chowHt]

/- English proof (translation)
Rewrite using `[chowHt_zero_groups, eq_C_of_isEmpty g]`. Rewrite `hg` using `[eq_C_of_isEmpty g]`. Conclude with `chowHeightConst K n 0 H _ fun h => hg (by rw [h, map_zero])`.
-/
theorem chowHt_zero_groups_eq_zero (H : ArchData K n) (δ : ℕ) {g : MvPolynomial (Fin 0 × Fin n) K}
    (hg : g ≠ 0) : chowHt H 0 δ g = 0 := by
  rw [chowHt_zero_groups, eq_C_of_isEmpty g]
  rw [eq_C_of_isEmpty g] at hg
  exact chowHeightConst K n 0 H _ fun h => hg (by rw [h, map_zero])

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Rewrite using `[zero_mul, pow_zero, Nat.cast_zero, zero_mul, ← C_1]`. Conclude with `chowHeightConst K n k H 1 one_ne_zero`. Consider the case `succ m ih`.

Rewrite using `[pow_succ, Nat.succ_mul, hMul K n H k _ _ _ _ (pow_ne_zero _ hg) hg, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chowHt_pow (hMul : ChowHeightMul.Statement) (H : ArchData K n) {k : ℕ} (d : ℕ)
    {g : MvPolynomial (Fin k × Fin n) K} (hg : g ≠ 0) (m : ℕ) :
    chowHt H k (m * d) (g ^ m) = m * chowHt H k d g := by
  induction m with
  | zero =>
    rw [zero_mul, pow_zero, Nat.cast_zero, zero_mul, ← C_1]
    exact chowHeightConst K n k H 1 one_ne_zero
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul, hMul K n H k _ _ _ _ (pow_ne_zero _ hg) hg, ih]
    push_cast
    ring

/- English proof (translation)
Establish `hP : ∀ t ⊆ s, ∏ i ∈ t, g i ^ m i ≠ 0` using `fun t ht => Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hg i (ht hi))`. Establish `hprod : ∀ t ⊆ s, chowHt H k (∑ i ∈ t, m i * d i) (∏ i ∈ t, g i ^ m i) = ∑ i ∈ t, (m i : ℝ) * chowHt H k (d i) (g i)`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`.

Introduce `_`. Rewrite using `[Finset.sum_empty, Finset.prod_empty, Finset.sum_empty, ← C_1]`. Conclude with `chowHeightConst K n k H 1 one_ne_zero`. Consider the case `insert a t ha ih`. Introduce `hts`.

Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, hMul K n H k _ _ _ _ (pow_ne_zero _ (hg a (hts (Finset.mem_insert_self a t)))) (hP t (fun x hx => hts (Finset.mem_insert_of_mem hx))), chowHt_pow hMul H _ (hg a (hts (Finset.mem_insert_self a t))), ih (fun x hx = …`. Use `hMul K n H k 0 (∑ i ∈ s, m i * d i) (C c) _ (C_ne_zero.mpr hc) (hP s le_rfl)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Rewrite using `[this, chowHeightConst K n k H c hc, zero_add, hprod s le_rfl]`.
-/
theorem chowHt_C_mul_prod (hMul : ChowHeightMul.Statement) (H : ArchData K n) {k : ℕ} {ι : Type*}
    (s : Finset ι) (m d : ι → ℕ) (g : ι → MvPolynomial (Fin k × Fin n) K) (hg : ∀ i ∈ s, g i ≠ 0)
    {c : K} (hc : c ≠ 0) :
    chowHt H k (∑ i ∈ s, m i * d i) (C c * ∏ i ∈ s, g i ^ m i) =
      ∑ i ∈ s, (m i : ℝ) * chowHt H k (d i) (g i) := by
  classical
  have hP : ∀ t ⊆ s, ∏ i ∈ t, g i ^ m i ≠ 0 := fun t ht =>
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hg i (ht hi))
  have hprod : ∀ t ⊆ s, chowHt H k (∑ i ∈ t, m i * d i) (∏ i ∈ t, g i ^ m i) =
      ∑ i ∈ t, (m i : ℝ) * chowHt H k (d i) (g i) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.sum_empty, Finset.prod_empty, Finset.sum_empty, ← C_1]
      exact chowHeightConst K n k H 1 one_ne_zero
    | insert a t ha ih =>
      intro hts
      rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
        hMul K n H k _ _ _ _ (pow_ne_zero _ (hg a (hts (Finset.mem_insert_self a t))))
          (hP t (fun x hx => hts (Finset.mem_insert_of_mem hx))),
        chowHt_pow hMul H _ (hg a (hts (Finset.mem_insert_self a t))),
        ih (fun x hx => hts (Finset.mem_insert_of_mem hx))]
  have := hMul K n H k 0 (∑ i ∈ s, m i * d i) (C c) _ (C_ne_zero.mpr hc) (hP s le_rfl)
  rw [zero_add] at this
  rw [this, chowHeightConst K n k H c hc, zero_add, hprod s le_rfl]

open Matrix in
/- English proof (translation)
Unfold `HermNorm.norm`. Apply `Real.sqrt_pos.mpr` to reduce the goal to its premises. Establish `hAv : h.mat *ᵥ v ≠ 0`. Introduce `h0`. Apply `hv` to reduce the goal to its premises.

Use `congrArg (fun x => h.mat⁻¹ *ᵥ x) h0` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det, Matrix.one_mulVec, Matrix.mulVec_zero] at this`. Conclude with `this`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hAv`. Conclude with `Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩`.
-/
theorem HermNorm.norm_pos (h : HermNorm n) {v : Fin n → ℂ} (hv : v ≠ 0) : 0 < h.norm v := by
  unfold HermNorm.norm
  apply Real.sqrt_pos.mpr
  have hAv : h.mat *ᵥ v ≠ 0 := by
    intro h0
    apply hv
    have := congrArg (fun x => h.mat⁻¹ *ᵥ x) h0
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hAv
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩

/- English proof (translation)
Unfold `vertTerm vertTermAt`. Use `finsum_nonneg fun v => finsum_nonneg fun W => finsum_nonneg fun _ => ?_` and prove the remaining obligations. Conclude with `mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_natCast_nonneg _)`.
-/
theorem vertTerm_nonneg (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) (u : Fin n → 𝓞 K) :
    0 ≤ vertTerm I k u := by
  unfold vertTerm vertTermAt
  refine finsum_nonneg fun v => finsum_nonneg fun W => finsum_nonneg fun _ => ?_
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_natCast_nonneg _)

omit [NumberField K] in

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨j, hj⟩` from `hI`. Apply `hj` to reduce the goal to its premises. Establish `hmem : Pi.single j 1 ∈ Submodule.span (𝓞 K) S` using `by rw [hS]; trivial`.

Establish `key : ∀ v ∈ Submodule.span (𝓞 K) S, linForm (fun j => (v j : K)) ∈ I`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact hcon x hx`. Consider the case `zero => simp [linForm]`.

Consider the case `add x y _ _ hx hy`. Establish `: linForm (fun j => ((x + y) j : K)) = linForm (fun j => (x j : K)) + linForm (fun j => (y j : K))`. Simplify using `[linForm, Finset.sum_add_distrib, add_mul]`. Rewrite using `[this]`. Conclude with `I.add_mem hx hy`.

Consider the case `smul r x _ hx`. Establish `: linForm (fun j => ((r • x) j : K)) = C (r : K) * linForm (fun j => (x j : K))`. Simplify using `[linForm, Finset.mul_sum, mul_assoc]`. Rewrite using `[this]`. Conclude with `I.mul_mem_left _ hx`.

Use `key _ hmem` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `[linForm, Pi.single_apply]`.
-/
theorem exists_mem_linForm_not_mem {I : Ideal (MvPolynomial (Fin n) K)} (hI : IsRelevant I)
    {S : Set (Fin n → 𝓞 K)} (hS : Submodule.span (𝓞 K) S = ⊤) :
    ∃ s ∈ S, linForm (fun j => (s j : K)) ∉ I := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := hI
  apply hj
  have hmem : Pi.single j 1 ∈ Submodule.span (𝓞 K) S := by rw [hS]; trivial
  have key : ∀ v ∈ Submodule.span (𝓞 K) S, linForm (fun j => (v j : K)) ∈ I := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact hcon x hx
    | zero => simp [linForm]
    | add x y _ _ hx hy =>
      have : linForm (fun j => ((x + y) j : K)) = linForm (fun j => (x j : K)) + linForm (fun j => (y j : K)) := by
        simp [linForm, Finset.sum_add_distrib, add_mul]
      rw [this]
      exact I.add_mem hx hy
    | smul r x _ hx =>
      have : linForm (fun j => ((r • x) j : K)) = C (r : K) * linForm (fun j => (x j : K)) := by
        simp [linForm, Finset.mul_sum, mul_assoc]
      rw [this]
      exact I.mul_mem_left _ hx
  have := key _ hmem
  convert this using 1
  simp [linForm, Pi.single_apply]

end Height

open Classical in

/- English proof (translation)
Introduce `K _ _ n e₀ δ₀ H I₀ f₀ S Λ hI₀ hf₀ hδ₀ hspan hΛ`. Use `set L : ℝ := (1 / Module.finrank ℚ K : ℝ) * ∑ σ : K →+* ℂ, Real.log (Λ σ) with hL`. Establish `hd : (0 : ℝ) ≤ 1 / Module.finrank ℚ K` using `by positivity`. It suffices to establish `claim : ∀ k : ℕ, ∀ (I : Ideal (MvPolynomial (Fin n) K)) (g : MvPolynomial (Fin k × Fin n) K) (δ : ℕ), IsProjPrime I → IsChowForm I k g → IsMultiHomog δ g → -((k * δ : ℕ) : ℝ) * L ≤ chowHt H k δ g by`. Conclude with `claim (e₀ + 1) I₀ f₀ δ₀ hI₀ hf₀ hδ₀`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `I g δ _ hg _`. Rewrite using `[chowHt_zero_groups_eq_zero H δ hg.1]`.

Simplify using the standard rewrite rules. Consider the case `succ e ih`. Introduce `I f δ hI hf hδ`. Take `⟨s, hsS, hs⟩` from `exists_mem_linForm_not_mem hI.isRelevant hspan`. Establish `hrec` using `hR K n e δ H I f s hI hf hδ hs`.

Establish `hsec : -((e * δ : ℕ) : ℝ) * L ≤ chowHt H e δ (specFirst f fun j => (s j : K))`. Take `⟨c, hc, g, hg, heq⟩` from `hS K n e I f (fun j => (s j : K)) hI hf hs`. Establish `hne : specFirst f (fun j => (s j : K)) ≠ 0`. Rewrite using `[heq]`. Conclude with `mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)`.

Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases. Substitute `he` using the available equality. Rewrite using `[chowHt_zero_groups_eq_zero H δ hne]`. Simplify using the standard rewrite rules. Establish `hδs` using `hδ.specFirst (fun j => (s j : K))`.

Rewrite `hδs`, `hne` using `[heq]`. Take `⟨δW, hδW, hsum⟩` from `exists_degrees_of_chowFormCycle he _ c g hg hδs hne`. Rewrite using `[heq, ← hsum, chowHt_C_mul_prod hMul H _ _ _ _ (fun W hW => (hg W hW).1) hc]`. Establish `hprime : ∀ W ∈ (divCycle I fun j => (s j : K)).support, IsProjPrime W`. Introduce `W hW`.

Conclude with `isProjPrime_of_mem_support_divCycle hI _ hW`. Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Rewrite using `[Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := Finset.sum_le_sum fun W hW => mul_le_mul_of_nonneg_left (ih W (g W) (δW W) (hprime W hW) (hg W hW) (hδW W hW)) (Nat.cast_nonneg _)`. Establish `harch : ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e (fsLog (H.normAt σ) fun j => σ (s j)) ≤ δ * ∑ σ : K →+* ℂ, Real.log (Λ σ)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun σ _ => ?_` and prove the remaining obligations.

Use `(hB K n e δ (H.normAt σ) I f (fun j => (s j : K)) σ hI hf hδ hs).trans ?_` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)` to reduce the goal to its premises. Establish `hne : (fun j => σ (s j : K)) ≠ 0`. Introduce `h0`. Apply `hs` to reduce the goal to its premises.

Establish `: (fun j => (s j : K)) = 0` using `funext fun j => σ.injective (by simpa using congrFun h0 j)`. Rewrite using `[this]`. Simplify using `[linForm]`. Conclude with `Real.log_le_log (HermNorm.norm_pos _ hne) (hΛ s hsS σ)`. Establish `hvert` using `vertTerm_nonneg I (e + 1) s`.

Rewrite using `[hrec]`. Establish `: -(((e + 1) * δ : ℕ) : ℝ) * L = -((e * δ : ℕ) : ℝ) * L + (1 / Module.finrank ℚ K : ℝ) * (0 - δ * ∑ σ : K →+* ℂ, Real.log (Λ σ))`. Rewrite using `[hL]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Use `gcongr`.
-/
theorem chowHeightLowerBound_of (hR : ChowHeightRecursion.Statement) (hS : ChowFormSection.Statement)
    (hB : BaseChangeLogBound.Statement) (hMul : ChowHeightMul.Statement) :
    ChowHeightLowerBound.Statement := by
  intro K _ _ n e₀ δ₀ H I₀ f₀ S Λ hI₀ hf₀ hδ₀ hspan hΛ
  set L : ℝ := (1 / Module.finrank ℚ K : ℝ) * ∑ σ : K →+* ℂ, Real.log (Λ σ) with hL
  have hd : (0 : ℝ) ≤ 1 / Module.finrank ℚ K := by positivity

  suffices claim : ∀ k : ℕ, ∀ (I : Ideal (MvPolynomial (Fin n) K)) (g : MvPolynomial (Fin k × Fin n) K)
      (δ : ℕ), IsProjPrime I → IsChowForm I k g → IsMultiHomog δ g → -((k * δ : ℕ) : ℝ) * L ≤ chowHt H k δ g by
    exact claim (e₀ + 1) I₀ f₀ δ₀ hI₀ hf₀ hδ₀
  intro k
  induction k with
  | zero =>
    intro I g δ _ hg _
    rw [chowHt_zero_groups_eq_zero H δ hg.1]
    simp
  | succ e ih =>
    intro I f δ hI hf hδ
    obtain ⟨s, hsS, hs⟩ := exists_mem_linForm_not_mem hI.isRelevant hspan
    have hrec := hR K n e δ H I f s hI hf hδ hs

    have hsec : -((e * δ : ℕ) : ℝ) * L ≤ chowHt H e δ (specFirst f fun j => (s j : K)) := by
      obtain ⟨c, hc, g, hg, heq⟩ := hS K n e I f (fun j => (s j : K)) hI hf hs
      have hne : specFirst f (fun j => (s j : K)) ≠ 0 := by
        rw [heq]
        exact mul_ne_zero (C_ne_zero.mpr hc) (Finset.prod_ne_zero_iff.mpr fun W hW =>
          pow_ne_zero _ (hg W hW).1)
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he
        rw [chowHt_zero_groups_eq_zero H δ hne]
        simp
      · have hδs := hδ.specFirst (fun j => (s j : K))
        rw [heq] at hδs hne
        obtain ⟨δW, hδW, hsum⟩ := exists_degrees_of_chowFormCycle he _ c g hg hδs hne
        rw [heq, ← hsum, chowHt_C_mul_prod hMul H _ _ _ _ (fun W hW => (hg W hW).1) hc]
        have hprime : ∀ W ∈ (divCycle I fun j => (s j : K)).support, IsProjPrime W := by
          intro W hW
          exact isProjPrime_of_mem_support_divCycle hI _ hW
        calc -(((e * ∑ W ∈ (divCycle I fun j => (s j : K)).support,
                (divCycle I fun j => (s j : K)) W * δW W : ℕ)) : ℝ) * L
            = ∑ W ∈ (divCycle I fun j => (s j : K)).support,
                ((divCycle I fun j => (s j : K)) W : ℝ) * (-((e * δW W : ℕ) : ℝ) * L) := by
              push_cast
              rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]
              refine Finset.sum_congr rfl fun W _ => ?_
              ring
          _ ≤ _ := Finset.sum_le_sum fun W hW =>
              mul_le_mul_of_nonneg_left (ih W (g W) (δW W) (hprime W hW) (hg W hW) (hδW W hW))
                (Nat.cast_nonneg _)

    have harch : ∑ σ : K →+* ℂ, cycleIntegral (H.normAt σ) (fundCycle (I.map (MvPolynomial.map σ))) e
        (fsLog (H.normAt σ) fun j => σ (s j)) ≤ δ * ∑ σ : K →+* ℂ, Real.log (Λ σ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun σ _ => ?_
      refine (hB K n e δ (H.normAt σ) I f (fun j => (s j : K)) σ hI hf hδ hs).trans ?_
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hne : (fun j => σ (s j : K)) ≠ 0 := by
        intro h0
        apply hs
        have : (fun j => (s j : K)) = 0 := funext fun j => σ.injective (by simpa using congrFun h0 j)
        rw [this]
        simp [linForm]
      exact Real.log_le_log (HermNorm.norm_pos _ hne) (hΛ s hsS σ)
    have hvert := vertTerm_nonneg I (e + 1) s
    rw [hrec]
    have : -(((e + 1) * δ : ℕ) : ℝ) * L = -((e * δ : ℕ) : ℝ) * L +
        (1 / Module.finrank ℚ K : ℝ) * (0 - δ * ∑ σ : K →+* ℂ, Real.log (Λ σ)) := by
      rw [hL]
      push_cast
      ring
    rw [this]
    gcongr

end

end GroundTheory.Heights₂.Heights
