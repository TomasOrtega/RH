import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad
open scoped nonZeroDivisors Pointwise

namespace UpperTheory.IdealSupremumPower

/- English proof (translation)
Establish `hint : ∀ n : ℤ, w (n : K) ≤ 1` using `fun n => IsNonarchimedean.apply_intCast_le_one hw`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Take `⟨p, hp, hpr⟩` from `(RingOfIntegers.isIntegral_coe r)`. Use `set x : K := (r : K) with hx`.

Rewrite `hpr` using `[Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul]`. Establish `h1 : x ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ K (p.coeff i) * x ^ i`. Take the linear combination `hpr`. Establish `h2 : ∀ s : Finset ℕ, (∀ i ∈ s, i < p.natDegree) → w (∑ i ∈ s, algebraMap ℤ K (p.coeff i) * x ^ i) < w x ^ p.natDegree`. Introduce `s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _`. Simplify using the standard rewrite rules. Check the signs of the components of the expression. Consider the case `insert i s hi ih`.

Introduce `hs`. Rewrite using `[Finset.sum_insert hi]`. Use `lt_of_le_of_lt (hw _ _) (max_lt ?_ (ih fun j hj => hs j (Finset.mem_insert_of_mem hj)))` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Establish `h3` using `hint (p.coeff i)`.

Establish `h4 : w x ^ i < w x ^ p.natDegree` using `pow_lt_pow_right₀ h (hs i (Finset.mem_insert_self _ _))`. Establish `h5 : 0 ≤ w x ^ i` using `by positivity`. Simplify using `only [eq_intCast]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h6` using `h2 _ (fun i hi => Finset.mem_range.mp hi)`.

Rewrite `h6` using `[← w.map_neg, ← h1, map_pow]`. Conclude with `lt_irrefl _ h6`.
-/
private theorem w_le_one {K : Type} [Field K] [NumberField K] (w : AbsoluteValue K ℝ)
    (hw : IsNonarchimedean w) (r : 𝓞 K) : w (r : K) ≤ 1 := by
  have hint : ∀ n : ℤ, w (n : K) ≤ 1 := fun n => IsNonarchimedean.apply_intCast_le_one hw
  by_contra h
  push Not at h
  obtain ⟨p, hp, hpr⟩ := (RingOfIntegers.isIntegral_coe r)
  set x : K := (r : K) with hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hpr
  have h1 : x ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ K (p.coeff i) * x ^ i := by
    linear_combination hpr
  have h2 : ∀ s : Finset ℕ, (∀ i ∈ s, i < p.natDegree) →
      w (∑ i ∈ s, algebraMap ℤ K (p.coeff i) * x ^ i) < w x ^ p.natDegree := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp; positivity
    | insert i s hi ih =>
      intro hs
      rw [Finset.sum_insert hi]
      refine lt_of_le_of_lt (hw _ _) (max_lt ?_ (ih fun j hj => hs j (Finset.mem_insert_of_mem hj)))
      rw [map_mul, map_pow]
      have h3 := hint (p.coeff i)
      have h4 : w x ^ i < w x ^ p.natDegree := pow_lt_pow_right₀ h (hs i (Finset.mem_insert_self _ _))
      have h5 : 0 ≤ w x ^ i := by positivity
      simp only [eq_intCast]
      nlinarith
  have h6 := h2 _ (fun i hi => Finset.mem_range.mp hi)
  rw [← w.map_neg, ← h1, map_pow] at h6
  exact lt_irrefl _ h6

/- English proof (translation)
Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact hS x hx`. Consider the case `zero => simpa using ht`. Consider the case `add x y _ _ hx hy => exact (hw _ _).trans (max_le hx hy)`.

Consider the case `smul r x _ hx`. Rewrite using `[Algebra.smul_def, map_mul]`. Use `w_le_one w hw r` as an intermediate fact. Establish `h0` using `w.nonneg x`. Establish `h1 : w (algebraMap (𝓞 K) K r) ≤ 1` using `this`.

Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem span_le {K : Type} [Field K] [NumberField K] (w : AbsoluteValue K ℝ)
    (hw : IsNonarchimedean w) (S : Set K) (t : ℝ) (ht : 0 ≤ t) (hS : ∀ x ∈ S, w x ≤ t) :
    ∀ y ∈ Submodule.span (𝓞 K) S, w y ≤ t := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simpa using ht
  | add x y _ _ hx hy => exact (hw _ _).trans (max_le hx hy)
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul]
    have := w_le_one w hw r
    have h0 := w.nonneg x
    have h1 : w (algebraMap (𝓞 K) K r) ≤ 1 := this
    nlinarith

/- English proof (translation)
Take `⟨S, rfl⟩` from `hM`. Take `⟨x, hx, hmax⟩` from `(insert 0 S).exists_max_image (fun b => w b) (Finset.insert_nonempty _ _)`. Use `⟨x, ?_, span_le w hw _ _ (w.nonneg x) fun y hy => hmax y (Finset.mem_insert_of_mem hy)⟩` and prove the remaining obligations. Break down `Finset.mem_insert.mp hx with rfl | hx` into its components or cases. Conclude with `Submodule.zero_mem _`.

Conclude with `Submodule.subset_span hx`.
-/
private theorem exists_max {K : Type} [Field K] [NumberField K] (w : AbsoluteValue K ℝ)
    (hw : IsNonarchimedean w) (M : Submodule (𝓞 K) K) (hM : M.FG) :
    ∃ x ∈ M, ∀ y ∈ M, w y ≤ w x := by
  classical
  obtain ⟨S, rfl⟩ := hM
  obtain ⟨x, hx, hmax⟩ := (insert 0 S).exists_max_image (fun b => w b) (Finset.insert_nonempty _ _)
  refine ⟨x, ?_, span_le w hw _ _ (w.nonneg x) fun y hy => hmax y (Finset.mem_insert_of_mem hy)⟩
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact Submodule.zero_mem _
  · exact Submodule.subset_span hx

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using hM`. Consider the case `succ n ih`. Introduce `y hy`. Rewrite `hy` using `[pow_succ]`.

Use `Submodule.mul_induction_on hy ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Rewrite using `[map_mul, pow_succ]`. Conclude with `mul_le_mul (ih a ha) (hM b hb) (w.nonneg _) (by positivity)`. Introduce `a b ha hb`.

Conclude with `(hw _ _).trans (max_le ha hb)`.
-/
private theorem pow_le {K : Type} [Field K] (w : AbsoluteValue K ℝ)
    (hw : IsNonarchimedean w) (M : Submodule (𝓞 K) K) (t : ℝ) (ht : 0 ≤ t) (hM : ∀ y ∈ M, w y ≤ t)
    (n : ℕ) : ∀ y ∈ M ^ (n + 1), w y ≤ t ^ (n + 1) := by
  induction n with
  | zero => simpa using hM
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      rw [map_mul, pow_succ]
      exact mul_le_mul (ih a ha) (hM b hb) (w.nonneg _) (by positivity)
    · intro a b ha hb
      exact (hw _ _).trans (max_le ha hb)

/- English proof (translation)
Take `⟨x, hx, hmax⟩` from `exists_max w hw M hM`. Establish `hs : sSup ((fun b => w b) '' (M : Set K)) = w x`. Apply `IsGreatest.csSup_eq` to reduce the goal to its premises. Use `⟨⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `hmax y hy`. Rewrite using `[hs]`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← map_pow]`.

Use `span_le w hw {c} _ (w.nonneg c) (by simp) _ ?_` and prove the remaining obligations. Rewrite using `[← hc]`. Conclude with `Submodule.pow_mem_pow M hx _`. Use `pow_le w hw M _ (w.nonneg x) hmax m c ?_` and prove the remaining obligations. Rewrite using `[hc]`.

Conclude with `Submodule.mem_span_singleton_self c`.
-/
private theorem sup_pow {K : Type} [Field K] [NumberField K] (w : AbsoluteValue K ℝ)
    (hw : IsNonarchimedean w) (M : Submodule (𝓞 K) K) (hM : M.FG) (n : ℕ) (hn : 0 < n) (c : K)
    (hc : M ^ n = Submodule.span (𝓞 K) {c}) :
    sSup ((fun b => w b) '' (M : Set K)) ^ n = w c := by
  obtain ⟨x, hx, hmax⟩ := exists_max w hw M hM
  have hs : sSup ((fun b => w b) '' (M : Set K)) = w x := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax y hy
  rw [hs]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  apply le_antisymm
  · rw [← map_pow]
    refine span_le w hw {c} _ (w.nonneg c) (by simp) _ ?_
    rw [← hc]
    exact Submodule.pow_mem_pow M hx _
  · refine pow_le w hw M _ (w.nonneg x) hmax m c ?_
    rw [hc]
    exact Submodule.mem_span_singleton_self c

/- English proof (translation)
Establish `h` using `pow_card_eq_one (x := ClassGroup.mk K (Units.mk0 I hI))`. Rewrite `h` using `[← map_pow, ClassGroup.mk_eq_one_iff]`. Take `⟨c, hc⟩` from `h`. Establish `h2 : I ^ Fintype.card (ClassGroup (𝓞 K)) = FractionalIdeal.spanSingleton (𝓞 K)⁰ c`. Apply `FractionalIdeal.coeToSubmodule_injective` to reduce the goal to its premises.

Simplify using `using hc`. Use `⟨_, c, Fintype.card_pos, ?_, h2⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at h2`. Conclude with `hI h2`.
-/
private theorem exists_pow {K : Type} [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) : ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ I ^ n = FractionalIdeal.spanSingleton (𝓞 K)⁰ c := by
  have h := pow_card_eq_one (x := ClassGroup.mk K (Units.mk0 I hI))
  rw [← map_pow, ClassGroup.mk_eq_one_iff] at h
  obtain ⟨c, hc⟩ := h
  have h2 : I ^ Fintype.card (ClassGroup (𝓞 K)) = FractionalIdeal.spanSingleton (𝓞 K)⁰ c := by
    apply FractionalIdeal.coeToSubmodule_injective
    simpa using hc
  refine ⟨_, c, Fintype.card_pos, ?_, h2⟩
  rintro rfl
  simp at h2
  exact hI h2

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression.
-/
private theorem absNorm_idx {K : Type} [Field K] [NumberField K] (J : Ideal (𝓞 K)) :
    Ideal.absNorm J = J.toAddSubgroup.index := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

/- English proof (translation)
Use `set d := I.den with hd`. Establish `hd0 : algebraMap (𝓞 K) K d ≠ 0`. Simplify using `using nonZeroDivisors.coe_ne_zero d`. Establish `hI` using `FractionalIdeal.den_mul_self_eq_num I`. Set `J₀ : Ideal (𝓞 K)` to `Submodule.comap (Algebra.linearMap (𝓞 K) K) (d • (J : Submodule (𝓞 K) K))`.

Establish `hle : d • (J : Submodule (𝓞 K) K) ≤ d • (I : Submodule (𝓞 K) K)` using `Submodule.map_mono h`. Establish `hJ : d • (J : Submodule (𝓞 K) K) = Submodule.map (Algebra.linearMap (𝓞 K) K) J₀`. Use `(Submodule.map_comap_eq_self ?_).symm` and prove the remaining obligations. Use `hle.trans ?_` and prove the remaining obligations. Rewrite using `[hI]`.

Conclude with `LinearMap.map_le_range`. Establish `hJI : J₀ ≤ I.num`. Establish `: Submodule.map (Algebra.linearMap (𝓞 K) K) J₀ ≤ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num`. Rewrite using `[← hJ, ← hI]`. Conclude with `hle`.

Conclude with `(Submodule.map_le_map_iff_of_injective (IsFractionRing.injective (𝓞 K) K) _ _).mp this`. Establish `h1 : (J : Submodule (𝓞 K) K).toAddSubgroup.relIndex (I : Submodule (𝓞 K) K).toAddSubgroup = J₀.toAddSubgroup.relIndex I.num.toAddSubgroup`. Establish `e1` using `AddSubgroup.relIndex_map_map_of_injective (f := AddMonoidHom.mulLeft (algebraMap (𝓞 K) K d)) (J : Submodule (𝓞 K) K).toAddSubgroup (I : Submodule (𝓞 K) K).toAddSubgroup (mul_right_injective₀ hd0)`. Establish `e2` using `AddSubgroup.relIndex_map_map_of_injective (f := (algebraMap (𝓞 K) K).toAddMonoidHom) J₀.toAddSubgroup I.num.toAddSubgroup (IsFractionRing.injective (𝓞 K) K)`. Rewrite using `[← e1, ← e2]`.

Use `congr 1`. Conclude with `congrArg Submodule.toAddSubgroup hJ`. Conclude with `congrArg Submodule.toAddSubgroup hI`. Establish `h2` using `AddSubgroup.relIndex_mul_index (H := J₀.toAddSubgroup) (K := I.num.toAddSubgroup) hJI`. Rewrite using `[FractionalIdeal.absNorm_eq' d J₀ hJ, FractionalIdeal.absNorm_eq, h1, absNorm_idx, absNorm_idx, ← h2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem relIndex_mul {K : Type} [Field K] [NumberField K] (I J : FractionalIdeal (𝓞 K)⁰ K)
    (h : J ≤ I) :
    (((J : Submodule (𝓞 K) K).toAddSubgroup.relIndex (I : Submodule (𝓞 K) K).toAddSubgroup : ℕ) : ℚ)
      * FractionalIdeal.absNorm I = FractionalIdeal.absNorm J := by
  set d := I.den with hd
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 := by
    simpa using nonZeroDivisors.coe_ne_zero d
  have hI := FractionalIdeal.den_mul_self_eq_num I
  let J₀ : Ideal (𝓞 K) := Submodule.comap (Algebra.linearMap (𝓞 K) K) (d • (J : Submodule (𝓞 K) K))
  have hle : d • (J : Submodule (𝓞 K) K) ≤ d • (I : Submodule (𝓞 K) K) :=
    Submodule.map_mono h
  have hJ : d • (J : Submodule (𝓞 K) K) = Submodule.map (Algebra.linearMap (𝓞 K) K) J₀ := by
    refine (Submodule.map_comap_eq_self ?_).symm
    refine hle.trans ?_
    rw [hI]
    exact LinearMap.map_le_range
  have hJI : J₀ ≤ I.num := by
    have : Submodule.map (Algebra.linearMap (𝓞 K) K) J₀ ≤ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hJ, ← hI]; exact hle
    exact (Submodule.map_le_map_iff_of_injective (IsFractionRing.injective (𝓞 K) K) _ _).mp this
  have h1 : (J : Submodule (𝓞 K) K).toAddSubgroup.relIndex (I : Submodule (𝓞 K) K).toAddSubgroup
      = J₀.toAddSubgroup.relIndex I.num.toAddSubgroup := by
    have e1 := AddSubgroup.relIndex_map_map_of_injective
      (f := AddMonoidHom.mulLeft (algebraMap (𝓞 K) K d))
      (J : Submodule (𝓞 K) K).toAddSubgroup (I : Submodule (𝓞 K) K).toAddSubgroup
      (mul_right_injective₀ hd0)
    have e2 := AddSubgroup.relIndex_map_map_of_injective
      (f := (algebraMap (𝓞 K) K).toAddMonoidHom)
      J₀.toAddSubgroup I.num.toAddSubgroup (IsFractionRing.injective (𝓞 K) K)
    rw [← e1, ← e2]
    congr 1
    · exact congrArg Submodule.toAddSubgroup hJ
    · exact congrArg Submodule.toAddSubgroup hI
  have h2 := AddSubgroup.relIndex_mul_index (H := J₀.toAddSubgroup) (K := I.num.toAddSubgroup) hJI
  rw [FractionalIdeal.absNorm_eq' d J₀ hJ, FractionalIdeal.absNorm_eq, h1, absNorm_idx, absNorm_idx,
    ← h2]
  push_cast
  ring

/- English proof (translation)
Establish `h` using `congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)`. Simplify using `only [norm_prod, eq_ratCast, Complex.norm_ratCast] at h`. Rewrite using `[Rat.cast_abs, h, Real.log_prod (fun σ _ => by simpa using hx)]`. Conclude with `Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)`.
-/
private theorem sum_log {K : Type} [Field K] [NumberField K] (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ x‖ = Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have h := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod, eq_ratCast, Complex.norm_ratCast] at h
  rw [Rat.cast_abs, h, Real.log_prod (fun σ _ => by simpa using hx)]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)

end UpperTheory.IdealSupremumPower

open UpperTheory.IdealSupremumPower in
/- English proof (translation)
Introduce `K _ _ 𝔞 a hfg ha ha0`. Set `I : FractionalIdeal (𝓞 K)⁰ K` to `⟨𝔞, FractionalIdeal.isFractional_of_fg hfg⟩`. Establish `hIc : (I : Submodule (𝓞 K) K) = 𝔞` using `rfl`. Establish `haI : a ∈ I` using `ha`. Establish `hI : I ≠ 0`.

Introduce `h`. Rewrite `haI` using `[h]`. Conclude with `ha0 ((FractionalIdeal.mem_zero_iff _).mp haI)`. Take `⟨n, c, hn, hc, h⟩` from `exists_pow I hI`. Use `⟨n, c, hn, hc, fun w hw => sup_pow w hw 𝔞 hfg n hn c ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hIc, ← FractionalIdeal.coe_pow, h, FractionalIdeal.coe_spanSingleton]`. Establish `h1` using `relIndex_mul I (FractionalIdeal.spanSingleton (𝓞 K)⁰ a) (FractionalIdeal.spanSingleton_le_iff_mem.mpr haI)`. Rewrite `h1` using `[FractionalIdeal.coe_spanSingleton, hIc, FractionalIdeal.absNorm_span_singleton]`. Establish `h2` using `congrArg FractionalIdeal.absNorm h`. Rewrite `h2` using `[map_pow, FractionalIdeal.absNorm_span_singleton]`.

Establish `hN : FractionalIdeal.absNorm I ≠ 0` using `fun h => hI (FractionalIdeal.absNorm_eq_zero_iff.mp h)`. Establish `hNa : |Algebra.norm ℚ a| ≠ 0` using `by simpa [Algebra.norm_eq_zero_iff] using ha0`. Establish `hr : (((Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex 𝔞.toAddSubgroup : ℕ) : ℚ) ≠ 0`. Introduce `h0`. Rewrite `h1` using `[h0, zero_mul]`.

Conclude with `hNa h1.symm`. Rewrite using `[sum_log a ha0, sum_log c hc, ← h1, ← h2, Rat.cast_mul, Rat.cast_pow, Real.log_pow, Real.log_mul (by exact_mod_cast hr) (by exact_mod_cast hN), Rat.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ideal_norm_log_height :
    ∀ (K : Type) [Field K] [NumberField K] (𝔞 : Submodule (𝓞 K) K) (a : K), 𝔞.FG → a ∈ 𝔞 → a ≠ 0 → ∃ (n : ℕ) (c : K), 0 < n ∧ c ≠ 0 ∧ (∀ w : AbsoluteValue K ℝ, IsNonarchimedean w → sSup ((fun b => w b) '' (𝔞 : Set K)) ^ n = w c) ∧ (n : ℝ) * (Real.log ((Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex 𝔞.toAddSubgroup : ℝ) - ∑ σ : K →+* ℂ, Real.log ‖σ a‖) = -∑ σ : K →+* ℂ, Real.log ‖σ c‖ := by
  intro K _ _ 𝔞 a hfg ha ha0
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔞, FractionalIdeal.isFractional_of_fg hfg⟩
  have hIc : (I : Submodule (𝓞 K) K) = 𝔞 := rfl
  have haI : a ∈ I := ha
  have hI : I ≠ 0 := by
    intro h
    rw [h] at haI
    exact ha0 ((FractionalIdeal.mem_zero_iff _).mp haI)
  obtain ⟨n, c, hn, hc, h⟩ := exists_pow I hI
  refine ⟨n, c, hn, hc, fun w hw => sup_pow w hw 𝔞 hfg n hn c ?_, ?_⟩
  · rw [← hIc, ← FractionalIdeal.coe_pow, h, FractionalIdeal.coe_spanSingleton]
  · have h1 := relIndex_mul I (FractionalIdeal.spanSingleton (𝓞 K)⁰ a)
      (FractionalIdeal.spanSingleton_le_iff_mem.mpr haI)
    rw [FractionalIdeal.coe_spanSingleton, hIc, FractionalIdeal.absNorm_span_singleton] at h1
    have h2 := congrArg FractionalIdeal.absNorm h
    rw [map_pow, FractionalIdeal.absNorm_span_singleton] at h2
    have hN : FractionalIdeal.absNorm I ≠ 0 := fun h => hI (FractionalIdeal.absNorm_eq_zero_iff.mp h)
    have hNa : |Algebra.norm ℚ a| ≠ 0 := by simpa [Algebra.norm_eq_zero_iff] using ha0
    have hr : (((Submodule.span (𝓞 K) {a}).toAddSubgroup.relIndex 𝔞.toAddSubgroup : ℕ) : ℚ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h1
      exact hNa h1.symm
    rw [sum_log a ha0, sum_log c hc, ← h1, ← h2, Rat.cast_mul, Rat.cast_pow, Real.log_pow,
      Real.log_mul (by exact_mod_cast hr) (by exact_mod_cast hN), Rat.cast_natCast]
    ring
