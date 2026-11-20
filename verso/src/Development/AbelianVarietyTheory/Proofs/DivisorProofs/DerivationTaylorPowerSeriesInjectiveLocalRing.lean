import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHomStatement
open IsLocalRing GlobalTheory.FormalOrigin MvPowerSeries

noncomputable section
namespace GlobalTheory.TaylorInj

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons i l ih`. Simplify using `only [List.foldr_cons, ih, List.count_cons]`. Distinguish the cases in `h : i = a`.

Substitute `h` using the available equality. Simplify using `[Function.iterate_succ_apply']`. Simplify using `[h]`.
-/
theorem foldr_ite {A : Type} {n : ℕ} (D : A → A) (a : Fin n) (f : A) (l : List (Fin n)) :
    l.foldr (fun i g => if i = a then D g else g) f = D^[l.count a] f := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons, ih, List.count_cons]
    by_cases h : i = a
    · subst h; simp [Function.iterate_succ_apply']
    · simp [h]

/- English proof (translation)
Establish `e : (fun i g => (ds i)^[Finsupp.single a 1 i] g) = (fun i g => if i = a then ds a g else g)`. Use function extensionality and compare the values at `i g`. Distinguish the cases in `h : i = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Finsupp.single_apply, Ne.symm h, h]`. Unfold `iterOp`. Rewrite using `[e, foldr_ite, List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange a)]`. Both sides reduce to the same expression.
-/
theorem iterOp_single {A : Type} {n : ℕ} (ds : Fin n → A → A) (a : Fin n) (f : A) :
    iterOp ds (Finsupp.single a 1) f = ds a f := by
  have e : (fun i g => (ds i)^[Finsupp.single a 1 i] g) = (fun i g => if i = a then ds a g else g) := by
    funext i g
    by_cases h : i = a
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h, h]
  unfold iterOp
  rw [e, foldr_ite, List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange a)]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_taylor {A B : Type} [CommRing A] [CommRing B] [Algebra ℚ B] {n : ℕ} (ev : A →+* B)
    (ds : Fin n → A → A) (f : A) (α : Fin n →₀ ℕ) :
    coeff α (taylor ev ds f) = (∏ i, ((α i).factorial : ℚ))⁻¹ • ev (iterOp ds α f) := rfl

/- English proof (translation)
Establish `hsum` using `h`. Rewrite `hsum` using `[Finsupp.degree_eq_sum]`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, D s ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Simplify using `[hc] at hsum`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `hle : ∀ t, t ≠ s → D s + D t ≤ 1` using `fun t ht => by`. Rewrite using `[← hsum, ← Finset.sum_pair (Ne.symm ht)]`. Conclude with `Finset.sum_le_sum_of_subset (Finset.subset_univ _)`.

Use extensionality with `t`. Distinguish the cases in `ht : t = s`. Substitute `ht` using the available equality. Establish `: D t ≤ 1` using `h ▸ Finsupp.le_degree t D`. Simplify using `only [Finsupp.single_eq_same]`.

Use linear arithmetic over natural numbers and integers. Use `hle t ht` as an intermediate fact. Simplify using `only [Finsupp.single_apply, if_neg (Ne.symm ht)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem degree_eq_one {n : ℕ} {D : Fin n →₀ ℕ} (h : D.degree = 1) : ∃ s, D = Finsupp.single s 1 := by
  have hsum := h
  rw [Finsupp.degree_eq_sum] at hsum
  obtain ⟨s, hs⟩ : ∃ s, D s ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at hsum
  refine ⟨s, ?_⟩
  have hle : ∀ t, t ≠ s → D s + D t ≤ 1 := fun t ht => by
    rw [← hsum, ← Finset.sum_pair (Ne.symm ht)]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  ext t
  by_cases ht : t = s
  · subst ht
    have : D t ≤ 1 := h ▸ Finsupp.le_degree t D
    simp only [Finsupp.single_eq_same]
    omega
  · have := hle t ht
    simp only [Finsupp.single_apply, if_neg (Ne.symm ht)]
    omega

section Rel
variable {σ S : Type} [CommRing S]

def Rel (e : ℕ) (F G : MvPowerSeries σ S) : Prop :=
  (e : ℕ∞) ≤ G.order ∧ ((e + 1 : ℕ) : ℕ∞) ≤ (F - G).order

/- English proof (translation)
Establish `: F = G + (F - G)` using `by ring`. Rewrite using `[this]`. Conclude with `le_trans (le_min h.1 (le_trans (by exact_mod_cast Nat.le_succ e) h.2)) min_order_le_add`.
-/
theorem le_order_of_rel {e : ℕ} {F G : MvPowerSeries σ S} (h : Rel e F G) : (e : ℕ∞) ≤ F.order := by
  have : F = G + (F - G) := by ring
  rw [this]
  exact le_trans (le_min h.1 (le_trans (by exact_mod_cast Nat.le_succ e) h.2)) min_order_le_add

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `le_trans ?_ le_order_mul push_cast` and prove the remaining obligations. Conclude with `add_le_add h.1 h'.1`. Establish `e : F * F' - G * G' = (F - G) * F' + G * (F' - G')` using `by ring`. Rewrite using `[e]`.

Use `le_trans (le_min ?_ ?_) min_order_le_add` and prove the remaining obligations. Use `le_trans ?_ le_order_mul` and prove the remaining obligations. Use `le_trans (le_of_eq ?_) (add_le_add h.2 (le_order_of_rel h'))` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `le_trans ?_ le_order_mul` and prove the remaining obligations. Use `le_trans (le_of_eq ?_) (add_le_add h.1 h'.2)` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_mul {a b : ℕ} {F G F' G' : MvPowerSeries σ S} (h : Rel a F G) (h' : Rel b F' G') :
    Rel (a + b) (F * F') (G * G') := by
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ le_order_mul
    push_cast; exact add_le_add h.1 h'.1
  · have e : F * F' - G * G' = (F - G) * F' + G * (F' - G') := by ring
    rw [e]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h.2 (le_order_of_rel h'))
      push_cast; ring
    · refine le_trans ?_ le_order_mul
      refine le_trans (le_of_eq ?_) (add_le_add h.1 h'.2)
      push_cast; ring

/- English proof (translation)
Use `⟨by simp, by simp⟩` and prove the remaining obligations.
-/
theorem rel_one : Rel 0 (1 : MvPowerSeries σ S) 1 := by
  refine ⟨by simp, by simp⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using (rel_one (σ := σ) (S := S))`. Consider the case `succ k ih`. Rewrite using `[pow_succ, pow_succ, Nat.mul_succ]`. Conclude with `rel_mul ih h`.
-/
theorem rel_pow {a : ℕ} {F G : MvPowerSeries σ S} (h : Rel a F G) (k : ℕ) :
    Rel (a * k) (F ^ k) (G ^ k) := by
  induction k with
  | zero => simpa using (rel_one (σ := σ) (S := S))
  | succ k ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ]
    exact rel_mul ih h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (rel_one (σ := σ) (S := S))`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]`. Use `rel_mul (rel_pow (h i) (β i)) ih` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem rel_prod_pow {ι : Type} (s : Finset ι) (F G : ι → MvPowerSeries σ S) (β : ι → ℕ)
    (h : ∀ i, Rel 1 (F i) (G i)) :
    Rel (∑ i ∈ s, β i) (∏ i ∈ s, F i ^ β i) (∏ i ∈ s, G i ^ β i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (rel_one (σ := σ) (S := S))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    have := rel_mul (rel_pow (h i) (β i)) ih
    rwa [one_mul] at this

end Rel

/- English proof (translation)
Use `set K := RingHom.ker ev`. Use `set J := Ideal.span (Set.range z)`. Use `set I := (maximalIdeal R).map inc`. Establish `hJK : J ≤ K` using `Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)`. Establish `key : ∀ y ∈ I, y - inc (ev y) ∈ I * K`.

Introduce `y hy`. Use `Submodule.span_induction (p := fun y _ => y - inc (ev y) ∈ I * K) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨r, -, rfl⟩`. Simplify using `[hev]`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Use `Ideal.add_mem _ hx hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `a x hx' hx`. Establish `e : a • x - inc (ev (a • x)) = (a - inc (ev a)) * x + inc (ev a) * (x - inc (ev x))`. Simplify using `only [smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hx)` and prove the remaining obligations. Rewrite using `[mul_comm (a - inc (ev a))]; exact Ideal.mul_mem_mul hx' (RingHom.mem_ker.2 (by simp [hev]))`. Establish `hle : K ≤ J ⊔ I • K`. Introduce `x hx`. Establish `hxm : x ∈ maximalIdeal A`.

Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Use `hu.map ev` as an intermediate fact. Rewrite `this` using `[RingHom.mem_ker.1 hx]`. Conclude with `not_isUnit_zero this`.

Rewrite `hxm` using `[hm, Submodule.mem_sup]`. Take `⟨y, hy, w, hw, rfl⟩` from `hxm`. Establish `hw0 : ev w = 0` using `hJK hw`. Establish `hy0 : ev y = 0`. Use `RingHom.mem_ker.1 hx` as an intermediate fact.

Rewrite `this` using `[map_add, hw0, add_zero]`. Then use the resulting hypothesis. Use `key y hy` as an intermediate fact. Rewrite `this` using `[hy0, map_zero, sub_zero]`. Rewrite using `[add_comm]`. Conclude with `Submodule.add_mem_sup hw this`.

Establish `hIj : I ≤ Ideal.jacobson ⊥`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hm]`. Conclude with `le_sup_left`. Conclude with `Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian K) hIj hle`.
-/
theorem ker_le_span {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R) (hev : ∀ r, ev (inc r) = r) {n : ℕ}
    (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hm : maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z)) :
    RingHom.ker ev ≤ Ideal.span (Set.range z) := by
  set K := RingHom.ker ev
  set J := Ideal.span (Set.range z)
  set I := (maximalIdeal R).map inc
  have hJK : J ≤ K := Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hz i)
  have key : ∀ y ∈ I, y - inc (ev y) ∈ I * K := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => y - inc (ev y) ∈ I * K) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨r, -, rfl⟩; simp [hev]
    · simp
    · intro x y _ _ hx hy
      have := Ideal.add_mem _ hx hy
      convert this using 1; simp only [map_add]; ring
    · intro a x hx' hx
      have e : a • x - inc (ev (a • x)) = (a - inc (ev a)) * x + inc (ev a) * (x - inc (ev x)) := by
        simp only [smul_eq_mul, map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hx)
      rw [mul_comm (a - inc (ev a))]; exact Ideal.mul_mem_mul hx' (RingHom.mem_ker.2 (by simp [hev]))
  have hle : K ≤ J ⊔ I • K := by
    intro x hx
    have hxm : x ∈ maximalIdeal A := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; intro hu
      have := hu.map ev; rw [RingHom.mem_ker.1 hx] at this; exact not_isUnit_zero this
    rw [hm, Submodule.mem_sup] at hxm
    obtain ⟨y, hy, w, hw, rfl⟩ := hxm
    have hw0 : ev w = 0 := hJK hw
    have hy0 : ev y = 0 := by
      have := RingHom.mem_ker.1 hx; rwa [map_add, hw0, add_zero] at this
    have := key y hy
    rw [hy0, map_zero, sub_zero] at this
    rw [add_comm]; exact Submodule.add_mem_sup hw this
  have hIj : I ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hm]; exact le_sup_left
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian K) hIj hle

end GlobalTheory.TaylorInj

namespace GlobalTheory.TaylorInj
section Main
variable {R A : Type} [CommRing R] [Algebra ℚ R] [CommRing A] {n : ℕ}

/- English proof (translation)
Use `⟨by simp, ?_⟩` and prove the remaining obligations. Establish `h0 : constantCoeff (T c) = ev c`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hT, coeff_taylor]`. Simplify using `[iterOp_zero]`. Rewrite using `[zero_add, Nat.cast_one, one_le_order_iff_constCoeff_eq_zero, map_sub, h0]`.

Simplify using the standard rewrite rules.
-/
theorem rel_const (ev : A →+* R) (ds : Fin n → A → A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev ds f) (c : A) : Rel 0 (T c) (C (ev c)) := by
  refine ⟨by simp, ?_⟩
  have h0 : constantCoeff (T c) = ev c := by
    rw [← coeff_zero_eq_constantCoeff_apply, hT, coeff_taylor]; simp [iterOp_zero]
  rw [zero_add, Nat.cast_one, one_le_order_iff_constCoeff_eq_zero, map_sub, h0]
  simp

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `one_le_order_iff_constCoeff_eq_zero.2 (by simp)`. Use `nat_le_order fun d hd2 => ?_` and prove the remaining obligations. Rewrite using `[map_sub, hT, coeff_taylor]`. Distinguish the cases in `h0 : d.degree = 0`.

Rewrite using `[(Finsupp.degree_eq_zero_iff d).1 h0]`. Simplify using `[iterOp_zero, hz]`. Take `⟨a, rfl⟩` from `degree_eq_one (by omega : d.degree = 1)`. Rewrite using `[iterOp_single, hd, coeff_X]`. Establish `hf : ∀ j, (((Finsupp.single a 1 : Fin n →₀ ℕ) j).factorial : ℚ) = 1`.

Apply the tactic sequence `intro j; rw [Finsupp.single_apply]; split_ifs <;> simp`. Simplify using `only [hf, Finset.prod_const_one, inv_one, one_smul]`. Distinguish the cases in `hai : a = i`. Substitute `hai` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hai, Finsupp.single_left_inj (one_ne_zero)]`.
-/
theorem rel_coord (ev : A →+* R) (ds : Fin n → Derivation ℤ A A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f) (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hd : ∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) (i : Fin n) :
    Rel 1 (T (z i)) (X i) := by
  refine ⟨?_, ?_⟩
  · exact one_le_order_iff_constCoeff_eq_zero.2 (by simp)
  · refine nat_le_order fun d hd2 => ?_
    rw [map_sub, hT, coeff_taylor]
    by_cases h0 : d.degree = 0
    · rw [(Finsupp.degree_eq_zero_iff d).1 h0]; simp [iterOp_zero, hz]
    · obtain ⟨a, rfl⟩ := degree_eq_one (by omega : d.degree = 1)
      rw [iterOp_single, hd, coeff_X]
      have hf : ∀ j, (((Finsupp.single a 1 : Fin n →₀ ℕ) j).factorial : ℚ) = 1 := by
        intro j; rw [Finsupp.single_apply]; split_ifs <;> simp
      simp only [hf, Finset.prod_const_one, inv_one, one_smul]
      by_cases hai : a = i
      · subst hai; simp
      · simp [hai, Finsupp.single_left_inj (one_ne_zero)]

/- English proof (translation)
Take `⟨p, hp, rfl⟩` from `(Ideal.mem_span_pow_iff_exists_isHomogeneous z f).1 hk`. Establish `hdeg : ∀ β ∈ p.support, β.degree = k`. Introduce `β hβ`. Use `hp (MvPolynomial.mem_support_iff.1 hβ)` as an intermediate fact. Rewrite using `[Finsupp.degree_eq_weight_one]`.

Conclude with `this`. Establish `hev : MvPolynomial.eval z p = ∑ β ∈ p.support, p.coeff β * ∏ i, z i ^ β i` using `MvPolynomial.eval_eq' z p`. Establish `hmon : ∀ (β : Fin n →₀ ℕ) (c : R), C c * ∏ i, (X i : MvPowerSeries (Fin n) R) ^ β i = monomial β c`. Introduce `β c`. Simplify using `only [X_pow_eq]`.

Rewrite using `[prod_monomial, ← monomial_zero_eq_C_apply, monomial_mul_monomial]`. Simplify using `[Finsupp.univ_sum_single]`. Use `set G : MvPowerSeries (Fin n) R := ∑ β ∈ p.support, monomial β (ev (p.coeff β)) with hGdef`. Establish `hrel : ∀ β ∈ p.support, Rel k (T (p.coeff β * ∏ i, z i ^ β i)) (monomial β (ev (p.coeff β)))`. Introduce `β hβ`.

Establish `h` using `rel_mul (rel_const ev _ T hT (p.coeff β)) (rel_prod_pow Finset.univ (fun i => T (z i)) X (fun i => β i) (rel_coord ev ds T hT z hz hd))`. Rewrite `h` using `[zero_add, ← Finsupp.degree_eq_sum, hdeg β hβ, hmon]`. Rewrite using `[map_mul, map_prod]`. Simplify using `only [map_pow]`. Conclude with `h`.

Establish `hcoef : ∀ α : Fin n →₀ ℕ, α.degree = k → coeff α (T (MvPolynomial.eval z p)) = coeff α G`. Introduce `α hα`. Rewrite using `[← sub_eq_zero, ← map_sub, hev, map_sum, hGdef, ← Finset.sum_sub_distrib, map_sum]`. Use `Finset.sum_eq_zero fun β hβ => coeff_of_lt_order ?_` and prove the remaining obligations. Conclude with `lt_of_lt_of_le (by rw [hα]; exact_mod_cast Nat.lt_succ_self k) (hrel β hβ).2`.

Establish `hG : ∀ α, coeff α G = ev (p.coeff α)`. Introduce `α`. Simplify using `only [hGdef, map_sum, coeff_monomial, Finset.sum_ite_eq]`. Use `split_ifs with h`. Both sides reduce to the same expression.

Rewrite `h` using `[MvPolynomial.mem_support_iff, not_not]`. Rewrite using `[h, map_zero]`. Rewrite using `[hev]`. Use `Ideal.sum_mem _ fun β hβ => ?_` and prove the remaining obligations. Rewrite using `[pow_succ']`.

Use `Ideal.mul_mem_mul (hker (RingHom.mem_ker.2 ?_)) ?_` and prove the remaining obligations. Rewrite using `[← hG, ← hcoef β (hdeg β hβ), hf, map_zero]`. Rewrite using `[← hdeg β hβ, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]`. Conclude with `Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _`.
-/
theorem step (ev : A →+* R) (ds : Fin n → Derivation ℤ A A) (T : A →+* MvPowerSeries (Fin n) R)
    (hT : ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f) (z : Fin n → A) (hz : ∀ i, ev (z i) = 0)
    (hd : ∀ a i, ev (ds a (z i)) = if a = i then 1 else 0)
    (hker : RingHom.ker ev ≤ Ideal.span (Set.range z)) (k : ℕ) (f : A) (hf : T f = 0)
    (hk : f ∈ Ideal.span (Set.range z) ^ k) : f ∈ Ideal.span (Set.range z) ^ (k + 1) := by
  classical
  obtain ⟨p, hp, rfl⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous z f).1 hk
  have hdeg : ∀ β ∈ p.support, β.degree = k := by
    intro β hβ
    have := hp (MvPolynomial.mem_support_iff.1 hβ)
    rw [Finsupp.degree_eq_weight_one]; exact this
  have hev : MvPolynomial.eval z p = ∑ β ∈ p.support, p.coeff β * ∏ i, z i ^ β i :=
    MvPolynomial.eval_eq' z p
  have hmon : ∀ (β : Fin n →₀ ℕ) (c : R), C c * ∏ i, (X i : MvPowerSeries (Fin n) R) ^ β i = monomial β c := by
    intro β c
    simp only [X_pow_eq]
    rw [prod_monomial, ← monomial_zero_eq_C_apply, monomial_mul_monomial]
    simp [Finsupp.univ_sum_single]
  set G : MvPowerSeries (Fin n) R := ∑ β ∈ p.support, monomial β (ev (p.coeff β)) with hGdef
  have hrel : ∀ β ∈ p.support,
      Rel k (T (p.coeff β * ∏ i, z i ^ β i)) (monomial β (ev (p.coeff β))) := by
    intro β hβ
    have h := rel_mul (rel_const ev _ T hT (p.coeff β))
      (rel_prod_pow Finset.univ (fun i => T (z i)) X (fun i => β i) (rel_coord ev ds T hT z hz hd))
    rw [zero_add, ← Finsupp.degree_eq_sum, hdeg β hβ, hmon] at h
    rw [map_mul, map_prod]; simp only [map_pow]; exact h
  have hcoef : ∀ α : Fin n →₀ ℕ, α.degree = k →
      coeff α (T (MvPolynomial.eval z p)) = coeff α G := by
    intro α hα
    rw [← sub_eq_zero, ← map_sub, hev, map_sum, hGdef, ← Finset.sum_sub_distrib, map_sum]
    refine Finset.sum_eq_zero fun β hβ => coeff_of_lt_order ?_
    exact lt_of_lt_of_le (by rw [hα]; exact_mod_cast Nat.lt_succ_self k) (hrel β hβ).2
  have hG : ∀ α, coeff α G = ev (p.coeff α) := by
    intro α
    simp only [hGdef, map_sum, coeff_monomial, Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · rw [MvPolynomial.mem_support_iff, not_not] at h; rw [h, map_zero]
  rw [hev]
  refine Ideal.sum_mem _ fun β hβ => ?_
  rw [pow_succ']
  refine Ideal.mul_mem_mul (hker (RingHom.mem_ker.2 ?_)) ?_
  · rw [← hG, ← hcoef β (hdeg β hβ), hf, map_zero]
  · rw [← hdeg β hβ, Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

end Main

/- English proof (translation)
Introduce `R A _ _ _ _ _ _ inc ev hev n ds z hz hd hm f hf`. Take `⟨T, hT⟩` from `GlobalTheory.T.exists_ringHom_eq_taylor A R n ev ds`. Establish `hker` using `ker_le_span inc ev hev z hz hm`. Establish `hTf : T f = 0` using `by rw [hT]; exact hf`. Establish `hall : ∀ k, f ∈ Ideal.span (Set.range z) ^ k`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => exact step ev ds T hT z hz hd hker k f hTf ih`. Establish `hne : Ideal.span (Set.range z) ≠ ⊤`.

Introduce `h`. Apply `(maximalIdeal.isMaximal A).ne_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff, hm, ← h]`. Conclude with `le_sup_right`. Use `Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne` as an intermediate fact.

Rewrite using `[← Ideal.mem_bot, ← this, Ideal.mem_iInf]`. Conclude with `hall`.
-/
theorem taylor_injective : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [Algebra ℚ R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (ds : Fin n → Derivation ℤ A A) (z : Fin n → A), (∀ i, ev (z i) = 0) → (∀ a i, ev (ds a (z i)) = if a = i then 1 else 0) → maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ f, taylor ev (fun i => ⇑(ds i)) f = 0 → f = 0 := by
  intro R A _ _ _ _ _ _ inc ev hev n ds z hz hd hm f hf
  obtain ⟨T, hT⟩ := GlobalTheory.T.exists_ringHom_eq_taylor A R n ev ds
  have hker := ker_le_span inc ev hev z hz hm
  have hTf : T f = 0 := by rw [hT]; exact hf
  have hall : ∀ k, f ∈ Ideal.span (Set.range z) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact step ev ds T hT z hz hd hker k f hTf ih
  have hne : Ideal.span (Set.range z) ≠ ⊤ := by
    intro h
    apply (maximalIdeal.isMaximal A).ne_top
    rw [eq_top_iff, hm, ← h]; exact le_sup_right
  have := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]; exact hall

end GlobalTheory.TaylorInj
