import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace BlockAdjoinPrime

variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}

open Classical in

def killB (B : Set K) : MRing ι R →ₐ[R] MRing ι R :=
  aeval fun v => if v.1 ∈ B then 0 else X v

def varIdeal (B : Set K) : Ideal (MRing ι R) :=
  Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B ∧ p = X v}

/- English proof (translation)
Simplify using `[killB, hv]`.
-/
theorem killB_X_of_mem (B : Set K) {v : Σ k, ι k} (hv : v.1 ∈ B) :
    killB (R := R) B (X v) = 0 := by
  classical
  simp [killB, hv]

/- English proof (translation)
Simplify using `[killB, hv]`.
-/
theorem killB_X_of_not_mem (B : Set K) {v : Σ k, ι k} (hv : v.1 ∉ B) :
    killB (R := R) B (X v) = X v := by
  classical
  simp [killB, hv]

open Classical in
/- English proof (translation)
Rewrite using `[killB, aeval_monomial]`. Use `split_ifs with h`. Rewrite using `[monomial_eq, algebraMap_eq]`. Use `congr 1`. Use `Finsupp.prod_congr fun v hv => ?_` and prove the remaining obligations.

Rewrite using `[if_neg (h v hv)]`. Use `push Not at h`. Take `⟨v, hv, hB⟩` from `h`. Rewrite using `[Finsupp.prod, Finset.prod_eq_zero hv, mul_zero]`. Rewrite using `[if_pos hB, zero_pow (Finsupp.mem_support_iff.mp hv)]`.
-/
theorem killB_monomial (B : Set K) (d : (Σ k, ι k) →₀ ℕ) (a : R) :
    killB (R := R) B (monomial d a) =
      if ∀ v ∈ d.support, v.1 ∉ B then monomial d a else 0 := by
  rw [killB, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    rw [if_neg (h v hv)]
  · push Not at h
    obtain ⟨v, hv, hB⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero hv, mul_zero]
    rw [if_pos hB, zero_pow (Finsupp.mem_support_iff.mp hv)]

open Classical in
/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial e a`. Rewrite using `[killB_monomial]`. Distinguish the cases in `hed : e = d`. Apply the tactic sequence `subst hed split_ifs <;> simp`.

Apply the tactic sequence `split_ifs <;> simp [coeff_monomial, hed]`. Consider the case `add p q hp hq`. Rewrite using `[map_add, coeff_add, hp, hq]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coeff_killB (B : Set K) (p : MRing ι R) (d : (Σ k, ι k) →₀ ℕ) :
    coeff d (killB B p) = if ∀ v ∈ d.support, v.1 ∉ B then coeff d p else 0 := by
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
    rw [killB_monomial]
    by_cases hed : e = d
    · subst hed
      split_ifs <;> simp
    · split_ifs <;> simp [coeff_monomial, hed]
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq]
    split_ifs <;> simp

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq`. Rewrite using `[map_add, add_sub_add_comm]`. Conclude with `add_mem hp hq`.

Consider the case `mul_X p v hp`. Establish `e : p * X v - killB B (p * X v) = (p - killB B p) * X v + killB B p * (X v - killB B (X v))`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)` and prove the remaining obligations. Distinguish the cases in `hv : v.1 ∈ B`. Rewrite using `[killB_X_of_mem B hv, sub_zero]`. Conclude with `Ideal.subset_span ⟨v, hv, rfl⟩`. Rewrite using `[killB_X_of_not_mem B hv, sub_self]`.

Conclude with `zero_mem _`.
-/
theorem sub_killB_mem (B : Set K) (p : MRing ι R) : p - killB B p ∈ varIdeal (R := R) B := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact add_mem hp hq
  | mul_X p v hp =>
    have e : p * X v - killB B (p * X v) =
        (p - killB B p) * X v + killB B p * (X v - killB B (X v)) := by
      rw [map_mul]; ring
    rw [e]
    refine add_mem (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    by_cases hv : v.1 ∈ B
    · rw [killB_X_of_mem B hv, sub_zero]
      exact Ideal.subset_span ⟨v, hv, rfl⟩
    · rw [killB_X_of_not_mem B hv, sub_self]
      exact zero_mem _

variable [DecidableEq K]

/- English proof (translation)
Establish `hw : ∀ k, Finsupp.weight (blockWeight ι) d k = ∑ i ∈ d.support, d i * (Pi.single i.1 1 : K → ℕ) k`. Introduce `k`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Introduce `h v hv hB`. Establish `h0` using `h v.1 hB`. Rewrite `h0` using `[hw, Finset.sum_eq_zero_iff]`. Use `h0 v hv` as an intermediate fact. Simplify using `[Finsupp.mem_support_iff.mp hv] at this`.

Introduce `h k hk`. Rewrite using `[hw, Finset.sum_eq_zero_iff]`. Introduce `i hi`. Establish `hik : i.1 ≠ k` using `fun e => h i hi (e ▸ hk)`. Simplify using `[Ne.symm hik]`.
-/
theorem weight_eq_zero_iff (d : (Σ k, ι k) →₀ ℕ) (B : Set K) :
    (∀ k ∈ B, Finsupp.weight (blockWeight ι) d k = 0) ↔ ∀ v ∈ d.support, v.1 ∉ B := by
  have hw : ∀ k, Finsupp.weight (blockWeight ι) d k =
      ∑ i ∈ d.support, d i * (Pi.single i.1 1 : K → ℕ) k := by
    intro k
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    rfl
  constructor
  · intro h v hv hB
    have h0 := h v.1 hB
    rw [hw, Finset.sum_eq_zero_iff] at h0
    have := h0 v hv
    simp [Finsupp.mem_support_iff.mp hv] at this
  · intro h k hk
    rw [hw, Finset.sum_eq_zero_iff]
    intro i hi
    have hik : i.1 ≠ k := fun e => h i hi (e ▸ hk)
    simp [Ne.symm hik]

/- English proof (translation)
Set `M` to `(q.support.image (Finsupp.weight (blockWeight ι))).filter (fun m => ∀ k ∈ B, m k = 0)`. Establish `key : killB B q = ∑ m ∈ M, weightedHomogeneousComponent (blockWeight ι) m q`. Use extensionality with `d`. Rewrite using `[coeff_killB, coeff_sum]`. Repeatedly rewrite using `[coeff_weightedHomogeneousComponent]`.

Rewrite using `[Finset.sum_ite_eq]`. Distinguish the cases in `hd : coeff d q = 0`. Simplify using `[hd]`. Establish `hmem : d ∈ q.support` using `mem_support_iff.mpr hd`. Establish `hiff : Finsupp.weight (blockWeight ι) d ∈ M ↔ ∀ v ∈ d.support, v.1 ∉ B`.

Rewrite using `[← weight_eq_zero_iff]`. Simplify using `only [M, Finset.mem_filter, Finset.mem_image]`. Conclude with `⟨fun h => h.2, fun h => ⟨⟨d, hmem, rfl⟩, h⟩⟩`. Distinguish the cases in `hP : ∀ v ∈ d.support, v.1 ∉ B`. Rewrite using `[if_pos hP, if_pos (hiff.mpr hP)]`.

Rewrite using `[if_neg hP, if_neg (fun h => hP (hiff.mp h))]`. Rewrite using `[key]`. Conclude with `Q.sum_mem fun m _ => hQ q hq m`.
-/
theorem killB_mem {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K)
    {q : MRing ι R} (hq : q ∈ Q) : killB B q ∈ Q := by
  classical
  let M := (q.support.image (Finsupp.weight (blockWeight ι))).filter (fun m => ∀ k ∈ B, m k = 0)
  have key : killB B q = ∑ m ∈ M, weightedHomogeneousComponent (blockWeight ι) m q := by
    ext d
    rw [coeff_killB, coeff_sum]
    simp_rw [coeff_weightedHomogeneousComponent]
    rw [Finset.sum_ite_eq]
    by_cases hd : coeff d q = 0
    · simp [hd]
    · have hmem : d ∈ q.support := mem_support_iff.mpr hd
      have hiff : Finsupp.weight (blockWeight ι) d ∈ M ↔ ∀ v ∈ d.support, v.1 ∉ B := by
        rw [← weight_eq_zero_iff]
        simp only [M, Finset.mem_filter, Finset.mem_image]
        exact ⟨fun h => h.2, fun h => ⟨⟨d, hmem, rfl⟩, h⟩⟩
      by_cases hP : ∀ v ∈ d.support, v.1 ∉ B
      · rw [if_pos hP, if_pos (hiff.mpr hP)]
      · rw [if_neg hP, if_neg (fun h => hP (hiff.mp h))]
  rw [key]
  exact Q.sum_mem fun m _ => hQ q hq m

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le (fun q hq => killB_mem hQ B hq) ?_` and prove the remaining obligations. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `show killB B (X v) ∈ Q`.

Rewrite using `[killB_X_of_mem B hv]`. Conclude with `zero_mem _`. Introduce `p hp`. Establish `: p = killB B p + (p - killB B p)` using `by ring`. Rewrite using `[this]`.

Conclude with `add_mem (Ideal.mem_sup_left hp) (Ideal.mem_sup_right (sub_killB_mem B p))`.
-/
theorem sup_eq_comap {Q : Ideal (MRing ι R)} (hQ : IsMultiHomogIdeal Q) (B : Set K) :
    Q ⊔ varIdeal B = Q.comap (killB B) := by
  apply le_antisymm
  · refine sup_le (fun q hq => killB_mem hQ B hq) ?_
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨v, hv, rfl⟩
    show killB B (X v) ∈ Q
    rw [killB_X_of_mem B hv]
    exact zero_mem _
  · intro p hp
    have : p = killB B p + (p - killB B p) := by ring
    rw [this]
    exact add_mem (Ideal.mem_sup_left hp) (Ideal.mem_sup_right (sub_killB_mem B p))

/- English proof (translation)
Introduce `R _ K _ _ ι Q B hP hQ`. Establish `h` using `sup_eq_comap (R := R) hQ B`. Express the relevant statement in the definitionally equal form `(Q ⊔ varIdeal B).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B → (X v ∈ Q ⊔ varIdeal B ↔ X v ∈ Q)`. Rewrite using `[h]`. Use `⟨Ideal.IsPrime.comap (killB B) (hK := hP), fun v hv => ?_⟩` and prove the remaining obligations.

Rewrite using `[Ideal.mem_comap, killB_X_of_not_mem B hv]`.
-/
theorem proof : BlockAdjoinPrime.Statement := by
  intro R _ K _ _ ι Q B hP hQ
  have h := sup_eq_comap (R := R) hQ B
  change (Q ⊔ varIdeal B).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B → (X v ∈ Q ⊔ varIdeal B ↔ X v ∈ Q)
  rw [h]
  refine ⟨Ideal.IsPrime.comap (killB B) (hK := hP), fun v hv => ?_⟩
  rw [Ideal.mem_comap, killB_X_of_not_mem B hv]

end BlockAdjoinPrime

end

end GroundTheory.Heights₂.Heights.NumbersDVR
