import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace PFContracted

section Drop

variable {K : Type*} {ι : K → Type*} {F : Type*} [Field F]

/- English proof (translation)
Use `ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPQ) (Ideal.Quotient.factor_surjective hPQ) (r := Ideal.Quotient.mk P f) ?_ ?_` and prove the remaining obligations. Conclude with `mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])`. Rewrite using `[Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hfQ`.
-/
theorem ringKrullDim_add_one_le {P Q : Ideal (MRing ι F)} [P.IsPrime] (hPQ : P ≤ Q)
    {f : MRing ι F} (hfP : f ∉ P) (hfQ : f ∈ Q) :
    ringKrullDim (MRing ι F ⧸ Q) + 1 ≤ ringKrullDim (MRing ι F ⧸ P) := by
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPQ)
    (Ideal.Quotient.factor_surjective hPQ) (r := Ideal.Quotient.mk P f) ?_ ?_
  · exact mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem])
  · rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hfQ

/- English proof (translation)
Use `lt_of_le_of_lt (ringKrullDim_quotient_le Q) ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]`. Conclude with `WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)`.
-/
theorem ringKrullDim_lt_top [Finite K] [∀ k, Finite (ι k)] (Q : Ideal (MRing ι F)) :
    ringKrullDim (MRing ι F ⧸ Q) < ⊤ := by
  refine lt_of_le_of_lt (ringKrullDim_quotient_le Q) ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _)

end Drop

section Kill

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def killBlocks (T : Finset K) : MRing ι F →ₐ[F] MRing ι F :=
  aeval fun v => if v.1 ∈ T then 0 else X v

/- English proof (translation)
Simplify using `[killBlocks]`.
-/
theorem killBlocks_X (T : Finset K) (v : Σ k, ι k) :
    killBlocks (F := F) T (X v) = if v.1 ∈ T then 0 else X v := by
  simp [killBlocks]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[killBlocks_X]`.
-/
theorem killBlocks_empty : killBlocks (ι := ι) (F := F) (∅ : Finset K) = AlgHom.id F _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [killBlocks_X]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, killBlocks_X]`. Distinguish the cases in `hv : v.1 ∈ T`. Simplify using `[hv, h hv]`.

Simplify using `[hv, killBlocks_X]`.
-/
theorem killBlocks_comp {T T' : Finset K} (h : T ⊆ T') :
    (killBlocks (ι := ι) (F := F) T').comp (killBlocks T) = killBlocks T' := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, killBlocks_X]
  by_cases hv : v.1 ∈ T
  · simp [hv, h hv]
  · simp [hv, killBlocks_X]

/- English proof (translation)
Rewrite using `[killBlocks, aeval_monomial]`. Use `split_ifs with h`. Rewrite using `[monomial_eq, algebraMap_eq]`. Use `congr 1`. Conclude with `Finsupp.prod_congr fun v hv => by rw [if_neg (h v hv)]`.

Simplify using `only [not_forall, not_not] at h`. Take `⟨v, hv, hT⟩` from `h`. Use `mul_eq_zero_of_right _ (Finset.prod_eq_zero hv ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[if_pos hT, zero_pow (Finsupp.mem_support_iff.mp hv)]`.
-/
theorem killBlocks_monomial (T : Finset K) (d : (Σ k, ι k) →₀ ℕ) (c : F) :
    killBlocks T (monomial d c) =
      if ∀ v ∈ d.support, v.1 ∉ T then monomial d c else 0 := by
  rw [killBlocks, aeval_monomial]
  split_ifs with h
  · rw [monomial_eq, algebraMap_eq]
    congr 1
    exact Finsupp.prod_congr fun v hv => by rw [if_neg (h v hv)]
  · simp only [not_forall, not_not] at h
    obtain ⟨v, hv, hT⟩ := h
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hv ?_)
    dsimp only
    rw [if_pos hT, zero_pow (Finsupp.mem_support_iff.mp hv)]

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on' with`. Consider the case `monomial d' c`. Rewrite using `[killBlocks_monomial, apply_ite (coeff d), coeff_zero, coeff_monomial]`. Distinguish the cases in `hd : d' = d`. Substitute `hd` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[hd]`. Consider the case `add p q hp hq`. Rewrite using `[map_add, coeff_add, hp, hq, coeff_add]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coeff_killBlocks (T : Finset K) (q : MRing ι F) (d : (Σ k, ι k) →₀ ℕ) :
    coeff d (killBlocks T q) = if ∀ v ∈ d.support, v.1 ∉ T then coeff d q else 0 := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial d' c =>
    rw [killBlocks_monomial, apply_ite (coeff d), coeff_zero, coeff_monomial]
    by_cases hd : d' = d
    · subst hd
      simp
    · simp [hd]
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq, coeff_add]
    split_ifs <;> simp

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff]`. Use `forall₂_congr fun v hv => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, blockWeight, Pi.single_apply, mul_ite, mul_one, mul_zero]`. Use `Finsupp.mem_support_iff.mp hv` as an intermediate fact. Prove the components needed by the constructor for the conclusion.

Introduce `h hk`. Rewrite `h` using `[if_pos hk.symm]`. Conclude with `this h`. Introduce `h`. Rewrite using `[if_neg (fun hk => h hk.symm)]`.
-/
theorem weight_apply_eq_zero_iff (d : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) d k = 0 ↔ ∀ v ∈ d.support, v.1 ≠ k := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finset.sum_eq_zero_iff]
  refine forall₂_congr fun v hv => ?_
  simp only [Pi.smul_apply, smul_eq_mul, blockWeight, Pi.single_apply, mul_ite, mul_one, mul_zero]
  have := Finsupp.mem_support_iff.mp hv
  constructor
  · intro h hk
    rw [if_pos hk.symm] at h
    exact this h
  · intro h
    rw [if_neg (fun hk => h hk.symm)]

/- English proof (translation)
Use extensionality with `d`. Rewrite using `[coeff_killBlocks]`. Distinguish the cases in `hd : coeff d p = 0`. Apply the tactic sequence `split_ifs <;> simp [hd]`. Establish `hw : Finsupp.weight (blockWeight ι) d = b` using `hp hd`.

Establish `key : (∀ v ∈ d.support, v.1 ∉ T) ↔ ∀ k ∈ T, b k = 0`. Prove the components needed by the constructor for the conclusion. Introduce `h k hk`. Rewrite using `[← hw, weight_apply_eq_zero_iff]`. Introduce `v hv hvk`.

Conclude with `h v hv (hvk ▸ hk)`. Introduce `h v hv hvT`. Use `h v.1 hvT` as an intermediate fact. Rewrite `this` using `[← hw, weight_apply_eq_zero_iff]`. Conclude with `this v hv rfl`.

Distinguish the cases in `hb : ∀ k ∈ T, b k = 0`. Rewrite using `[if_pos (key.mpr hb), if_pos hb]`. Rewrite using `[if_neg (fun h => hb (key.mp h)), if_neg hb, coeff_zero]`.
-/
theorem killBlocks_of_isMultiHomog (T : Finset K) {p : MRing ι F} {b : K → ℕ}
    (hp : IsMultiHomog p b) : killBlocks T p = if ∀ k ∈ T, b k = 0 then p else 0 := by
  ext d
  rw [coeff_killBlocks]
  by_cases hd : coeff d p = 0
  · split_ifs <;> simp [hd]
  · have hw : Finsupp.weight (blockWeight ι) d = b := hp hd
    have key : (∀ v ∈ d.support, v.1 ∉ T) ↔ ∀ k ∈ T, b k = 0 := by
      constructor
      · intro h k hk
        rw [← hw, weight_apply_eq_zero_iff]
        intro v hv hvk
        exact h v hv (hvk ▸ hk)
      · intro h v hv hvT
        have := h v.1 hvT
        rw [← hw, weight_apply_eq_zero_iff] at this
        exact this v hv rfl
    by_cases hb : ∀ k ∈ T, b k = 0
    · rw [if_pos (key.mpr hb), if_pos hb]
    · rw [if_neg (fun h => hb (key.mp h)), if_neg hb, coeff_zero]

/- English proof (translation)
Rewrite using `[← sum_weightedHomogeneousComponent (blockWeight ι) q, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp q), map_sum]`. Use `Ideal.sum_mem _ fun b _ => ?_` and prove the remaining obligations. Rewrite using `[killBlocks_of_isMultiHomog T (weightedHomogeneousComponent_isWeightedHomogeneous b q)]`. Use `split_ifs`. Conclude with `hQ q hq b`.

Conclude with `Q.zero_mem`.
-/
theorem killBlocks_mem_of_isMultiHomogIdeal {Q : Ideal (MRing ι F)} (hQ : IsMultiHomogIdeal Q)
    (T : Finset K) {q : MRing ι F} (hq : q ∈ Q) : killBlocks T q ∈ Q := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) q,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp q), map_sum]
  refine Ideal.sum_mem _ fun b _ => ?_
  rw [killBlocks_of_isMultiHomog T (weightedHomogeneousComponent_isWeightedHomogeneous b q)]
  split_ifs
  · exact hQ q hq b
  · exact Q.zero_mem

def killIdeal (Q : Ideal (MRing ι F)) (T : Finset K) : Ideal (MRing ι F) :=
  Q.comap (killBlocks T)

/- English proof (translation)
Use `choose i hi using hrel`. Establish `hmono : ∀ {T T' : Finset K}, T ⊆ T' → killIdeal Q T ≤ killIdeal Q T'`. Introduce `T T' h q hq`. Express the relevant statement in the definitionally equal form `killBlocks T' q ∈ Q`. Rewrite using `[← killBlocks_comp h]`.

Conclude with `hQ T' _ hq`. Establish `hprime : ∀ T, (killIdeal Q T).IsPrime` using `fun T => Ideal.comap_isPrime _ _`. Establish `hchain : ∀ T : Finset K, ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ Q)`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`.

Consider the case `empty`. Establish `: killIdeal Q (∅ : Finset K) = Q`. Use extensionality with `q`. Simplify using `[killIdeal, killBlocks_empty]`. Rewrite using `[this, Finset.card_empty, Nat.cast_zero, add_zero]`.

Consider the case `insert k T hk ih`. Use `hprime T` as an intermediate fact. Establish `hstep` using `ringKrullDim_add_one_le (P := killIdeal Q T) (Q := killIdeal Q (insert k T)) (hmono (Finset.subset_insert k T)) (f := X ⟨k, i k⟩) (by`. Express the relevant statement in the definitionally equal form `killBlocks T (X ⟨k, i k⟩) ∉ Q`. Rewrite using `[killBlocks_X, if_neg hk]`.

Conclude with `hi k)`. Use the proof step `(by`. Express the relevant statement in the definitionally equal form `killBlocks (insert k T) (X ⟨k, i k⟩) ∈ Q`. Rewrite using `[killBlocks_X, if_pos (Finset.mem_insert_self k T)]`. Conclude with `Q.zero_mem)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, add_assoc, add_comm (1 : WithBot ℕ∞)]`. Use `_ ≤ ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) := by gcongr`. Use `_ ≤ _ := ih`. Use `hprime Finset.univ` as an intermediate fact.

Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := MRing ι F ⧸ killIdeal Q Finset.univ)`. Use `hchain Finset.univ` as an intermediate fact. Rewrite `this` using `[Finset.card_univ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_le_ringKrullDim [Fintype K] {Q : Ideal (MRing ι F)} [hQp : Q.IsPrime]
    (hQ : ∀ (T : Finset K) (q : MRing ι F), q ∈ Q → killBlocks T q ∈ Q) (hrel : IsRelevant Q) :
    (Fintype.card K : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ Q) := by
  choose i hi using hrel
  have hmono : ∀ {T T' : Finset K}, T ⊆ T' → killIdeal Q T ≤ killIdeal Q T' := by
    intro T T' h q hq
    change killBlocks T' q ∈ Q
    rw [← killBlocks_comp h]
    exact hQ T' _ hq
  have hprime : ∀ T, (killIdeal Q T).IsPrime := fun T => Ideal.comap_isPrime _ _
  have hchain : ∀ T : Finset K,
      ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) ≤
        ringKrullDim (MRing ι F ⧸ Q) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have : killIdeal Q (∅ : Finset K) = Q := by
        ext q
        simp [killIdeal, killBlocks_empty]
      rw [this, Finset.card_empty, Nat.cast_zero, add_zero]
    | insert k T hk ih =>
      have := hprime T
      have hstep := ringKrullDim_add_one_le (P := killIdeal Q T) (Q := killIdeal Q (insert k T))
        (hmono (Finset.subset_insert k T)) (f := X ⟨k, i k⟩)
        (by
          change killBlocks T (X ⟨k, i k⟩) ∉ Q
          rw [killBlocks_X, if_neg hk]
          exact hi k)
        (by
          change killBlocks (insert k T) (X ⟨k, i k⟩) ∈ Q
          rw [killBlocks_X, if_pos (Finset.mem_insert_self k T)]
          exact Q.zero_mem)
      calc ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + ((insert k T).card : WithBot ℕ∞)
          = (ringKrullDim (MRing ι F ⧸ killIdeal Q (insert k T)) + 1) + (T.card : WithBot ℕ∞) := by
            rw [Finset.card_insert_of_notMem hk, Nat.cast_add, Nat.cast_one, add_assoc,
              add_comm (1 : WithBot ℕ∞)]
        _ ≤ ringKrullDim (MRing ι F ⧸ killIdeal Q T) + (T.card : WithBot ℕ∞) := by gcongr
        _ ≤ _ := ih
  have := hprime Finset.univ
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MRing ι F ⧸ killIdeal Q Finset.univ)
  have := hchain Finset.univ
  rw [Finset.card_univ] at this
  calc (Fintype.card K : WithBot ℕ∞) = 0 + (Fintype.card K : WithBot ℕ∞) := (zero_add _).symm
    _ ≤ ringKrullDim (MRing ι F ⧸ killIdeal Q Finset.univ) + (Fintype.card K : WithBot ℕ∞) := by
        gcongr
    _ ≤ _ := this

end Kill

end PFContracted

end

end GroundTheory.Heights₂.Heights.FieldNumbers
