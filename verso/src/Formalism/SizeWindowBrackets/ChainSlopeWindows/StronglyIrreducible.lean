import Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime
import Formalism.ThickAverageLoss.ThickAverageProofs.Balance

open Finset ArithmeticFunction

noncomputable section

namespace Formalism.LFunctionChainParameters.characterSumData

open Formalism Formalism.D5

namespace PB

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (authored)
There are exactly two residues modulo two. They are represented by zero and one.
-/
lemma zmod_two_cases_bis (e : ZMod 2) : e = 0 ∨ e = 1 := by
  revert e
  decide

/- English proof (authored)
The defining condition for the selected half of the group is that the first binary coordinate is zero.
-/
lemma inPhi_iff (g : E0 × H) : InPhi g ↔ g.1.1 = 0 := Iff.rfl

/- English proof (authored)
The first binary coordinate is either zero or one. Excluding zero is therefore equivalent to requiring one.
-/
lemma not_inPhi_iff (g : E0 × H) : ¬ InPhi g ↔ g.1.1 = 1 := by
  rw [inPhi_iff]
  rcases zmod_two_cases_bis g.1.1 with h | h <;> rw [h] <;> decide

/- English proof (authored)
Both first binary coordinates are zero, and the coordinate of the sum is their sum. Hence the sum belongs to the selected half.
-/
lemma inPhi_add {x y : E0 × H} (hx : InPhi x) (hy : InPhi y) : InPhi (x + y) := by
  rw [inPhi_iff] at hx hy ⊢
  simp [hx, hy]

/- English proof (authored)
The zero multiple lies in the selected half. If the n-th multiple lies there, adding the original element stays there by closure under addition. Induction gives the result.
-/
lemma inPhi_nsmul {x : E0 × H} (hx : InPhi x) (i : ℕ) : InPhi (i • x) := by
  induction i with
  | zero => rw [zero_smul]; exact (inPhi_iff _).2 rfl
  | succ n ih => rw [succ_nsmul]; exact inPhi_add ih hx

/- English proof (authored)
The top-place translation has zero first binary coordinate, so it preserves the first coordinate of each element. Membership in the complementary half is therefore unchanged.
-/
lemma filter_notPhi_eq (t : H) :
    (univ.filter (fun g : E0 × H => ¬ InPhi g)) = univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)) := by
  ext g
  simp [inPhi_iff, topPl]

/- English proof (authored)
The partner translation adds a top-place element with zero first coordinate and a conjugation element with first coordinate one. The resulting first coordinate is one plus the original coordinate.
-/
private theorem partner_fst_lemma (t : H) (g : E0 × H) : (partner t g).1.1 = 1 + g.1.1 := by
  simp [partner, cconj, topPl]

/- English proof (authored)
Subtracting the top-place element changes the first binary coordinate by zero. Subtracting the conjugation element changes it by minus one.
-/
private theorem sub_fst_lemma_2 (t : H) (ρ : E0 × H) : (ρ - topPl t - cconj).1.1 = ρ.1.1 - 1 := by
  simp [topPl, cconj]

/- English proof (authored)
The partner translation sends the complementary half to the selected half because it adds one to the first binary coordinate. Subtracting the two translating elements reverses the map and sends each selected element back to the complement. The maps are inverse, so reindexing the finite sum along them preserves its value.
-/
lemma sum_partner {β : Type*} [AddCommMonoid β] (t : H) (F : E0 × H → β) :
    ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), F (partner t g) = ∑ ρ ∈ PhiSet (H := H), F ρ := by
  refine Finset.sum_nbij' (partner t) (fun ρ => ρ - topPl t - cconj) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [PhiSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [inPhi_iff, partner_fst_lemma, (not_inPhi_iff a).1 ha]
    decide
  · intro a ha
    simp only [PhiSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [not_inPhi_iff, sub_fst_lemma_2, (inPhi_iff a).1 ha]
    decide
  · intro a _
    simp only [partner]
    abel
  · intro a _
    simp only [partner]
    abel
  · intro a _
    rfl

/- English proof (authored)
Apply the reindexing identity to the constant summand one. Each sum then counts its indexing half.
-/
lemma card_notPhi : (univ.filter (fun g : E0 × H => ¬ InPhi g)).card = (PhiSet (H := H)).card := by
  have h := sum_partner (H := H) (β := ℕ) 0 (fun _ => 1)
  simpa using h

/- English proof (authored)
A complex character of a finite group has values of modulus one. The value at the negative element is the reciprocal of the original value, which for modulus one is its complex conjugate.
-/
lemma conj_eq_neg (ψ : AddChar (E0 × H) ℂ) (g : E0 × H) : starRingEnd ℂ (ψ g) = ψ (-g) := by
  first
  | exact (AddChar.map_neg_eq_conj ψ g).symm
  | rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (AddChar.norm_apply ψ g)]

/- English proof (authored)
Replace the conjugated character value at g by the value at −g. Multiplicativity combines the two character values into the value at h − g. Character orthogonality gives the group cardinality at the zero element and zero otherwise. The difference is zero exactly when h = g.
-/
lemma ortho (g h : E0 × H) :
    ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ψ h
      = if h = g then (Fintype.card (E0 × H) : ℂ) else 0 := by
  simp_rw [conj_eq_neg, ← AddChar.map_add_eq_mul]
  rw [AddChar.sum_apply_eq_ite]
  simp only [neg_add_eq_sub, sub_eq_zero]

/- English proof (authored)
The sign character is defined by the first binary coordinate. It is one at coordinate zero and minus one at coordinate one.
-/
lemma chC_apply' (g : E0 × H) : (chC : AddChar (E0 × H) ℂ) g = if g.1.1 = 0 then 1 else -1 := rfl

/- English proof (authored)
Negation fixes each residue modulo two. The first coordinate therefore keeps the same sign character value.
-/
lemma chC_neg (g : E0 × H) : (chC : AddChar (E0 × H) ℂ) (-g) = chC g := by
  have h1 : (-g).1.1 = g.1.1 := by
    simp only [Prod.fst_neg]
    generalize g.1.1 = e
    revert e
    decide
  rw [chC_apply', chC_apply', h1]

/- English proof (authored)
Each sign value is either one or minus one. Its square is one in both cases.
-/
lemma chC_sq (g : E0 × H) : (chC : AddChar (E0 × H) ℂ) g * chC g = 1 := by
  rw [chC_apply']
  split_ifs <;> simp

/- English proof (authored)
The zero element in the additive character group is the trivial character, whose value at every input is one.
-/
private theorem zero_apply_lemma (g : E0 × H) : (0 : AddChar (E0 × H) ℂ) g = 1 := by
  first
  | exact AddChar.zero_apply g
  | rfl
  | simp

/- English proof (authored)
The product of the sign character with itself evaluates to the square of its sign at each element. That square is one, so the product is the trivial character.
-/
lemma chC_mul_self : (chC : AddChar (E0 × H) ℂ) * chC = 0 := by
  ext g
  rw [AddChar.mul_apply, chC_sq, zero_apply_lemma]

/- English proof (authored)
If the pointwise product is trivial, evaluate at any group element and multiply the resulting equality by the sign value there. Its square is one, so this makes the other character's value equal to the sign. Conversely the sign squared is the trivial character.
-/
lemma mul_chC_eq_zero_iff (ψ : AddChar (E0 × H) ℂ) : ψ * chC = 0 ↔ ψ = chC := by
  constructor
  · intro h
    ext g
    have h1 : ((ψ * chC : AddChar (E0 × H) ℂ)) g = (0 : AddChar (E0 × H) ℂ) g := by rw [h]
    rw [AddChar.mul_apply, zero_apply_lemma] at h1
    calc ψ g = ψ g * (chC g * chC g) := by rw [chC_sq, mul_one]
      _ = (ψ g * chC g) * chC g := by ring
      _ = chC g := by rw [h1, one_mul]
  · rintro rfl
    exact chC_mul_self

/- English proof (authored)
At the element with first coordinate one and all other coordinates zero, the sign value is minus one. The trivial character takes the value one there, so the two differ.
-/
lemma chC_ne_zero : (chC : AddChar (E0 × H) ℂ) ≠ 0 := by
  intro h
  have h1 : (chC : AddChar (E0 × H) ℂ) (((1, 0), 0) : E0 × H)
      = (0 : AddChar (E0 × H) ℂ) (((1, 0), 0) : E0 × H) := by rw [h]
  have h2 : ¬ ((((1, 0), 0) : E0 × H).1.1 = 0) := by
    show ¬ ((1 : ZMod 2) = 0)
    decide
  rw [chC_apply', if_neg h2, zero_apply_lemma] at h1
  norm_num at h1

/- English proof (authored)
The group identity has first coordinate zero and belongs to the selected half. Its cardinality is therefore nonzero, also after embedding in the complex numbers.
-/
lemma phi_card_ne_zero : ((PhiSet (H := H)).card : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  apply Finset.card_ne_zero.mpr
  exact ⟨0, by simp [PhiSet, inPhi_iff]⟩

/- English proof (authored)
The full group is partitioned into the selected half and its complement. The two subsets have equal cardinalities by the partner bijection, so the total is twice the selected cardinality.
-/
lemma card_G : (Fintype.card (E0 × H) : ℂ) = 2 * ((PhiSet (H := H)).card : ℂ) := by
  have hN : Fintype.card (E0 × H) = 2 * (PhiSet (H := H)).card := by
    first
    | rw [← Finset.card_univ, ← Finset.filter_card_add_filter_neg_card_eq_card (p := InPhi), card_notPhi]
    | rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not (p := InPhi), card_notPhi]
    simp only [PhiSet]
    ring
  exact_mod_cast hN

end
end PB

open PB

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (authored)
The partner map adds one to the first binary coordinate, sending the complement into the selected half. It is injective because it is translation by a fixed element. For a selected target, subtract the top-place and conjugation elements to produce its preimage. The first coordinate of that preimage is one, so it lies in the complement.
-/
theorem partner_bijection : PartnerBij (H := H) := by
  intro t
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    show InPhi (partner t g)
    rw [inPhi_iff, partner_fst_lemma, (not_inPhi_iff g).1 hg]
    decide
  · intro x _ y _ hxy
    simp only [partner] at hxy
    exact add_left_cancel (add_right_cancel hxy)
  · intro ρ hρ
    refine ⟨ρ - topPl t - cconj, ?_, ?_⟩
    · show ¬ InPhi (ρ - topPl t - cconj)
      rw [not_inPhi_iff, sub_fst_lemma_2, (inPhi_iff ρ).1 hρ]
      decide
    · simp only [partner]
      abel

/- English proof (authored)
The indicator of the complementary half is one half of one minus the sign character. Multiply it by the conjugated character value and sum over the group. Negation reindexes the sum, so orthogonality makes the untwisted sum vanish unless the character is trivial. The sign-twisted sum vanishes unless the product with the sign is trivial, which occurs exactly for the sign character itself. In the two exceptional cases the corresponding sum is the group cardinality. Divide their difference by two and use that this is twice the selected cardinality.
-/
theorem colour_sum : ColourSum (H := H) := by
  intro ψ
  have hneg : ∀ F : E0 × H → ℂ, ∑ g : E0 × H, F (-g) = ∑ g : E0 × H, F g :=
    fun F => Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
  have hind : ∀ g : E0 × H, (if ¬ InPhi g then (1 : ℂ) else 0) = (1 - chC g) / 2 := by
    intro g
    rw [chC_apply']
    by_cases h : g.1.1 = 0
    · rw [if_pos h, if_neg (show ¬¬InPhi g from not_not.2 h)]
      ring
    · rw [if_neg h, if_pos (show ¬InPhi g from h)]
      ring
  have e1 : ∀ g : E0 × H, (if ¬ InPhi g then starRingEnd ℂ (ψ g) else 0)
      = (starRingEnd ℂ (ψ g) - chC g * starRingEnd ℂ (ψ g)) / 2 := by
    intro g
    rw [← boole_mul, hind]
    ring
  have hA : ∑ g : E0 × H, starRingEnd ℂ (ψ g) = if ψ = 0 then (Fintype.card (E0 × H) : ℂ) else 0 := by
    simp_rw [conj_eq_neg]
    rw [hneg (⇑ψ), AddChar.sum_eq_ite]
  have hB : ∑ g : E0 × H, chC g * starRingEnd ℂ (ψ g)
      = if ψ = chC then (Fintype.card (E0 × H) : ℂ) else 0 := by
    have h4 : ∀ g : E0 × H, chC g * starRingEnd ℂ (ψ g) = ((ψ * chC : AddChar (E0 × H) ℂ)) (-g) := by
      intro g
      rw [AddChar.mul_apply, conj_eq_neg, ← chC_neg, mul_comm]
    simp_rw [h4]
    rw [hneg (⇑(ψ * chC : AddChar (E0 × H) ℂ)), AddChar.sum_eq_ite]
    simp only [mul_chC_eq_zero_iff]
  rw [Finset.sum_filter]
  simp_rw [e1]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hA, hB, card_G]
  have hne := chC_ne_zero (H := H)
  by_cases h0 : ψ = 0
  · have h1 : ¬ ψ = chC := fun h => hne (h ▸ h0)
    simp only [if_pos h0, if_neg h1]
    ring
  · by_cases h1 : ψ = chC
    · simp only [if_neg h0, if_pos h1]
      ring
    · simp only [if_neg h0, if_neg h1]
      ring

/- English proof (authored)
The primitive value is a product of coset averages. For the trivial character every summand in each average is one. The inertia subgroup contains zero, so its cardinality is positive and cancels in the average. Every factor of the product is thus one.
-/
theorem primitive_value_trivial : PrimValTriv (H := H) := by
  intro D n
  unfold primVal
  refine Finset.prod_eq_one (fun p _ => ?_)
  unfold cosetMean
  simp only [zero_apply_lemma, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine div_self ?_
  rw [Nat.cast_ne_zero]
  exact Finset.card_ne_zero.mpr ⟨0, by simp⟩

/- English proof (authored)
For a positive power of a prime, the prime support is the singleton containing that prime and its exponent is i. The primitive-value product therefore has exactly the stated coset-average factor.
-/
theorem primitive_value_pow : PrimValPow (H := H) := by
  intro D ψ p i hp hi
  unfold primVal
  first
  | rw [Nat.primeFactors_prime_pow (by omega) hp, Finset.prod_singleton, hp.factorization_pow,
      Finsupp.single_eq_same]
  | simp [Nat.primeFactors_prime_pow (by omega : i ≠ 0) hp, hp.factorization_pow]

/- English proof (authored)
The translating element has first binary coordinate one. Adding it adds one to the first coordinate of x.
-/
private theorem sgc0_fst_lemma_3 (x : E0 × H) : (x + sgc0).1.1 = x.1.1 + 1 := by
  simp [sgc0]

/- English proof (authored)
At the distinguished prime the inertia subgroup consists of zero and the element with first binary coordinate one. Its coset therefore consists of the unshifted Frobenius multiple and that multiple plus the translating element. The two first coordinates differ by one. Exactly one is in the complementary half, giving the claimed unique element in either case.
-/
theorem double_coset_singleton : DCosetSingle (H := H) := by
  intro D hD i
  by_cases hf : InPhi (i • D.frob D.d)
  · refine ⟨i • D.frob D.d + sgc0, ⟨?_, ?_⟩, ?_⟩
    · rw [hD.inertia_d]
      right
      abel
    · rw [not_inPhi_iff, sgc0_fst_lemma_3, (inPhi_iff _).1 hf]
      decide
    · rintro y ⟨hy1, hy2⟩
      rcases (hD.inertia_d _).1 hy1 with h | h
      · exact absurd (by rw [sub_eq_zero.1 h]; exact hf) hy2
      · rw [sub_eq_iff_eq_add] at h
        rw [h, add_comm]
  · refine ⟨i • D.frob D.d, ⟨?_, hf⟩, ?_⟩
    · rw [hD.inertia_d]
      left
      exact sub_self _
    · rintro y ⟨hy1, hy2⟩
      rcases (hD.inertia_d _).1 hy1 with h | h
      · exact sub_eq_zero.1 h
      · exfalso
        apply hy2
        rw [sub_eq_iff_eq_add] at h
        rw [h, inPhi_iff, add_comm, sgc0_fst_lemma_3, (not_inPhi_iff _).1 hf]
        decide

end

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (authored)
Elements of the subgroup are exactly the ambient group elements satisfying its membership predicate. The subgroup type counts these elements once each, as does the filtered finite set.
-/
lemma natCard_eq_filter (I : AddSubgroup (E0 × H)) [DecidablePred (fun x => x ∈ I)] :
    Nat.card I = (univ.filter (fun x => x ∈ I)).card := by
  first
  | (rw [Nat.card_eq_fintype_card]; exact Fintype.card_subtype _)
  | (rw [Nat.card_eq_fintype_card]; convert Fintype.card_subtype (fun x => x ∈ I))
  | simp [Nat.card_eq_fintype_card, Fintype.card_subtype]

open Classical in
/- English proof (authored)
Expand the coset average and interchange its finite sum with the character sum. By orthogonality, for a subgroup element x the inner sum is zero unless h + x = g, when it equals the ambient group cardinality. The only possible contributing element is x = g − h. If it belongs to the subgroup, divide by the subgroup cardinality and the selected cardinality, noting that the ambient group has twice the selected cardinality. Otherwise every summand is zero.
-/
lemma ortho_coset (I : AddSubgroup (E0 × H)) (h g : E0 × H) :
    (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * cosetMean I h ψ
      = if g - h ∈ I then 2 / (Nat.card I : ℂ) else 0 := by
  have hS : Nat.card I = (univ.filter (fun x => x ∈ I)).card := natCard_eq_filter I
  have hc : ((univ.filter (fun x => x ∈ I)).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.card_ne_zero.mpr ⟨0, by simp⟩
  have e1 : ∀ ψ : AddChar (E0 × H) ℂ, cosetMean I h ψ
      = (∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x)) / ((univ.filter (fun x => x ∈ I)).card : ℂ) :=
    fun ψ => rfl
  simp_rw [e1]
  have e2 : ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g)
        * ((∑ x ∈ univ.filter (fun x => x ∈ I), ψ (h + x)) / ((univ.filter (fun x => x ∈ I)).card : ℂ))
      = (∑ x ∈ univ.filter (fun x => x ∈ I), ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ψ (h + x))
        / ((univ.filter (fun x => x ∈ I)).card : ℂ) := by
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    rw [mul_div_assoc', Finset.mul_sum]
  rw [e2]
  have e3 : ∀ x : E0 × H, (h + x = g) ↔ (x = g - h) := fun x => by
    rw [eq_sub_iff_add_eq, add_comm]
  simp_rw [ortho, e3]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hS]
  have hΦ := phi_card_ne_zero (H := H)
  split_ifs
  · rw [card_G]
    first
    | (field_simp; done)
    | (field_simp; ring)
  · simp

end

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (authored)
For each character substitute the prime-power formula for its primitive value. The resulting sum is the coset orthogonality expression with the inertia subgroup and the given Frobenius multiple, so the coset formula applies.
-/
theorem orthogonality_ramified : OrthoRam (H := H) := by
  intro D p i hp hi g
  have hv : ∀ ψ : AddChar (E0 × H) ℂ, primVal D ψ (p ^ i) = cosetMean (D.inertia p) (i • D.frob p) ψ :=
    fun ψ => primitive_value_pow D ψ p i hp hi
  simp_rw [hv]
  convert ortho_coset (D.inertia p) (i • D.frob p) g

/- English proof (authored)
At the specified unramified prime the inertia subgroup is trivial. Thus its coset condition says exactly that g equals the Frobenius multiple, and its cardinality is one. Substituting these facts into the ramified orthogonality formula gives the two values.
-/
theorem orthogonality_unramified : OrthoUnram (H := H) := by
  intro D hD p i hp h2 hq hd hi g
  refine (orthogonality_ramified D p i hp hi g).trans ?_
  rw [hD.unram p hp h2 hq hd]
  by_cases hc : i • D.frob p = g
  · subst hc
    simp
  · rw [if_neg hc, if_neg]
    intro hm
    rw [AddSubgroup.mem_bot, sub_eq_zero] at hm
    exact hc hm.symm

end

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (authored)
The von Mangoldt function vanishes away from positive prime powers. Each such power has a unique prime base and exponent by prime factorization and strict growth of the powers of a prime. When the power is at most N, both its prime base and its exponent are within the indicated bounds. Conversely, candidates whose power exceeds N contribute zero by assumption. Reindex the nonzero contributions by the prime and exponent, using that the von Mangoldt value is the logarithm of the prime.
-/
lemma sum_vonMangoldt_primePow (N : ℕ) (X : ℕ → ℂ)
    (hX : ∀ p i, p.Prime → 1 ≤ i → N < p ^ i → X (p ^ i) = 0) :
    ∑ n ∈ Icc 1 N, (Λ n : ℂ) * X n
      = ∑ p ∈ (range (N + 1)).filter Nat.Prime, ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * X (p ^ i) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1 ^ x.2) ?_ ?_ ?_ ?_
  · intro x hx hne
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hx
    obtain ⟨⟨_, hp⟩, hi1, _⟩ := hx
    have hle : x.1 ^ x.2 ≤ N := by
      by_contra hlt
      exact hne (by rw [hX x.1 x.2 hp hi1 (not_le.1 hlt), mul_zero])
    show x.1 ^ x.2 ∈ Icc 1 N
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_pow _ _ hp.pos, hle⟩
  · intro x hx _ y hy _ hxy
    have hxy' : x.1 ^ x.2 = y.1 ^ y.2 := hxy
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hx hy
    obtain ⟨⟨_, hp⟩, hi1, _⟩ := hx
    obtain ⟨⟨_, hq⟩, hj1, _⟩ := hy
    have hpq : x.1 = y.1 := by
      have hd : x.1 ∣ y.1 ^ y.2 := by
        rw [← hxy']
        exact dvd_pow_self _ (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd)
    have hij : x.2 = y.2 := by
      rw [hpq] at hxy'
      exact Nat.pow_right_injective hq.two_le hxy'
    exact Prod.ext hpq hij
  · intro n hn hne
    rw [Finset.mem_Icc] at hn
    have hΛ : Λ n ≠ 0 := by
      intro h0
      apply hne
      show (Λ n : ℂ) * X n = 0
      rw [h0]
      simp
    rw [ArithmeticFunction.vonMangoldt_ne_zero_iff, isPrimePow_nat_iff] at hΛ
    obtain ⟨p, k, hp, hk, rfl⟩ := hΛ
    have h1 : p ≤ p ^ k := Nat.le_self_pow (by omega) p
    have h2 : k < p ^ k := by
      first
      | exact Nat.lt_pow_self hp.one_lt
      | exact Nat.lt_pow_self hp.one_lt k
    refine ⟨(p, k), ?_, ?_, rfl⟩
    · rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      exact ⟨⟨Nat.lt_succ_of_le (h1.trans hn.2), hp⟩, hk, (h2.trans_le hn.2).le⟩
    · intro h0
      apply hne
      show (Λ (p ^ k) : ℂ) * X (p ^ k) = 0
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact h0
  · intro x hx _
    rw [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hx
    show (Real.log x.1 : ℂ) * X (x.1 ^ x.2) = (Λ (x.1 ^ x.2) : ℂ) * X (x.1 ^ x.2)
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hx.1.2]

/- English proof (authored)
A complementary element has first coordinate one. Its partner adds one to that coordinate, giving zero modulo two and hence membership in the selected half.
-/
lemma partner_inPhi {g : E0 × H} (t : H) (hg : ¬ InPhi g) : InPhi (partner t g) := by
  rw [inPhi_iff, partner_fst_lemma, (not_inPhi_iff g).1 hg]
  decide

/- English proof (authored)
The partner lies in the selected half, so its weight is positive and a divided by that weight is at most N. Since m > N ≥ 0, this gives a < m times the weight. Dividing by positive m makes the argument of the positive part negative, so the positive part is zero.
-/
lemma max_zero_of_gt {N : ℕ} {a : ℝ} {t : H} {w : E0 × H → ℝ} (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) {g : E0 × H} (hg : ¬ InPhi g) {m : ℝ} (hm : (N : ℝ) < m) :
    max (a / m - w (partner t g)) 0 = 0 := by
  have hρ := partner_inPhi t hg
  have hwρ := hw _ hρ
  have h1 : a / w (partner t g) < m := lt_of_le_of_lt (hN _ hρ) hm
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt (Nat.cast_nonneg N) hm
  have h3 : a < m * w (partner t g) := (div_lt_iff₀ hwρ).1 h1
  have h2 : a / m < w (partner t g) := by
    rw [div_lt_iff₀ hm0]
    linarith [mul_comm m (w (partner t g))]
  exact max_eq_right (by linarith)

/- English proof (authored)
At every positive exponent the distinguished prime power is at least the prime itself and exceeds N. Each term uses a complementary group element, so its positive-part weight vanishes by the cutoff estimate. Both finite sums are therefore zero.
-/
lemma askD_zero_of_gt (D : ArithData H) (hD : HostFacts D) {N : ℕ} {a : ℝ} {t : H} {w : E0 × H → ℝ}
    (hw : ∀ ρ, InPhi ρ → 0 < w ρ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) (hdN : N < D.d) :
    askD D N a t w = 0 := by
  classical
  unfold askD
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro g hg
  have hg' : ¬ InPhi g := (Finset.mem_filter.1 hg).2.2
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  apply max_zero_of_gt hw hN hg'
  have h3 : D.d ≤ D.d ^ i := Nat.le_self_pow (by omega) _
  exact_mod_cast lt_of_lt_of_le hdN h3

/- English proof (authored)
The inertia group at the distinguished prime consists of zero and the specified translating element. They are distinct because their first binary coordinates differ, so the group has cardinality two.
-/
lemma card_inertia_d (D : ArithData H) (hD : HostFacts D) : (Nat.card (D.inertia D.d) : ℂ) = 2 := by
  classical
  have h0 : (0 : E0 × H) ≠ sgc0 := by
    intro h
    have h' : (0 : E0 × H).1.1 = (sgc0 : E0 × H).1.1 := by rw [h]
    simp [sgc0] at h'
  have hs : (univ.filter (fun x : E0 × H => x ∈ D.inertia D.d)) = {0, sgc0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    exact hD.inertia_d x
  have hc : Nat.card (D.inertia D.d) = 2 := by
    rw [natCard_eq_filter, hs, Finset.card_pair h0]
  exact_mod_cast hc

end

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def Kc (D : ArithData H) (n : ℕ) (g : E0 × H) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * primVal D ψ n

def Fc (a : ℝ) (t : H) (w : E0 × H → ℝ) (n : ℕ) (g : E0 × H) : ℂ :=
  ((max (a / (n : ℝ) - w (partner t g)) 0 : ℝ) : ℂ)

/- English proof (authored)
The character kernel is two at the Frobenius multiple and zero elsewhere. Thus for each exponent the inner sum contributes only when this multiple lies in the complementary half. Substituting its positive-part weight and summing over exponents gives the defining prime sum multiplied by twice the prime logarithm.
-/
lemma local_unram (D : ArithData H) (hD : HostFacts D) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hq : p ≠ D.q1) (hd : p ≠ D.d) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) := by
  have hK : ∀ i, 1 ≤ i → ∀ g, Kc D (p ^ i) g = if i • D.frob p = g then 2 else 0 :=
    fun i hi g => orthogonality_unramified D hD p i hp h2 hq hd hi g
  have hin : ∀ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = (((if ¬ InPhi (i • D.frob p) then
          2 * Real.log p * max (a / (p : ℝ) ^ i - w (partner t (i • D.frob p))) 0 else 0) : ℝ) : ℂ) := by
    intro i hi
    simp_rw [hK i (Finset.mem_Icc.1 hi).1, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> first
      | (simp; done)
      | (simp only [Fc]; push_cast; ring)
  rw [Finset.sum_congr rfl hin, ← Complex.ofReal_sum]
  congr 1
  unfold askP
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> ring

/- English proof (authored)
For these primes, the inertia subgroup and the Frobenius element lie in the selected half. The whole coset of every natural Frobenius multiple also lies there by closure under addition. The ramified orthogonality formula therefore gives zero at every complementary element, and the sum vanishes.
-/
lemma local_split (D : ArithData H) (hD : HostFacts D) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    {p : ℕ} (hp : p.Prime) (h2 : p = 2 ∨ p = D.q1) :
    ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g
      = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  rw [Finset.sum_eq_zero, mul_zero]
  intro g hg
  have hg' : ¬ InPhi g := (Finset.mem_filter.1 hg).2
  have hK : Kc D (p ^ i) g = 0 := by
    refine (orthogonality_ramified D p i hp hi1 g).trans ?_
    rw [if_neg]
    intro hm
    apply hg'
    have h1 := hD.split_inertia p h2 _ hm
    have h3 := inPhi_nsmul (hD.split_frob p h2) i
    have h4 := inPhi_add h1 h3
    rwa [sub_add_cancel] at h4
  rw [hK, zero_mul]

/- English proof (authored)
At the distinguished prime the inertia subgroup has cardinality two. The coset kernel is therefore one on its coset and zero elsewhere. Restricting the complementary sum to that coset leaves exactly the positive-part terms in the distinguished prime contribution. The prime logarithm factors out.
-/
lemma local_d (D : ArithData H) (hD : HostFacts D) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) :
    ∑ i ∈ Icc 1 N, (Real.log D.d : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        Kc D (D.d ^ i) g * Fc a t w (D.d ^ i) g
      = ((Real.log D.d * askD D N a t w : ℝ) : ℂ) := by
  classical
  have hc := card_inertia_d D hD
  have hK : ∀ i, 1 ≤ i → ∀ g, Kc D (D.d ^ i) g
      = if g - i • D.frob D.d ∈ D.inertia D.d then 1 else 0 := by
    intro i hi g
    refine (orthogonality_ramified D D.d i hD.d_prime hi g).trans ?_
    rw [hc]
    split_ifs <;> norm_num
  unfold askD
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  congr 1
  simp_rw [hK i (Finset.mem_Icc.1 hi).1, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  by_cases h1 : InPhi g <;> by_cases h2 : g - i • D.frob D.d ∈ D.inertia D.d <;> simp [h1, h2, Fc]

end

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (authored)
Interchange the finite sums to combine the normalized character coefficients into the character kernel at each integer n. The cutoff estimate makes all prime-power terms beyond N vanish, so the von Mangoldt sum can be grouped by prime and exponent. The two split primes contribute zero. The distinguished prime contributes its inertia-coset sum. For every other prime, use the unramified kernel and note that a Frobenius element in the selected half has every natural multiple in that half, so only the inert primes contribute. If the distinguished prime exceeds N, its separate contribution vanishes by the same cutoff. This gives the arithmetic sum in the claimed form.
-/
theorem characterSum_expansion : AskExpansion (H := H) := by
  classical
  intro D hD a t w ha hw N hN
  have step1 : (1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
      = ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * (Kc D n g * Fc a t w n g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    simp only [Kc, Fc, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun ψ _ => ?_))
    ring
  have step2 : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * (Kc D n g * Fc a t w n g)
      = ∑ n ∈ Icc 1 N, (Λ n : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
          Kc D n g * Fc a t w n g := by
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  have hX : ∀ p i, p.Prime → 1 ≤ i → N < p ^ i →
      ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D (p ^ i) g * Fc a t w (p ^ i) g = 0 := by
    intro p i _ _ hlt
    apply Finset.sum_eq_zero
    intro g hg
    have hg' : ¬ InPhi g := (Finset.mem_filter.1 hg).2
    have hF : Fc a t w (p ^ i) g = 0 := by
      simp only [Fc]
      rw [max_zero_of_gt (m := ((p ^ i : ℕ) : ℝ)) hw hN hg' (by exact_mod_cast hlt), Complex.ofReal_zero]
    rw [hF, mul_zero]
  rw [step1, step2, sum_vonMangoldt_primePow N
    (fun n => ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), Kc D n g * Fc a t w n g) hX]
  have hloc : ∀ p ∈ (range (N + 1)).filter Nat.Prime,
      ∑ i ∈ Icc 1 N, (Real.log p : ℂ) * ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
          Kc D (p ^ i) g * Fc a t w (p ^ i) g
        = (((if IsInert D p then 2 * Real.log p * askP D N a t w p else 0)
            + (if p = D.d then Real.log D.d * askD D N a t w else 0) : ℝ) : ℂ) := by
    intro p hp
    have hp' : p.Prime := (Finset.mem_filter.1 hp).2
    by_cases hs : p = 2 ∨ p = D.q1
    · rw [local_split D hD N a t w hp' hs]
      have h1 : ¬ IsInert D p := fun h => hs.elim h.2.1 h.2.2.1
      have h2 : p ≠ D.d := fun h => hs.elim (fun h2' => hD.d_ne_two (h.symm.trans h2'))
        (fun hq' => hD.firstPrime_ne_secondPrime (h.symm.trans hq').symm)
      simp [h1, h2]
    · push_neg at hs
      by_cases hdd : p = D.d
      · subst hdd
        rw [local_d D hD N a t w]
        have h1 : ¬ IsInert D D.d := fun h => h.2.2.2.1 rfl
        simp [h1]
      · rw [local_unram D hD N a t w hp' hs.1 hs.2 hdd]
        by_cases hin : IsInert D p
        · simp [hin, hdd]
        · have hphi : InPhi (D.frob p) := by
            by_contra hc
            exact hin ⟨hp', hs.1, hs.2, hdd, hc⟩
          have h0 : askP D N a t w p = 0 := by
            unfold askP
            apply Finset.sum_eq_zero
            intro i hi
            exact absurd (inPhi_nsmul hphi i) (Finset.mem_filter.1 hi).2
          simp [hin, hdd, h0]
  rw [Finset.sum_congr rfl hloc, ← Complex.ofReal_sum]
  unfold ASK
  congr 1
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_filter, Finset.filter_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  · simp only [Finset.sum_ite_eq', Finset.sum_ite_eq]
    by_cases hdm : D.d ∈ (range (N + 1)).filter Nat.Prime
    · rw [if_pos hdm]
    · rw [if_neg hdm]
      have hdN : N < D.d := by
        by_contra hc
        apply hdm
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hD.d_prime⟩
      rw [askD_zero_of_gt D hD hw hN hdN, mul_zero]

end

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (authored)
Distribute the factor w across the difference. Since w is nonzero, w times a/w is a. The two terms then become a/n and −w.
-/
lemma term_real (a w : ℝ) (hw : w ≠ 0) (n : ℕ) : a / n - w = w * (a / w / n - 1) := by
  have hw' : w * (a / w) = a := by
    first
    | field_simp
    | rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hw, mul_one]
  rw [mul_sub, mul_one, mul_div_assoc', hw']

/- English proof (authored)
For an integer n ≥ 1, the weight a/n − W is nonnegative exactly when n ≤ a/W. Since n is integral, this is the cutoff at the natural floor of a/W. The positive part equals the weight below that cutoff and vanishes above it. The cutoff is at most N, so removing the zero terms gives the stated shorter sum.
-/
lemma sum_cut (D : ArithData H) (ψ : AddChar (E0 × H) ℂ) (N : ℕ) (a W : ℝ) (ha : 0 < a) (hW : 0 < W)
    (hN : a / W ≤ N) :
    ∑ n ∈ Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / n - W) 0 : ℝ) : ℂ)
      = ∑ n ∈ Icc 1 ⌊a / W⌋₊, (Λ n : ℂ) * primVal D ψ n * ((a / n - W : ℝ) : ℂ) := by
  have hMN : ⌊a / W⌋₊ ≤ N := by
    have h1 : ((⌊a / W⌋₊ : ℕ) : ℝ) ≤ N := (Nat.floor_le (by positivity)).trans hN
    exact_mod_cast h1
  have hterm : ∀ n ∈ Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / n - W) 0 : ℝ) : ℂ)
      = if n ≤ ⌊a / W⌋₊ then (Λ n : ℂ) * primVal D ψ n * ((a / n - W : ℝ) : ℂ) else 0 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
    have hn0 : (0 : ℝ) < n := by linarith
    split_ifs with h
    · have h2 : (n : ℝ) ≤ a / W := (Nat.le_floor_iff (by positivity)).1 h
      rw [le_div_iff₀ hW] at h2
      have h3 : W ≤ a / n := by
        rw [le_div_iff₀ hn0]
        linarith [mul_comm W (n : ℝ)]
      rw [max_eq_left (by linarith)]
    · have h2 : a / W < n := (Nat.floor_lt (by positivity)).1 (not_le.1 h)
      rw [div_lt_iff₀ hW] at h2
      have h3 : a / n < W := by
        rw [div_lt_iff₀ hn0]
        linarith [mul_comm W (n : ℝ)]
      rw [max_eq_right (by linarith)]
      simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2.trans hMN⟩, h2⟩

/- English proof (authored)
For the trivial character, the primitive values are one. Factor w out of the weight to obtain the zeta smoothing sum at a/w, then expand its logarithmic and linear corrections. Since w times a/w equals a, the logarithm of the quotient splits into log(a) minus log(w) and gives the displayed main terms. For a nontrivial character, the same factorization gives its smoothing sum. The definition adds the linear correction involving the character coefficient, which is removed by subtracting a times that coefficient.
-/
lemma inner_eq (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (a w : ℝ)
    (ha : 0 < a) (hw : 0 < w) :
    ∑ n ∈ Icc 1 ⌊a / w⌋₊, (Λ n : ℂ) * primVal D ψ n * ((a / n - w : ℝ) : ℂ)
      = (w : ℂ) * GPsi D ell ψ (a / w) + (if ψ = 0 then
          ((a * Real.log a - a * Real.log w - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * ell ψ) := by
  unfold GPsi
  split_ifs with h0
  · subst h0
    simp only [Gz, Sz]
    simp_rw [primitive_value_trivial D, mul_one, ← Complex.ofReal_mul]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_add]
    congr 1
    have hS : w * ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * (a / w / n - 1)
        = ∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * (a / n - w) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [term_real a w hw.ne' n]
      ring
    have hwa' : w * (a / w) = a := by field_simp
    rw [Real.log_div ha.ne' hw.ne', ← hS]
    linear_combination (Real.log a - Real.log w - (1 + Real.eulerMascheroniConstant)) * hwa'
  · have hwa' : w * (a / w) = a := by field_simp
    have hwa : (w : ℂ) * ((a / w : ℝ) : ℂ) = a := by
      rw [← Complex.ofReal_mul, hwa']
    rw [mul_add, Finset.mul_sum]
    have hs : ∀ n ∈ Icc 1 ⌊a / w⌋₊, (w : ℂ) * ((Λ n : ℂ) * primVal D ψ n * ((a / w / n - 1 : ℝ) : ℂ))
        = (Λ n : ℂ) * primVal D ψ n * ((a / n - w : ℝ) : ℂ) := by
      intro n _
      rw [term_real a w hw.ne' n]
      push_cast
      ring
    rw [Finset.sum_congr rfl hs, ← mul_assoc, hwa]
    ring

end

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

/- English proof (authored)
Use the character expansion and evaluate each inner sum at the partner weight, which is positive and within the cutoff. The smoothing error terms give the stated double sum. For the remaining terms, interchange the character and group sums. The trivial character contributes its full logarithmic main term. Every nontrivial character's constant correction vanishes by the complement sum except for the sign character, whose complement sum is minus the selected cardinality. This converts its correction into the positive sign-character term. Reindex the trivial character's weight-log sum by the partner bijection, count the constant terms, and divide by the nonzero selected cardinality.
-/
theorem colour_balance : AskMainBalance (H := H) := by
  classical
  intro D hD ell a t w ha hw N hN
  rw [characterSum_expansion D hD a t w ha hw N hN]
  have hinner : ∀ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∀ ψ : AddChar (E0 × H) ℂ,
      ∑ n ∈ Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
        = ((w (partner t g) : ℝ) : ℂ) * GPsi D ell ψ (a / w (partner t g))
          + (if ψ = 0 then ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ) := by
    intro g hg ψ
    have hg' : ¬ InPhi g := (Finset.mem_filter.1 hg).2
    have hρ := partner_inPhi t hg'
    rw [sum_cut D ψ N a (w (partner t g)) ha (hw _ hρ) (hN _ hρ),
      inner_eq D ell ψ a (w (partner t g)) ha (hw _ hρ)]
  have hsum : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ ψ : AddChar (E0 × H) ℂ,
        starRingEnd ℂ (ψ g) * ∑ n ∈ Icc 1 N,
          (Λ n : ℂ) * primVal D ψ n * ((max (a / n - w (partner t g)) 0 : ℝ) : ℂ)
      = ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ ψ : AddChar (E0 × H) ℂ,
          starRingEnd ℂ (ψ g) * ((w (partner t g) : ℝ) : ℂ) * GPsi D ell ψ (a / w (partner t g))
        + ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ ψ : AddChar (E0 × H) ℂ,
          starRingEnd ℂ (ψ g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun g hg => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    rw [hinner g hg ψ]
    ring
  have hcorr : ∀ ψ : AddChar (E0 × H) ℂ, ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        starRingEnd ℂ (ψ g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ)
      = (if ψ = 0 then ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
            ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else 0)
        + (if ψ = chC then (a : ℂ) * ell chC * ((PhiSet (H := H)).card : ℂ) else 0) := by
    intro ψ
    by_cases h0 : ψ = 0
    · have h1 : ¬ ψ = chC := fun h => chC_ne_zero (h ▸ h0)
      rw [if_pos h0, if_neg h1, add_zero]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [if_pos h0, h0, zero_apply_lemma, map_one, one_mul]
    · rw [if_neg h0, zero_add]
      simp only [if_neg h0]
      rw [← Finset.sum_mul, colour_sum ψ, if_neg h0]
      by_cases h1 : ψ = chC
      · rw [if_pos h1, if_pos h1, h1]
        ring
      · rw [if_neg h1, if_neg h1, zero_mul]
  have hB : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g), ∑ ψ : AddChar (E0 × H) ℂ,
          starRingEnd ℂ (ψ g) * (if ψ = 0 then ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) else -(a : ℂ) * ell ψ)
      = ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
            ((a * Real.log a - a * Real.log (w (partner t g))
              - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
        + (a : ℂ) * ell chC * ((PhiSet (H := H)).card : ℂ) := by
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun ψ _ => hcorr ψ), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hC : ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g),
        (a * Real.log a - a * Real.log (w (partner t g)) - (1 + Real.eulerMascheroniConstant) * a)
      = ((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a)
        - a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      ← Finset.mul_sum, sum_partner t (fun ρ => Real.log (w ρ)), card_notPhi]
    simp only [nsmul_eq_mul]
    ring
  rw [hsum, hB, ← Complex.ofReal_sum, hC]
  have hΦ := phi_card_ne_zero (H := H)
  unfold De MAIN
  push_cast
  field_simp
  ring

end

end Formalism.LFunctionChainParameters.characterSumData
