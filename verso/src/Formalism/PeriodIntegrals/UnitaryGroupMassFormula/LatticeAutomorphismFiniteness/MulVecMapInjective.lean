import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.SylvesterLe
import Lemmata.GeneralBFactUpperAltForm.Imports

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Matrix Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem hT_expand (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * S.gram i j * S.frame.repr y j := by
  have hx : ∀ w, S.hT x w = ∑ i, star (S.frame.repr x i) * S.hT (S.frame i) w := by
    intro w
    conv_lhs => rw [← S.frame.sum_repr x]
    rw [map_sum, LinearMap.sum_apply]
    simp [LinearMap.map_smulₛₗ, starRingEnd_apply]
  have hy : ∀ w, S.hT w y = ∑ j, S.hT w (S.frame j) * S.frame.repr y j := by
    intro w
    conv_lhs => rw [← S.frame.sum_repr y]
    rw [map_sum]
    simp [mul_comm]
  rw [hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [HSpace.gram, mul_assoc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem herm_swap (x y : S.V) : S.hT y x = star (S.hT x y) := by
  rw [← S.herm.eq x y]; rfl

def coordC {k : Type} (τ : E →+* ℂ) (u : k → S.V) : Matrix (Fin S.rank) k ℂ :=
  Matrix.of fun i a => τ (S.frame.repr (u a) i)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem gram_entry (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    {k : Type} (τ : E →+* ℂ) (u : k → S.V) (a b : k) :
    ((coordC S τ u)ᴴ * S.gram.map τ * coordC S τ u) a b = τ (S.hT (u a) (u b)) := by
  rw [hT_expand, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, coordC, Matrix.of_apply, Matrix.map_apply,
    map_sum, map_mul, hstar, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem form_eq {n k : Type} [Fintype n] [Fintype k] (B : Matrix n k ℂ) (J : Matrix n n ℂ) (v : k → ℂ) :
    star (B *ᵥ v) ⬝ᵥ (J *ᵥ (B *ᵥ v)) = star v ⬝ᵥ ((Bᴴ * J * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem mulVec_map_injective {K : Type} [Field K] {n k : Type} [Fintype n] [DecidableEq n] [Fintype k]
    [DecidableEq k] (f : K →+* ℂ) (A : Matrix n k K) (hA : Function.Injective A.mulVec) :
    Function.Injective (A.map f).mulVec := by
  first | exact Bl.general_b_fact_upper_alt_form.goal1 .. | (apply Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_alt_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_alt_form.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› f A hA | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› f A | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› f | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n k | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› n | exact @Bl.general_b_fact_upper_alt_form.goal1 K ‹_› | exact @Bl.general_b_fact_upper_alt_form.goal1 K

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses repeatedly using the stated equalities. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem coord_injective {k : Type} [Fintype k] (u : k → S.V) (hu : LinearIndependent E u) :
    Function.Injective (Matrix.of fun i a => S.frame.repr (u a) i).mulVec := by
  intro c d hcd
  have key : ∀ c : k → E, (Matrix.of fun i a => S.frame.repr (u a) i) *ᵥ c = S.frame.repr (∑ a, c a • u a) := by
    intro c; ext i
    simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
  rw [key, key] at hcd
  have h2 := S.frame.repr.injective (Finsupp.ext fun i => congrFun hcd i)
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h2
  simp_rw [← sub_smul] at h2
  have h3 := (Fintype.linearIndependent_iff.mp hu) (fun a => c a - d a) h2
  funext a; exact sub_eq_zero.mp (h3 a)

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Simplify using the standard rewrite rules. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem pos_perp (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (τ : E →+* ℂ) {p q : ℕ} (hsig : Formalism.UG.HasSignature (S.gram.map τ) p q) {r : ℕ} (hq : q ≤ r + 1)
    (e : Fin r → S.V) (he : LinearIndependent E e) (hee : ∀ a b, S.hT (e a) (e b) = 0)
    (z : S.V) (hez : ∀ a, S.hT (e a) z = 0) (hzz : (τ (S.hT z z)).re < 0)
    (y : S.V) (hey : ∀ a, S.hT (e a) y = 0) (hzy : S.hT z y = 0)
    (hyX : y ∉ Submodule.span E (Set.range e)) : 0 < (τ (S.hT y y)).re := by
  by_contra hle'
  have hle := not_lt.mp hle'
  have hzz0 : S.hT z z ≠ 0 := by
    intro h; rw [h, map_zero] at hzz; simp at hzz
  have hze : ∀ a, S.hT z (e a) = 0 := fun a => by rw [herm_swap, hez, star_zero]
  have hye : ∀ a, S.hT y (e a) = 0 := fun a => by rw [herm_swap, hey, star_zero]
  have hyz : S.hT y z = 0 := by rw [herm_swap, hzy, star_zero]

  have hXz : ∀ x ∈ Submodule.span E (Set.range e), S.hT z x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hze a
    | zero => simp
    | add x y _ _ h1 h2 => simp [map_add, h1, h2]
    | smul c x _ h => simp [h]
  let u : Fin r ⊕ Fin 2 → S.V := Sum.elim e ![z, y]
  have hpair : LinearIndependent E ![z, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (S.hT z) hst
    simp [map_add, hzy] at h1
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hzz0
    subst hs
    refine ⟨rfl, ?_⟩
    simp at hst
    rcases hst with h | h
    · exact h
    · exact absurd (h ▸ Submodule.zero_mem _) hyX
  have hdisj : Disjoint (Submodule.span E (Set.range e)) (Submodule.span E (Set.range ![z, y])) := by
    rw [Submodule.disjoint_def]
    intro w hw1 hw2
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Submodule.mem_span_pair] at hw2
    obtain ⟨s, t, rfl⟩ := hw2
    have h1 := hXz _ hw1
    simp [map_add, hzy] at h1
    have hs : s = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hzz0
    subst hs
    simp only [zero_smul, zero_add] at hw1 ⊢
    by_cases ht : t = 0
    · simp [ht]
    · exfalso; apply hyX
      have := Submodule.smul_mem _ t⁻¹ hw1
      rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  have hind : LinearIndependent E u := he.sum_type hpair hdisj
  have hB : Function.Injective (coordC S τ u).mulVec :=
    mulVec_map_injective τ _ (coord_injective S u hind)
  have hneg : ∀ v : Fin r ⊕ Fin 2 → ℂ,
      (star (coordC S τ u *ᵥ v) ⬝ᵥ (S.gram.map τ *ᵥ (coordC S τ u *ᵥ v))).re ≤ 0 := by
    intro v
    rw [form_eq]
    have hM : ∀ a b, ((coordC S τ u)ᴴ * S.gram.map τ * coordC S τ u) a b = τ (S.hT (u a) (u b)) :=
      gram_entry S hstar τ u
    simp only [dotProduct, Matrix.mulVec, hM, Fintype.sum_sum_type, Fin.sum_univ_two, u,
      Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
      hee, hez, hey, hze, hye, hzy, hyz, map_zero, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
      add_zero]
    have hn : ∀ w : ℂ, ∀ c : ℂ, (star w * (c * w)).re = Complex.normSq w * c.re := by
      intro w c
      rw [Complex.star_def, mul_comm c w, ← mul_assoc, mul_comm (starRingEnd ℂ w) w, Complex.mul_conj]
      rw [Complex.re_ofReal_mul]
    rw [Pi.star_apply, Pi.star_apply, Complex.add_re, hn, hn]
    have := Complex.normSq_nonneg (v (Sum.inr 0))
    have := Complex.normSq_nonneg (v (Sum.inr 1))
    nlinarith
  have hc := sylvester_le _ hsig _ hB hneg
  simp at hc
  omega

end PI.AutLzFinite.SlopeTestRemainingChoices
