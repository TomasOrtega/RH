import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.GoodModelLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.IntegerEndomorphismInstance
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalI
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.AtVariableWeierstrassDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementJ

noncomputable section
open scoped BigOperators
open Filter Topology

namespace Formalism.L2.Th1.B.Fib

open PowerSeries
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries taylor_ring isogenyP halfShift)
open Formalism.L2.Th1.F.TaylorWp
open Formalism.L2.Th1.F.EndoZ

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem sum_reps {ι κ M : Type} [AddCommMonoid M] (L : PeriodPair) (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ)
    (hA : ∀ i ∈ s, ∀ i' ∈ s, a i - a i' ∈ L.lattice → i = i')
    (hB : ∀ j ∈ t, ∀ j' ∈ t, b j - b j' ∈ L.lattice → j = j')
    (hAB : ∀ i ∈ s, ∃ j ∈ t, a i - b j ∈ L.lattice)
    (hBA : ∀ j ∈ t, ∃ i ∈ s, b j - a i ∈ L.lattice)
    (f : ℂ → M) (hf : ∀ x y, x - y ∈ L.lattice → f x = f y) :
    ∑ i ∈ s, f (a i) = ∑ j ∈ t, f (b j) := by
  choose φ hφ using hAB
  refine Finset.sum_bij φ (fun i hi => (hφ i hi).1) ?_ ?_ (fun i hi => hf _ _ (hφ i hi).2)
  · intro i hi i' hi' h
    apply hA i hi i' hi'
    have h1 := L.lattice.sub_mem (hφ i hi).2 (hφ i' hi').2
    rw [h] at h1
    have e : a i - b (φ i' hi') - (a i' - b (φ i' hi')) = a i - a i' := by ring
    rwa [e] at h1
  · intro j hj
    obtain ⟨i, hi, h⟩ := hBA j hj
    refine ⟨i, hi, ?_⟩
    apply hB _ (hφ i hi).1 j hj
    have h1 := L.lattice.neg_mem (L.lattice.add_mem h (hφ i hi).2)
    have e : -(b j - a i + (a i - b (φ i hi))) = b (φ i hi) - b j := by ring
    rwa [e] at h1

def repA (Q0 : ℂ) : Option ℂ → ℂ := fun o => Q0 + o.elim 0 id

def repB : ℂ ⊕ ℂ → ℂ := Sum.elim id Neg.neg

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
theorem two_mul_half (ω₀ : ℂ) : 2 * (ω₀ / 2) = ω₀ := by ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem notMem_of_two {L : PeriodPair} {Q : ℂ} (h : 2 * Q ∉ L.lattice) : Q ∉ L.lattice := by
  intro hQ
  apply h
  rw [two_mul]
  exact L.lattice.add_mem hQ hQ

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation.

Both sides reduce to the same expression. It suffices to derive a contradiction. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. It suffices to derive a contradiction. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Reduce the equality to equality of the corresponding arguments.

It suffices to derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Substitute using the available equality. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Use the resulting assumption. It suffices to derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Substitute using the available equality. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Establish an intermediate fact. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Establish an intermediate fact. Clear the denominators using the available nonvanishing facts. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Consider separately whether the proposition holds or fails. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem fibre_sum {M : Type} [AddCommMonoid M] (L : PeriodPair) (α ω₀ : ℂ) (S Sq : Finset ℂ)
    (hα : α ≠ 0) (hS : IsKerReps L α S) (hω : ω₀ ∈ L.lattice)
    (hq : IsHalfFibre L α (ω₀ / 2) Sq)
    (f : ℂ → M) (hf : ∀ x y, x - y ∈ L.lattice → f x = f y) :
    f (ω₀ / 2 / α) + ∑ P ∈ S, f (ω₀ / 2 / α + P) = ∑ Q ∈ Sq, f Q + ∑ Q ∈ Sq, f (-Q) := by
  have key := sum_reps L (Finset.insertNone S) (Sq.disjSum Sq) (repA (ω₀ / 2 / α)) repB
    ?_ ?_ ?_ ?_ f hf
  · rw [Finset.sum_insertNone, Finset.sum_disjSum] at key
    simpa [repA, repB] using key
  · intro i hi i' hi' h
    rcases i with _ | P <;> rcases i' with _ | P'
    · rfl
    · exfalso
      have hP' : P' ∈ S := by simpa using hi'
      apply (hS.1 P' hP').2
      have h1 := L.lattice.neg_mem h
      simpa [repA] using h1
    · exfalso
      have hP : P ∈ S := by simpa using hi
      apply (hS.1 P hP).2
      simpa [repA] using h
    · have hP : P ∈ S := by simpa using hi
      have hP' : P' ∈ S := by simpa using hi'
      congr 1
      apply hS.2.1 P hP P' hP'
      simpa [repA] using h
  · intro j hj j' hj' h
    rcases j with Q | Q <;> rcases j' with Q' | Q'
    · have hQ : Q ∈ Sq := by simpa using hj
      have hQ' : Q' ∈ Sq := by simpa using hj'
      congr 1
      exact hq.2.1 Q hQ Q' hQ' (Or.inl (by simpa [repB] using h))
    · exfalso
      have hQ : Q ∈ Sq := by simpa using hj
      have hQ' : Q' ∈ Sq := by simpa using hj'
      have h1 : Q + Q' ∈ L.lattice := by simpa [repB] using h
      have e := hq.2.1 Q hQ Q' hQ' (Or.inr h1)
      subst e
      apply (hq.1 Q hQ).2
      rwa [two_mul]
    · exfalso
      have hQ : Q ∈ Sq := by simpa using hj
      have hQ' : Q' ∈ Sq := by simpa using hj'
      have h1 : Q + Q' ∈ L.lattice := by
        have h2 := L.lattice.neg_mem h
        have e : -(repB (Sum.inr Q) - repB (Sum.inl Q')) = Q + Q' := by simp [repB]; ring
        rwa [e] at h2
      have e := hq.2.1 Q hQ Q' hQ' (Or.inr h1)
      subst e
      apply (hq.1 Q hQ).2
      rwa [two_mul]
    · have hQ : Q ∈ Sq := by simpa using hj
      have hQ' : Q' ∈ Sq := by simpa using hj'
      congr 1
      refine hq.2.1 Q hQ Q' hQ' (Or.inl ?_)
      have h2 := L.lattice.neg_mem h
      have e : -(repB (Sum.inr Q) - repB (Sum.inr Q')) = Q - Q' := by simp [repB]; ring
      rwa [e] at h2
  · intro i hi
    have h1 : α * repA (ω₀ / 2 / α) i - ω₀ / 2 ∈ L.lattice := by
      rcases i with _ | P
      · have e : α * repA (ω₀ / 2 / α) none - ω₀ / 2 = 0 := by
          simp only [repA, Option.elim_none, add_zero]
          field_simp
          ring
        rw [e]
        exact L.lattice.zero_mem
      · have hP : P ∈ S := by simpa using hi
        have e : α * repA (ω₀ / 2 / α) (some P) - ω₀ / 2 = α * P := by
          simp only [repA, Option.elim_some, id]
          field_simp
          ring
        rw [e]
        exact (hS.1 P hP).1
    obtain ⟨Q, hQ, h2 | h2⟩ := hq.2.2 _ h1
    · exact ⟨Sum.inl Q, by simpa using hQ, by simpa [repB] using h2⟩
    · exact ⟨Sum.inr Q, by simpa using hQ, by simpa [repB] using h2⟩
  · intro j hj
    have h1 : α * repB j - ω₀ / 2 ∈ L.lattice := by
      rcases j with Q | Q
      · have hQ : Q ∈ Sq := by simpa using hj
        simpa [repB] using (hq.1 Q hQ).1
      · have hQ : Q ∈ Sq := by simpa using hj
        have h2 := L.lattice.sub_mem (L.lattice.neg_mem (hq.1 Q hQ).1) hω
        have e : -(α * Q - ω₀ / 2) - ω₀ = α * repB (Sum.inr Q) - ω₀ / 2 := by
          simp only [repB, Sum.elim_inr]
          ring
        rwa [e] at h2
    have h3 : α * (repB j - ω₀ / 2 / α) ∈ L.lattice := by
      have e : α * (repB j - ω₀ / 2 / α) = α * repB j - ω₀ / 2 := by
        field_simp
      rwa [e]
    by_cases h4 : repB j - ω₀ / 2 / α ∈ L.lattice
    · exact ⟨none, by simp, by simpa [repA] using h4⟩
    · obtain ⟨P, hP, h5⟩ := hS.2.2 _ h3 h4
      refine ⟨some P, by simpa using hP, ?_⟩
      have e : repB j - repA (ω₀ / 2 / α) (some P) = repB j - ω₀ / 2 / α - P := by
        simp only [repA, Option.elim_some, id]
        ring
      rwa [e]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem fibre_card (L : PeriodPair) (α ω₀ : ℂ) (S Sq : Finset ℂ)
    (hα : α ≠ 0) (hS : IsKerReps L α S) (hω : ω₀ ∈ L.lattice)
    (hq : IsHalfFibre L α (ω₀ / 2) Sq) : 2 * Sq.card = S.card + 1 := by
  have h := fibre_sum L α ω₀ S Sq hα hS hω hq (fun _ => (1 : ℕ)) (fun _ _ _ => rfl)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  omega

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem T_shift_sub (L : PeriodPair) {P : ℂ} (hP : P ∉ L.lattice) :
    T (fun z => L.weierstrassP (z - P)) (taylor0 fun z => L.weierstrassP (z - P)) := by
  have hP' : -P ∉ L.lattice := fun h => hP (by simpa using L.lattice.neg_mem h)
  simpa only [← sub_eq_add_neg] using T_shift L hP'

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem clause1 (L : PeriodPair) {Q : ℂ} (hQ : Q ∉ L.lattice) :
    Formalism.L2.Th1.C.HasSecondLogDeriv (Formalism.L2.Th1.C.wpShift (pSeries L) (L.weierstrassP Q))
      (2 * pSeries L - taylor0 (fun z => L.weierstrassP (z + Q))
        - taylor0 (fun z => L.weierstrassP (z - Q))) := by
  have h := clause2 L (P := Q) (Q := -Q) hQ (by simp)
  simpa only [← sub_eq_add_neg] using h

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem ev_mul_shift_notMem (L : PeriodPair) (α : ℂ) {t : ℂ} (ht : t ∉ L.lattice) :
    ∀ᶠ z in 𝓝 (0 : ℂ), α * z + t ∉ L.lattice := by
  have h1 : Tendsto (fun z : ℂ => α * z) (𝓝 0) (𝓝 0) := by
    have : Tendsto (fun z : ℂ => α * z) (𝓝 0) (𝓝 (α * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rwa [mul_zero] at this
  exact h1.eventually (ev_shift_notMem L ht)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem clauseSum (L : PeriodPair) (α ω₀ : ℂ) (S Sq : Finset ℂ) (hα : α ≠ 0) (hm : MulStable L α)
    (hS : IsKerReps L α S) (hω : ω₀ ∈ L.lattice) (ht : ω₀ / 2 ∉ L.lattice)
    (hq : IsHalfFibre L α (ω₀ / 2) Sq) :
    C (α ^ 2) * rescale α (taylor0 fun z => L.weierstrassP (z + ω₀ / 2))
      = ∑ Q : Sq, ((taylor0 fun z => L.weierstrassP (z + (Q : ℂ)))
          + taylor0 fun z => L.weierstrassP (z - (Q : ℂ))) - C (∑ P ∈ S, L.weierstrassP P) := by
  have h1 := T.mul taylor_ring (T.const taylor_ring (α ^ 2)) (T.rescale α (T_shift L ht))
  have h2 := T.sub (T.sum (Finset.univ : Finset Sq)
    (fun Q z => L.weierstrassP (z + (Q : ℂ)) + L.weierstrassP (z - (Q : ℂ)))
    (fun Q => (taylor0 fun z => L.weierstrassP (z + (Q : ℂ)))
      + taylor0 fun z => L.weierstrassP (z - (Q : ℂ)))
    (fun Q _ => T.add taylor_ring (T_shift L (notMem_of_two (hq.1 Q Q.2).2))
      (T_shift_sub L (notMem_of_two (hq.1 Q Q.2).2))))
    (T.const taylor_ring (∑ P ∈ S, L.weierstrassP P))
  refine T.unique h1 h2 ?_
  filter_upwards [(ev_mul_shift_notMem L α ht).filter_mono nhdsWithin_le_nhds] with z hz
  have e : α * (z + ω₀ / 2 / α) = α * z + ω₀ / 2 := by field_simp
  have h3 := isogenyP L α S hα hm hS (z + ω₀ / 2 / α) (by rwa [e])
  rw [e, Finset.sum_sub_distrib] at h3
  have h4 := fibre_sum L α ω₀ S Sq hα hS hω hq (fun c => L.weierstrassP (z + c)) (by
    intro x y hxy
    apply wp_congr L
    have e2 : z + x - (z + y) = x - y := by ring
    rwa [e2])
  rw [Finset.sum_coe_sort Sq (fun Q => L.weierstrassP (z + Q) + L.weierstrassP (z - Q)),
    Finset.sum_add_distrib]
  simp only [← sub_eq_add_neg, ← add_assoc] at h4
  linear_combination h3 + h4

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem fibre_integer_instance_holds : FibreZInstance := by
  intro L α ω₀ S Sq hα hm hS hω ht hq
  refine ⟨fibre_card L α ω₀ S Sq hα hS hω hq, ?_, clauseSum L α ω₀ S Sq hα hm hS hω ht hq⟩
  intro Q
  exact clause1 L (notMem_of_two (hq.1 Q Q.2).2)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result.

Replace the relevant objects with their definitions. Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem half_shift_series_holds : HalfShiftSeries := by
  intro L ω₀ hω ht
  set t : ℂ := ω₀ / 2 with htd
  have h2t : 2 * t ∈ L.lattice := by rw [htd, two_mul_half]; exact hω
  have h1 := T.mul taylor_ring (T.sub (T_shift L ht) (T.const taylor_ring (L.weierstrassP t)))
    (T_fP L t)
  have h2 := T.mul taylor_ring (T.const taylor_ring (3 * L.weierstrassP t ^ 2 - L.g₂ / 4))
    (T.pow taylor_ring (T.id taylor_ring) 2)
  have h3 := T.unique h1 h2 (by
    filter_upwards [ev_notMem L, (ev_shift_notMem L ht).filter_mono nhdsWithin_le_nhds] with z hz hzt
    have hz0 : z ≠ 0 := ne_zero_of_notMem L hz
    rw [fP_eq L t hz0]
    have h := halfShift L t z ht h2t hz hzt
    linear_combination z ^ 2 * h)
  have h4 := GCob.wOf_mul (L.weierstrassP t) (pSeries L)
  have hU : (1 + X ^ 2 * pSeries L - C (L.weierstrassP t) * X ^ 2 : PowerSeries ℂ) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    simp at this
  apply mul_right_cancel₀ hU
  unfold Formalism.L2.Th1.C.wpShift at h3
  linear_combination h3 - C (3 * L.weierstrassP t ^ 2 - L.g₂ / 4) * h4

end Formalism.L2.Th1.B.Fib
