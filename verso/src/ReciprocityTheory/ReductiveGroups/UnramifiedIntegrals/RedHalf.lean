import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

variable {L : PeriodPair} {α : ℂ} {T : Finset ℂ}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsHalfReps.notMem (h : IsHalfReps L α T) {P : ℂ} (hP : P ∈ T) : P ∉ L.lattice := by
  intro hPL
  apply (h.1 P hP).2
  rw [two_mul]
  exact add_mem hPL hPL

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Substitute using the available equality. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Substitute using the available equality.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Substitute using the available equality. A detailed English derivation is pending.
-/
theorem IsHalfReps.kerReps (h : IsHalfReps L α T) :
    IsKerReps L α (T ∪ T.image (fun P => -P)) ∧ Disjoint T (T.image (fun P => -P)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact ⟨(h.1 P hP).1, h.notMem hP⟩
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      refine ⟨?_, ?_⟩
      · rw [mul_neg]; exact neg_mem (h.1 Q hQ).1
      · intro hn; exact h.notMem hQ (by simpa using neg_mem hn)
  · intro P hP Q hQ hPQ
    rcases Finset.mem_union.mp hP with hP | hP <;> rcases Finset.mem_union.mp hQ with hQ | hQ
    · exact h.2.1 P hP Q hQ (Or.inl hPQ)
    · obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have e : P = Q' := h.2.1 P hP Q' hQ' (Or.inr (by simpa using hPQ))
      subst e
      exact absurd (by rw [two_mul]; simpa using hPQ) (h.1 P hP).2
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      have h1 : P' + Q ∈ L.lattice := by
        have := neg_mem hPQ
        have e : -(-P' - Q) = P' + Q := by ring
        rwa [e] at this
      have e : P' = Q := h.2.1 P' hP' Q hQ (Or.inr h1)
      subst e
      exact absurd (by rw [two_mul]; exact h1) (h.1 P' hP').2
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
      obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
      have h1 : P' - Q' ∈ L.lattice := by
        have := neg_mem hPQ
        have e : -(-P' - -Q') = P' - Q' := by ring
        rwa [e] at this
      rw [h.2.1 P' hP' Q' hQ' (Or.inl h1)]
  · intro z hz hzL
    obtain ⟨P, hP, hzP | hzP⟩ := h.2.2 z hz hzL
    · exact ⟨P, Finset.mem_union_left _ hP, hzP⟩
    · exact ⟨-P, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hP), by simpa using hzP⟩
  · rw [Finset.disjoint_left]
    intro P hP hP'
    obtain ⟨Q, hQ, hQP⟩ := Finset.mem_image.mp hP'
    have h0 : P + Q ∈ L.lattice := by rw [← hQP]; simp
    have e : P = Q := h.2.1 P hP Q hQ (Or.inr h0)
    subst e
    exact (h.1 P hP).2 (by rw [two_mul]; exact h0)

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsHalfReps.card (h : IsHalfReps L α T) (hα : α ≠ 0) (hs : MulStable L α) :
    2 * (T.card : ℝ) + 1 = Complex.normSq α := by
  have h1 := kerRepsCard L α _ hα hs h.kerReps.1
  rw [Finset.card_union_of_disjoint h.kerReps.2, Finset.card_image_of_injective _ neg_injective] at h1
  rw [← h1]; push_cast; ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem IsHalfReps.injOn (h : IsHalfReps L α T) : Set.InjOn L.weierstrassP (T : Set ℂ) := by
  intro P hP Q hQ hPQ
  exact h.2.1 P hP Q hQ ((pInjective L P Q (h.notMem hP) (h.notMem hQ)).mp hPQ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IsHalfReps.card_xsOf (h : IsHalfReps L α T) : (xsOf L T).card = T.card :=
  Finset.card_image_of_injOn h.injOn

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem IsHalfReps.fW_ne (h : IsHalfReps L α T) {x : ℂ} (hx : x ∈ xsOf L T) : fW L.g₂ L.g₃ x ≠ 0 := by
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
  have hPL := h.notMem hP
  unfold fW
  rw [← L.derivWeierstrassP_sq P hPL]
  exact pow_ne_zero 2 (fun h0 => (h.1 P hP).2 ((pDerivZero L P hPL).mp h0))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem IsHalfReps.mem_xsOf (h : IsHalfReps L α T) (hs : MulStable L α) {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassP z ∈ xsOf L T ↔ α * z ∈ L.lattice := by
  constructor
  · intro hx
    obtain ⟨P, hP, hPz⟩ := Finset.mem_image.mp hx
    rcases (pInjective L z P hz (h.notMem hP)).mp hPz.symm with h1 | h1
    · have e : α * z = α * (z - P) + α * P := by ring
      rw [e]; exact add_mem (hs _ h1) (h.1 P hP).1
    · have e : α * z = α * (z + P) - α * P := by ring
      rw [e]; exact sub_mem (hs _ h1) (h.1 P hP).1
  · intro hk
    obtain ⟨P, hP, h1⟩ := h.2.2 z hk hz
    exact Finset.mem_image.mpr ⟨P, hP, ((pInjective L z P hz (h.notMem hP)).mpr h1).symm⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ker_norm (hs : MulStable L α) {N : ℕ} (hN : Complex.normSq α = N) {z : ℂ}
    (hz : α * z ∈ L.lattice) : (N : ℂ) * z ∈ L.lattice := by
  obtain ⟨t, n, ht, -, -⟩ := mulStableIntegral L α hs
  have h1 : (N : ℂ) = α * (starRingEnd ℂ) α := by
    rw [Complex.mul_conj, hN]; simp
  have e : (N : ℂ) * z = t • (α * z) - α * (α * z) := by
    rw [h1, zsmul_eq_mul, ← ht]; ring
  rw [e]
  exact sub_mem (zsmul_mem hz t) (hs _ hz)

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem halfReps_exist (L : PeriodPair) (α : ℂ) (hα : α ≠ 0) (hs : MulStable L α) (N : ℕ)
    (hN : Complex.normSq α = N) (hodd : Odd N) : ∃ T : Finset ℂ, IsHalfReps L α T := by
  obtain ⟨S, hS⟩ := kerRepsExist L α hα hs
  let g : ℂ → ℂ := fun x => Classical.epsilon (fun Q => Q ∈ S ∧ L.weierstrassP Q = x)
  have hg : ∀ P ∈ S, g (L.weierstrassP P) ∈ S ∧ L.weierstrassP (g (L.weierstrassP P)) = L.weierstrassP P :=
    fun P hP => Classical.epsilon_spec (p := fun Q => Q ∈ S ∧ L.weierstrassP Q = L.weierstrassP P) ⟨P, hP, rfl⟩
  refine ⟨(S.image L.weierstrassP).image g, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hx
    have hk := hS.1 _ (hg P0 hP0).1
    refine ⟨hk.1, fun h2 => hk.2 ?_⟩
    obtain ⟨k, hk'⟩ := hodd
    have h3 := ker_norm hs hN hk.1
    have e : g (L.weierstrassP P0) = (N : ℂ) * g (L.weierstrassP P0) - (k : ℤ) • (2 * g (L.weierstrassP P0)) := by
      rw [hk', zsmul_eq_mul]; push_cast; ring
    rw [e]
    exact sub_mem h3 (zsmul_mem h2 _)
  · intro P hP Q hQ hPQ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hQ
    obtain ⟨Q0, hQ0, rfl⟩ := Finset.mem_image.mp hy
    have h1 := (pInjective L _ _ (hS.1 _ (hg P0 hP0).1).2 (hS.1 _ (hg Q0 hQ0).1).2).mpr hPQ
    rw [(hg P0 hP0).2, (hg Q0 hQ0).2] at h1
    rw [h1]
  · intro z hz hzL
    obtain ⟨P0, hP0, h0⟩ := hS.2.2 z hz hzL
    refine ⟨g (L.weierstrassP P0),
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hP0), ?_⟩
    apply (pInjective L _ _ hzL (hS.1 _ (hg P0 hP0).1).2).mp
    rw [(hg P0 hP0).2]
    exact (pInjective L _ _ hzL (hS.1 _ hP0).2).mpr (Or.inl h0)

end ReciprocityTheory.ChartRestriction.L1
