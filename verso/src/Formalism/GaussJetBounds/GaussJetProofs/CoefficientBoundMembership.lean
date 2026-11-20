import Formalism.GaussJetBounds.StatementS

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial Formalism.IncomingBounds

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma det_sum_mul_expand {S : Type*} [CommRing S] {p n : ℕ} (u : Fin p → Fin n → S)
    (y : Fin n → Fin p → S) :
    (Matrix.of fun (r r' : Fin p) => ∑ a, u r a * y a r').det =
      ∑ A : Fin p → Fin n, (∏ r', y (A r') r') *
        (Matrix.of fun (r r' : Fin p) => u r (A r')).det := by
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun σ _ => ?_
  ring

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.
-/
lemma minorProd_expand {R : Type} [CommRing R] {ι : Type} {N0 N1 Cn : ℕ}
    (x : Fin N0 → Fin N0 → R) (Y : Fin N0 → Fin N1 → MvPolynomial ι R) (p : Fin Cn → ℕ)
    (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1) :
    minorProd (fun i b => ∑ a, C (x i a) * Y a b) p hp I =
      ∑ A ∈ Fintype.piFinset (fun c => (Finset.univ : Finset (Fin (p c) → Fin N0))),
        (∏ c, ∏ r', Y (A c r') (I c r')) *
          C (∏ c, (Matrix.of fun (r r' : Fin (p c)) =>
            x ⟨r.val, lt_of_lt_of_le r.isLt (hp c)⟩ (A c r')).det) := by
  simp only [minorProd, det_sum_mul_expand]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.prod_mul_distrib, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  congr 1

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
lemma exists_monomial_prod {R ι α : Type} [CommSemiring R] (s : Finset α)
    (f : α → MvPolynomial ι R) (hf : ∀ i ∈ s, ∃ e, f i = monomial e 1) :
    ∃ e, ∏ i ∈ s, f i = monomial e 1 := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => ⟨0, ?_⟩) ?_
  · rw [Finset.prod_empty, ← MvPolynomial.C_1, MvPolynomial.C_apply]
  intro a s ha ih hf
  obtain ⟨e1, h1⟩ := hf a (Finset.mem_insert_self a s)
  obtain ⟨e2, h2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
  exact ⟨e1 + e2, by rw [Finset.prod_insert ha, h1, h2, MvPolynomial.monomial_mul, mul_one]⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma coeff_sum_mem_lemma {K : Type} [Field K] {σ ι α : Type}
    (M : Submodule K (MvPolynomial σ K)) (S : Finset α) (f : α → MvPolynomial ι (MvPolynomial σ K))
    (hf : ∀ A ∈ S, ∃ e Q, Q ∈ M ∧ f A = MvPolynomial.monomial e Q) (κ : ι →₀ ℕ) :
    MvPolynomial.coeff κ (∑ A ∈ S, f A) ∈ M := by
  classical
  rw [MvPolynomial.coeff_sum]
  refine Submodule.sum_mem _ fun A hA => ?_
  obtain ⟨e, Q, hQ, hfA⟩ := hf A hA
  rw [hfA, MvPolynomial.coeff_monomial]
  split_ifs
  · exact hQ
  · exact Submodule.zero_mem _

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma jetPairPoly_mem_lemma_2 {K : Type} [Field K] {σ ι : Type}
    (M : Submodule K (MvPolynomial σ K)) (P : MvPolynomial ι (MvPolynomial σ K))
    (Th : MvPowerSeries ι K) (hP : ∀ κ, MvPolynomial.coeff κ P ∈ M) :
    jetPairPoly P Th ∈ M := by
  unfold jetPairPoly
  refine Submodule.sum_mem _ fun κ _ => ?_
  rw [mul_comm (MvPolynomial.coeff κ P), ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (hP κ)

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
private lemma prod_mul_C_lemma_3 {K : Type} [Field K] {σ ι α : Type}
    (M : Submodule K (MvPolynomial σ K)) (s : Finset α) (f : α → MvPolynomial ι (MvPolynomial σ K))
    (Q : MvPolynomial σ K) (hf : ∀ a ∈ s, ∃ e, f a = MvPolynomial.monomial e 1) (hQ : Q ∈ M) :
    ∃ e Q', Q' ∈ M ∧ (∏ a ∈ s, f a) * MvPolynomial.C Q = MvPolynomial.monomial e Q' := by
  obtain ⟨e, he⟩ := exists_monomial_prod s f hf
  exact ⟨e, Q, hQ, by rw [he, mul_comm, MvPolynomial.C_mul_monomial, mul_one]⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem coefficient_bound_membership : CBMem := by
  unfold CBMem
  intro K _ d N0 N1 _ colN p hp I Th
  unfold frameJet nablaK
  refine jetPairPoly_mem_lemma_2 _ _ _ fun κ => ?_
  simp only [minorProd_expand]
  rw [Finset.prod_univ_sum]
  refine coeff_sum_mem_lemma _ _ _ (fun A _ => ?_) κ
  rw [Finset.prod_mul_distrib, ← map_prod]
  refine prod_mul_C_lemma_3 _ _ _ _ (fun s _ => ?_) ?_
  · exact exists_monomial_prod _ _ fun c _ => exists_monomial_prod _ _ fun r' _ => ⟨_, rfl⟩
  · refine Submodule.subset_span ?_
    simp only [xMinors, Set.mem_setOf_eq]
    exact ⟨A, rfl⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem thmAWeyl_of (hG : ThmAGauss) : ThmAWeyl := by
  unfold ThmAWeyl
  unfold ThmAGauss at hG
  intro l _ d N0 N1 _ h3 h2 hE K0 hU ζ hζ be hB g hg0 hgs U hUi ε hε TT colN p hp hp1 I nu1 nu2 size
    h1 h2' h3' a ha hsa hlog hSB c hc
  have hbd := hG l d N0 N1 h3 h2 hE K0 hU ζ hζ be hB g hg0 hgs U hUi ε hε TT colN p hp hp1 I nu1
    nu2 size h1 h2' h3' a ha hsa hlog
  have hCB := coefficient_bound_membership
  unfold CBMem at hCB
  have hmem := hCB _ d N0 N1 colN p hp I (thetaZ g U ε be)
  unfold SBSat at hSB
  refine hSB _ (Submodule.smul_mem _ c⁻¹ hmem) fun n => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul, norm_inv]
  have hx := le_trans (hbd n) hc
  rcases (norm_nonneg c).eq_or_lt with h0 | hpos
  · rw [← h0, inv_zero, zero_mul]
    exact zero_le_one
  · calc _ ≤ ‖c‖⁻¹ * ‖c‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (norm_nonneg c))
      _ = 1 := inv_mul_cancel₀ hpos.ne'

end Formalism.DworkPowerSeriesWeights
