import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalAtNilpotentXEqCoordinateStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.BoxMonomials

variable {d : ℕ}

noncomputable def boxPt {q : ℕ} (a : Fin d → Fin q) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem boxPt_apply {q : ℕ} (a : Fin d → Fin q) (i : Fin d) : boxPt a i = a i := by
  simp [boxPt]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem boxPt_injective {q : ℕ} : Function.Injective (boxPt (d := d) (q := q)) := by
  intro a b h
  funext i
  exact Fin.ext (by simpa [boxPt_apply] using DFunLike.congr_fun h i)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem exists_boxPt {q : ℕ} (β : Fin d →₀ ℕ) (h : ∀ i, β i < q) :
    ∃ a : Fin d → Fin q, boxPt a = β :=
  ⟨fun i => ⟨β i, h i⟩, by ext i; simp [boxPt_apply]⟩

end GlobalTheory.BoxMonomials

open GlobalTheory.BoxMonomials in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem GlobalTheory.coeff_eq_zero_of_evA_eq_zero_of_le_finrank :
    ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (d q : ℕ)
      (x : Fin d → A) (hx : ∀ i, IsNilpotent (x i)) (J : Ideal A),
      Function.Surjective (MvPolynomial.aeval (R := K) x) → (∀ i, x i ^ q ∈ J) →
      q ^ d ≤ Module.finrank K (A ⧸ J) → ∀ f : MvPowerSeries (Fin d) K, evA K x hx f = 0 →
      ∀ α : Fin d →₀ ℕ, α.degree < q → coeff α f = 0 := by
  intro K A _ _ _ _ d q x hx J hsurj hJ hdim f hf α hα
  classical
  set E : MvPowerSeries (Fin d) K →ₐ[K] A ⧸ J := (Ideal.Quotient.mkₐ K J).comp (evA K x hx)
    with hE
  have hEapp : ∀ y, E y = Ideal.Quotient.mk J (evA K x hx y) := fun y => rfl
  have hEX : ∀ i, evA K x hx (X i) = x i := fun i => GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate K (Fin d) A x hx i
  have hEXq : ∀ i g, E (X i ^ q * g) = 0 := by
    intro i g
    rw [hEapp, Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, hEX]
    exact J.mul_mem_right _ (hJ i)
  have hmono : ∀ β : Fin d →₀ ℕ, ∀ i, q ≤ β i → ∀ c : K, E (monomial β c) = 0 := by
    intro β i hi c
    have : monomial β c = X i ^ q * monomial (β - Finsupp.single i q) c := by
      rw [X_pow_eq, monomial_mul_monomial, one_mul,
        add_tsub_cancel_of_le (Finsupp.single_le_iff.2 hi)]
    rw [this]
    exact hEXq i _
  set v : (Fin d → Fin q) → A ⧸ J := fun a => E (monomial (boxPt a) 1) with hv
  have hcoe : ∀ P : MvPolynomial (Fin d) K,
      Ideal.Quotient.mk J (MvPolynomial.aeval x P) = E (P : MvPowerSeries (Fin d) K) := by
    intro P
    have : (Ideal.Quotient.mkₐ K J).comp (MvPolynomial.aeval x) =
        E.comp (MvPolynomial.coeToMvPowerSeries.algHom K) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [hEapp, hEX]
    exact DFunLike.congr_fun this P
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    rintro y -
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨P, rfl⟩ := hsurj a'
    rw [hcoe]
    induction P using MvPolynomial.induction_on' with
    | monomial β c =>
      rw [MvPolynomial.coe_monomial]
      by_cases hb : ∀ i, β i < q
      · obtain ⟨a, rfl⟩ := exists_boxPt β hb
        have : monomial (boxPt a) c = c • monomial (boxPt a) (1 : K) := by
          rw [← map_smul, smul_eq_mul, mul_one]
        rw [this, map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      · push_neg at hb
        obtain ⟨i, hi⟩ := hb
        rw [hmono β i hi c]
        exact Submodule.zero_mem _
    | add P Q hP hQ =>
      rw [MvPolynomial.coe_add, map_add]
      exact Submodule.add_mem _ hP hQ
  have hcard : Fintype.card (Fin d → Fin q) = Module.finrank K (A ⧸ J) := by
    apply le_antisymm
    · simpa [Fintype.card_fun] using hdim
    · have h1 := finrank_range_le_card (R := K) v
      have h2 : Set.finrank K (Set.range v) = Module.finrank K (A ⧸ J) := by
        unfold Set.finrank
        rw [eq_top_iff.2 hspan, finrank_top]
      omega
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard
  set P : MvPowerSeries (Fin d) K :=
    ∑ a : Fin d → Fin q, coeff (boxPt a) f • monomial (boxPt a) (1 : K) with hP
  have hPcoeff : ∀ a : Fin d → Fin q, coeff (boxPt a) P = coeff (boxPt a) f := by
    intro a
    rw [hP, map_sum, Finset.sum_eq_single a]
    · simp [coeff_monomial]
    · intro b _ hb
      simp [coeff_monomial, boxPt_injective.ne (Ne.symm hb)]
    · simp
  set h : MvPowerSeries (Fin d) K := f - P with hh
  let hi : Fin d → MvPowerSeries (Fin d) K := fun i β =>
    if q ≤ β i ∧ ∀ j < i, β j < q then coeff β h else 0
  have hic : ∀ i β, coeff β (hi i) = if q ≤ β i ∧ ∀ j < i, β j < q then coeff β h else 0 :=
    fun i β => by rw [coeff_apply]
  have hdiv : ∀ i, X i ^ q ∣ hi i := by
    intro i
    rw [X_pow_dvd_iff]
    intro m hm
    rw [hic, if_neg]
    omega
  have hsum : h = ∑ i, hi i := by
    ext β
    rw [map_sum]
    simp only [hic]
    by_cases hb : ∀ i, β i < q
    · obtain ⟨a, rfl⟩ := exists_boxPt β hb
      have : coeff (boxPt a) h = 0 := by rw [hh, map_sub, hPcoeff, sub_self]
      rw [this]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      have := hb i
      omega
    · push_neg at hb
      obtain ⟨i0, hi0mem, hmin⟩ := (Finset.univ.filter (fun i => q ≤ β i)).exists_min_image id
        (by obtain ⟨i, hi⟩ := hb; exact ⟨i, by simp [hi]⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hi0mem hmin
      rw [Finset.sum_eq_single i0]
      · rw [if_pos]
        refine ⟨hi0mem, fun j hj => ?_⟩
        by_contra hc
        exact absurd (hmin j (by omega)) (not_le.2 hj)
      · intro j _ hj
        rw [if_neg]
        rintro ⟨hjq, hjlt⟩
        rcases lt_or_gt_of_ne hj with hlt | hlt
        · exact absurd (hmin j hjq) (not_le.2 hlt)
        · have := hjlt i0 hlt
          omega
      · simp
  have hEh : E h = 0 := by
    rw [hsum, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    obtain ⟨g, hg⟩ := hdiv i
    rw [hg]
    exact hEXq i g
  have hEf : E f = 0 := by rw [hEapp, hf, map_zero]
  have hfP : f = P + h := by rw [hh]; ring
  have hzero : ∑ a : Fin d → Fin q, coeff (boxPt a) f • v a = 0 := by
    have : E P = ∑ a : Fin d → Fin q, coeff (boxPt a) f • v a := by
      rw [hP, map_sum]
      simp only [map_smul, hv]
    rw [← this, ← hEf, hfP, map_add, hEh, add_zero]
  have hall := Fintype.linearIndependent_iff.1 hli _ hzero
  obtain ⟨a, rfl⟩ := exists_boxPt α (fun i => lt_of_le_of_lt (Finsupp.le_degree i α) hα)
  exact hall a
