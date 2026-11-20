import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.FinrankInfKerAddOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.ExistsTraceNeZero

open Finset Module

namespace DensInertW

open DensInertW.Sub

section
variable {L : Type} [Field L]

/- English proof (translation)
Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Proceed by induction. Treat this case separately. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately.

Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem diag_orth_family {m q : ℕ} {B : Matrix (Fin m) (Fin m) L}
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hB : IsHerm q B) (htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ q ≠ 0) :
    ∀ (d : ℕ) (W : Submodule L (Fin m → L)), finrank L W = d →
      ∃ (v : Fin d → Fin m → L) (r : ℕ), r ≤ d ∧ (∀ i, v i ∈ W) ∧ LinearIndependent L v ∧
        (∀ i j, i ≠ j → hf q B (v i) (v j) = 0) ∧ (∀ i, hf q B (v i) (v i) ≠ 0 ↔ i.val < r) := by
  have hq : q ≠ 0 := by
    rintro rfl
    have h := hinv 0
    simp at h

  have iso : ∀ (d : ℕ) (W : Submodule L (Fin m → L)), finrank L W = d → (∀ e ∈ W, hf q B e e = 0) →
      ∃ (v : Fin d → Fin m → L) (r : ℕ), r ≤ d ∧ (∀ i, v i ∈ W) ∧ LinearIndependent L v ∧
        (∀ i j, i ≠ j → hf q B (v i) (v j) = 0) ∧ (∀ i, hf q B (v i) (v i) ≠ 0 ↔ i.val < r) := by
    intro d W hW h0
    have hz := hf_eq_zero_of_diag hadd hinv hB htr W h0
    let b := Module.finBasisOfFinrankEq L W hW
    refine ⟨fun i => (b i : Fin m → L), 0, Nat.zero_le _, fun i => (b i).2, ?_,
      fun i j _ => hz _ (b i).2 _ (b j).2, fun i => ?_⟩
    · exact b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    · simp [hz _ (b i).2 _ (b i).2]
  intro d
  induction d with
  | zero =>
    intro W hW
    by_cases h : ∃ e ∈ W, hf q B e e ≠ 0
    · obtain ⟨e, he, hee⟩ := h
      have := finrank_perp_aniso W e he hee
      omega
    · push_neg at h
      exact iso 0 W hW h
  | succ d ih =>
    intro W hW
    by_cases h : ∃ e ∈ W, hf q B e e ≠ 0
    · obtain ⟨e, he, hee⟩ := h
      have hd : finrank L ↥(W ⊓ LinearMap.ker (hfL q B e)) = d := by
        have := finrank_perp_aniso W e he hee
        omega
      obtain ⟨v, r, hr, hvW, hli, horth, hdiag⟩ := ih _ hd
      have hvk : ∀ i, hf q B (v i) e = 0 := fun i => by
        rw [← hfL_apply]
        exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp (hvW i)).2
      have hek : ∀ i, hf q B e (v i) = 0 := fun i => by
        rw [hf_symm hadd hinv hB, hvk i, zero_pow hq]
      refine ⟨Fin.cons e v, r + 1, by omega, fun i => ?_, ?_, fun i j hij => ?_, fun i => ?_⟩
      · induction i using Fin.cases with
        | zero => simpa using he
        | succ j => simpa using (Submodule.mem_inf.mp (hvW j)).1
      · rw [linearIndependent_fin_cons]
        refine ⟨hli, fun hmem => hee ?_⟩
        have hle : Submodule.span L (Set.range v) ≤ LinearMap.ker (hfL q B e) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact (Submodule.mem_inf.mp (hvW i)).2
        have h1 := LinearMap.mem_ker.mp (hle hmem)
        rwa [hfL_apply] at h1
      · induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => simpa using hek j
        | succ i =>
          induction j using Fin.cases with
          | zero => simpa using hvk i
          | succ j => simpa using horth i j fun h => hij (by rw [h])
      · induction i using Fin.cases with
        | zero => simpa using hee
        | succ i =>
          simp only [Fin.cons_succ, Fin.val_succ]
          rw [hdiag i]
          omega
    · push_neg at h
      exact iso _ W hW h

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem diag_of_hyps {m q : ℕ} (B : Matrix (Fin m) (Fin m) L)
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hB : IsHerm q B) (htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ q ≠ 0) :
    ∃ P : Matrix (Fin m) (Fin m) L, IsUnit P.det ∧ ∃ (w : Fin m → L) (r : ℕ), r ≤ m ∧
        P * B * (P.map (fun y => y ^ q)).transpose = Matrix.diagonal w ∧
        (∀ i, w i ≠ 0 ↔ i.val < r) ∧ (∀ i, w i ^ q = w i) := by
  obtain ⟨v, r, hr, -, hli, horth, hdiag⟩ := diag_orth_family hadd hinv hB htr m ⊤
    (by rw [finrank_top, Module.finrank_fin_fun])
  refine ⟨Matrix.of fun i => v i, ?_, fun i => hf q B (v i) (v i), r, hr, ?_, hdiag, fun i => ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli)
  · ext i j
    have e : (Matrix.of (fun i => v i) * B * ((Matrix.of fun i => v i).map fun y => y ^ q).transpose) i j =
        hf q B (v i) (v j) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, hf,
        Finset.sum_mul]
      exact Finset.sum_comm
    rw [e, Matrix.diagonal_apply]
    split_ifs with h
    · rw [h]
    · exact horth i j h
  · exact (hf_symm hadd hinv hB (v i) (v i)).symm
end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Evaluate the numerical expressions. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem hermitianDiagonalization : Diag := by
  intro K L _ _ _ _ _ h2 m B hB
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hadd : ∀ a b : L, (a + b) ^ Fintype.card K = a ^ Fintype.card K + b ^ Fintype.card K := fun a b => by
    rw [hcard]
    exact add_pow_char_pow a b _ _
  have hcL : Fintype.card L = Fintype.card K ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := L), h2]
  have hinv : ∀ a : L, (a ^ Fintype.card K) ^ Fintype.card K = a := fun a => by
    rw [← pow_mul, ← sq, ← hcL, FiniteField.pow_card]
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card

  have htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ Fintype.card K ≠ 0 := by
    intro z hz
    by_contra hall
    push_neg at hall
    let P : Polynomial L := Polynomial.X ^ Fintype.card K + Polynomial.X
    have hroot : ∀ y : L, P.eval y = 0 := fun y => by
      have h := hall (y / z)
      rw [div_mul_cancel₀ y hz] at h
      simp only [P, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      linear_combination h
    have hP0 : P ≠ 0 := by
      intro h0
      have h := congrArg (Polynomial.coeff · 1) h0
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X_one,
        Polynomial.coeff_zero] at h
      split_ifs at h with hh
      · omega
      · norm_num at h
    have hdeg : P.natDegree ≤ Fintype.card K :=
      (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) (by simp; omega))
    have hsub : (Finset.univ : Finset L).val ≤ P.roots :=
      (Multiset.le_iff_subset Finset.univ.nodup).mpr fun y _ => (Polynomial.mem_roots hP0).mpr (hroot y)
    have hc := (Multiset.card_le_card hsub).trans ((Polynomial.card_roots' P).trans hdeg)
    rw [Finset.card_val, Finset.card_univ, hcL] at hc
    nlinarith
  exact diag_of_hyps B hadd hinv hB htr

end DensInertW
