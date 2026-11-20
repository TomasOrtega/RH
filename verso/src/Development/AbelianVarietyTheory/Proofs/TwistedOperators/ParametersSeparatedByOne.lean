import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
open Formalism.L2.Theta

namespace GlobalTheory.WordSep

open GlobalTheory.SignedHC

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
private theorem v_le {G : GridData} {i j : ℕ} (hi : 2 ≤ i) (hij : i ≤ j) (hj : j ≤ G.k) : G.v j ≤ G.v i := by
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (G.v_anti i j hi h hj).le

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
private theorem b_ge {G : GridData} {l : ℕ} (hl : 1 ≤ l) (hlm : l ≤ G.m) : G.b 1 ≤ G.b l := by
  rcases hl.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (G.b_mono 1 l le_rfl h hlm).le

/- English proof (translation)
Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Extract witnesses or component facts from the available result.

Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Substitute using the available equality. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis.

Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Substitute using the available equality. Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Combine the linear equalities and inequalities to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
-/
theorem sep_rat {G : GridData} (hga : 0 < G.ga)
    (hgap : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) (hb : 2 ≤ G.v G.k + G.b 1)
    {x y : ℚ} (hx : (∃ l, l ≤ G.m ∧ x = G.a l) ∨ ∃ j, 2 ≤ j ∧ j ≤ G.k ∧ x = G.vHalf j)
    (hy : (∃ j, 2 ≤ j ∧ j ≤ G.k ∧ y = G.v j) ∨ ∃ l, 1 ≤ l ∧ l ≤ G.m ∧ y = -(G.b l : ℚ)) :
    (y < x → y + 1 < x) ∧ x ≠ y := by
  have hk := G.two_le_k
  rcases hx with ⟨l, hl, rfl⟩ | ⟨j, hj2, hjk, rfl⟩
  · have hal : (G.v 2 : ℚ) + 3 / 2 ≤ G.a l := by
      unfold GridData.a
      have h1 : (1 : ℚ) ≤ (G.m : ℚ) + 1 - l := by
        have : (l : ℚ) ≤ G.m := by exact_mod_cast hl
        linarith
      have h2 : (1 : ℚ) ≤ G.ga := by exact_mod_cast hga
      nlinarith
    obtain ⟨z, hz, hzle⟩ : ∃ z : ℤ, y = z ∧ z ≤ G.v 2 := by
      rcases hy with ⟨j, hj2, hjk, rfl⟩ | ⟨l', hl1, hlm, rfl⟩
      · exact ⟨_, rfl, v_le le_rfl hj2 hjk⟩
      · refine ⟨-G.b l', by push_cast; ring, ?_⟩
        have := b_ge (G := G) hl1 hlm
        have := v_le (G := G) le_rfl hk le_rfl
        linarith
    have : (z : ℚ) ≤ G.v 2 := by exact_mod_cast hzle
    subst hz
    constructor
    · intro _; linarith
    · intro h; linarith
  · obtain ⟨z, hz, hzc⟩ : ∃ z : ℤ, y = z ∧ (G.v j ≤ z ∨ z ≤ G.v j - 2) := by
      rcases hy with ⟨j', hj2', hjk', rfl⟩ | ⟨l', hl1, hlm, rfl⟩
      · refine ⟨_, rfl, ?_⟩
        rcases le_or_gt j' j with h | h
        · exact Or.inl (v_le hj2' h hjk)
        · right
          have h1 := v_le (G := G) (by omega : 2 ≤ j + 1) (by omega : j + 1 ≤ j') hjk'
          have h2 := hgap j hj2 (by omega)
          linarith
      · refine ⟨-G.b l', by push_cast; ring, Or.inr ?_⟩
        have := b_ge (G := G) hl1 hlm
        have := v_le (G := G) hj2 hjk le_rfl
        linarith
    subst hz
    unfold GridData.vHalf
    rcases hzc with h | h
    · have : (G.v j : ℚ) ≤ z := by exact_mod_cast h
      constructor
      · intro h'; linarith
      · intro h'; linarith
    · have : (z : ℚ) ≤ G.v j - 2 := by exact_mod_cast h
      constructor
      · intro _; linarith
      · intro h'; linarith

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative.

Prove the second alternative. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative. Reduce the conclusion to the remaining proof obligations.

Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem word_sep : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) →
    2 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' →
    (∀ a i, mu i < lam a → mu i + 1 < lam a) ∧ ∀ a i, lam a ≠ mu i := by
  rintro G n lam ε mu ε' hga hgap hb ⟨-, q, hq, hS⟩ ⟨-, q', hq', hT⟩
  have key : ∀ a i, (q' i < q a → q' i + 1 < q a) ∧ q a ≠ q' i := by
    intro a i
    have ha : (q a, ε a) ∈ G.lam := by
      rw [← G.parPi_zero, hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    have hi : (q' i, ε' i) ∈ G.parD0 := by
      rw [hT]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    refine sep_rat hga hgap hb ?_ ?_
    · rcases GridData.mem_lam.1 ha with ⟨l, hl, e⟩ | ⟨h, -⟩
      · exact Or.inl ⟨l, hl, (Prod.ext_iff.1 e).1⟩
      · exact Or.inr (GridData.mem_cloudHalf.1 h)
    · rcases GridData.mem_discrete_parameter_iff.1 hi with ⟨h, -⟩ | ⟨l, h1, h2, e⟩
      · exact Or.inl (GridData.mem_cloud.1 h)
      · exact Or.inr ⟨l, h1, h2, (Prod.ext_iff.1 e).1⟩
  refine ⟨fun a i h => ?_, fun a i h => ?_⟩
  · rw [hq, hq'] at h ⊢
    have := (key a i).1 (by exact_mod_cast h)
    exact_mod_cast this
  · rw [hq, hq'] at h
    exact (key a i).2 (by exact_mod_cast h)

end GlobalTheory.WordSep
