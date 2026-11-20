import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplFirstRow

/- English proof (translation)
Introduce `h`. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrFun h i` as an intermediate fact. Simplify `this` using `[intVec]`.
-/
theorem intVec_ne_zero {ι : Type*} {v : ι → ℤ} (hv : v ≠ 0) : intVec v ≠ 0 := by
  intro h
  apply hv
  funext i
  have := congrFun h i
  simpa [intVec] using this

end PSymplFirstRow

/- English proof (translation)
Introduce `n G hG hpd`. Take `⟨ρsq, hleast⟩` from `h1 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd`. Establish `hdet : G.det = 1` using `SymplecticGroup.det_eq_one hG`. Establish `hbound` using `h2 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd hdet ρsq hleast`. Take `⟨v, hv0, hvρ⟩` from `hleast.1`.

Use `⟨ρsq, hleast, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hvρ]`. Use `hpd.dotProduct_mulVec_pos (PSymplFirstRow.intVec_ne_zero hv0)` as an intermediate fact. Simplify `this` using `[qf]`. Simplify using `only [Fintype.card_sum, Fintype.card_fin] at hbound`.

Move the coercions through the operations in `at hbound`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmin : ∀ u : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, u ≠ 0 → qf G (intVec v) ≤ qf G (intVec u)`. Introduce `u hu`. Rewrite using `[← hvρ]`.

Conclude with `hleast.2 ⟨u, hu, rfl⟩`. Take `⟨P, hP, m, hm⟩` from `h3 n v`. Establish `hrow : ∃ P' ∈ symplecticGroup (Fin (n + 1)) ℤ, P' (Sum.inl 0) = v`. Break down `h4 _ G hpd v (P (Sum.inl 0)) m hm hv0 hmin with h | h` into its components or cases. Conclude with `⟨P, hP, by rw [hm, h, one_smul]⟩`.

Use `⟨-P, SymplecticGroup.neg_mem hP, ?_⟩` and prove the remaining obligations. Rewrite using `[hm, h, neg_one_smul]`. Both sides reduce to the same expression. Take `⟨P', hP', hP'v⟩` from `hrow`. Use `⟨P', hP', ?_⟩` and prove the remaining obligations.

Rewrite using `[(h5 (n + 1) P' G hP' hG hpd).2.2.2 (Sum.inl 0), hP'v, hvρ]`.
-/
theorem SymplFirstRow.proof (h1 : SymplMinExists.Statement) (h2 : SymplMinBound.Statement)
    (h3 : SymplOrbit.Statement) (h4 : SymplShortPrim.Statement) (h5 : SymplGramMem.Statement) :
    SymplFirstRow.Statement := by
  intro n G hG hpd
  obtain ⟨ρsq, hleast⟩ := h1 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd
  have hdet : G.det = 1 := SymplecticGroup.det_eq_one hG
  have hbound := h2 (Fin (n + 1) ⊕ Fin (n + 1)) G hpd hdet ρsq hleast
  obtain ⟨v, hv0, hvρ⟩ := hleast.1
  refine ⟨ρsq, hleast, ?_, ?_, ?_⟩
  · rw [hvρ]
    have := hpd.dotProduct_mulVec_pos (PSymplFirstRow.intVec_ne_zero hv0)
    simpa [qf] using this
  · simp only [Fintype.card_sum, Fintype.card_fin] at hbound
    push_cast at hbound
    linarith
  · have hmin : ∀ u : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, u ≠ 0 →
        qf G (intVec v) ≤ qf G (intVec u) := by
      intro u hu
      rw [← hvρ]
      exact hleast.2 ⟨u, hu, rfl⟩
    obtain ⟨P, hP, m, hm⟩ := h3 n v
    have hrow : ∃ P' ∈ symplecticGroup (Fin (n + 1)) ℤ, P' (Sum.inl 0) = v := by
      rcases h4 _ G hpd v (P (Sum.inl 0)) m hm hv0 hmin with h | h
      · exact ⟨P, hP, by rw [hm, h, one_smul]⟩
      · refine ⟨-P, SymplecticGroup.neg_mem hP, ?_⟩
        rw [hm, h, neg_one_smul]
        rfl
    obtain ⟨P', hP', hP'v⟩ := hrow
    refine ⟨P', hP', ?_⟩
    rw [(h5 (n + 1) P' G hP' hG hpd).2.2.2 (Sum.inl 0), hP'v, hvρ]

end GroundTheory.Heights₂.Heights
