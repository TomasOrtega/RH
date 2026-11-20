import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IterateOnePlusCasOfEq
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum

open GlobalTheory.LowTypeDetermined

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

/- English proof (translation)
Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Treat this case separately. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Dw_comb (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) (L : List (ℂ × List (Mx n))) (hL : ∀ u ∈ L, ∀ Y ∈ u.2, Y ∈ lieSet ε) :
    Sm ε σ ((L.map fun u => u.1 • Dw σ u.2 v).sum) ∧
      Dw σ l ((L.map fun u => u.1 • Dw σ u.2 v).sum) = (L.map fun u => u.1 • Dw σ (l ++ u.2) v).sum := by
  induction L with
  | nil =>
    refine ⟨(smooth (Jm ε) σ).zero_mem, ?_⟩
    have h := Dw_smul hσ hl (0 : ℂ) hv
    simpa using h
  | cons u L ih =>
    have hu : Sm ε σ (Dw σ u.2 v) := hv.word hσ (hL u List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := ih fun w hw => hL w (List.mem_cons_of_mem _ hw)
    have hs : Sm ε σ (u.1 • Dw σ u.2 v) := (smooth (Jm ε) σ).smul_mem u.1 hu
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      exact (smooth (Jm ε) σ).add_mem hs ih1
    · simp only [List.map_cons, List.sum_cons]
      rw [Dw_add hσ hl hs ih1, Dw_smul hσ hl u.1 hu, ← Dw_append, ih2]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem sum_neg_comb (L : List (ℂ × List (Mx n))) (f : List (Mx n) → H) :
    (L.map fun u => (-u.1) • f u.2).sum = -(L.map fun u => u.1 • f u.2).sum := by
  induction L with
  | nil => simp
  | cons u L ih =>
    simp only [List.map_cons, List.sum_cons, neg_smul, neg_add] at *
    rw [ih]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sum_norm_neg (L : List (ℂ × List (Mx n))) (f : List (Mx n) → List (Mx n)) :
    ((L.map fun u => ((-u.1, f u.2) : ℂ × List (Mx n))).map fun u => ‖u.1‖).sum = (L.map fun u => ‖u.1‖).sum := by
  simp [List.map_map, Function.comp_def]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem sum_flatMap' {α M : Type} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun i => (f i).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem caspow_expand : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ (d : ℕ) (X : Fin d → Mx n), (∀ i, X i ∈ lieSet ε) →
    ∀ r : ℕ, ∃ L : List (ℂ × List (Mx n)), (∀ u ∈ L, u.2.length ≤ 2 * r ∧ ∀ Y ∈ u.2, ∃ i, X i = Y) ∧
      (L.map fun u => ‖u.1‖).sum ≤ (1 + (d : ℝ)) ^ r ∧
      ∀ v, Sm ε σ v → (onePlusCas σ X)^[r] v = (L.map fun u => u.1 • Dw σ u.2 v).sum := by
  intro n ε H _ _ σ hσ d X hX r
  induction r with
  | zero =>
    refine ⟨[(1, [])], ?_, ?_, ?_⟩
    · simp
    · simp
    · intro v _; simp
  | succ r ih =>
    obtain ⟨L, hL1, hL2, hL3⟩ := ih
    have hLie : ∀ u ∈ L, ∀ Y ∈ u.2, Y ∈ lieSet ε := fun u hu Y hY => by
      obtain ⟨i, rfl⟩ := (hL1 u hu).2 Y hY
      exact hX i
    let M : Fin d → List (ℂ × List (Mx n)) := fun i => L.map fun u => (-u.1, X i :: X i :: u.2)
    refine ⟨L ++ (List.finRange d).flatMap M, ?_, ?_, ?_⟩
    · intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact ⟨(hL1 u hu).1.trans (by omega), (hL1 u hu).2⟩
      · obtain ⟨i, -, hu⟩ := List.mem_flatMap.1 hu
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
        refine ⟨?_, ?_⟩
        · simp only [List.length_cons]; have := (hL1 w hw).1; omega
        · intro Y hY
          simp only [List.mem_cons] at hY
          rcases hY with rfl | rfl | hY
          · exact ⟨i, rfl⟩
          · exact ⟨i, rfl⟩
          · exact (hL1 w hw).2 Y hY
    · have hM : ∀ i, ((M i).map fun u => ‖u.1‖).sum = (L.map fun u => ‖u.1‖).sum := fun i => sum_norm_neg L (fun l => X i :: X i :: l)
      rw [List.map_append, List.sum_append, List.map_flatMap, sum_flatMap']
      simp only [hM, List.map_const', List.sum_replicate, List.length_finRange, nsmul_eq_mul]
      have h0 : 0 ≤ (L.map fun u => ‖u.1‖).sum := List.sum_nonneg fun x hx => by
        obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [pow_succ]
      nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + d) r]
    · intro v hv
      have hi : ∀ i, dRep σ (X i) (dRep σ (X i) (L.map fun u => u.1 • Dw σ u.2 v).sum) =
          (L.map fun u => u.1 • Dw σ (X i :: X i :: u.2) v).sum := fun i =>
        (Dw_comb hσ (l := [X i, X i]) (by simp [hX i]) hv L hLie).2
      have hMi : ∀ i, ((M i).map fun u => u.1 • Dw σ u.2 v).sum =
          -(L.map fun u => u.1 • Dw σ (X i :: X i :: u.2) v).sum := fun i => by
        rw [← sum_neg_comb L (fun l => Dw σ (X i :: X i :: l) v)]
        simp [M, List.map_map, Function.comp_def]
      rw [Function.iterate_succ_apply', hL3 v hv, onePlusCas]
      simp only [hi]
      rw [List.map_append, List.sum_append, List.map_flatMap, sum_flatMap', ← Fin.sum_univ_def]
      simp only [hMi, Finset.sum_neg_distrib, sub_eq_add_neg]

end GlobalTheory.TypeSum
