import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Evaluate the decidable proposition. A detailed English derivation is pending.
-/
private theorem idx_cases (a b : Fin 3) :
    Odd (w 3 a - w 3 b) ∨ (a = 1 ∧ b = 1) ∨ ∃ i j, a = cor i ∧ b = cor j := by
  revert a b
  decide

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Fr.frobenius_corner_monomial :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K] (ρ : NRep F 3 K) (σ : NRep F 2 K), IsCorner ρ σ → ∀ (j : ℤ), ∀ x ∈ ρ.mon j, x = 0 ∨ ∃ T : List F.G0, ∃ y ∈ σ.mon j, x = (T.map fun g => ρ.r g 1 1).prod * y := by
  intro l _ k _ F K _ ρ σ hc j x hx
  obtain ⟨L, hL, rfl⟩ := hx
  induction L generalizing j with
  | nil =>
    right
    refine ⟨[], 1, ⟨[], ?_, ?_⟩, ?_⟩
    · simpa using hL
    · simp
    · simp
  | cons s L ih =>
    obtain ⟨g, a, b⟩ := s
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hL ⊢
    rcases ih _ rfl with h | ⟨T, y, ⟨M, hM, hy⟩, he⟩
    · left
      rw [h, mul_zero]
    · rcases idx_cases a b with hab | ⟨rfl, rfl⟩ | ⟨i, i', rfl, rfl⟩
      · left
        rw [hc.odd g a b hab, zero_mul]
      · right
        refine ⟨g :: T, y, ⟨M, ?_, hy⟩, ?_⟩
        · rw [hM, ← hL]
          simp
        · rw [he]
          simp only [List.map_cons, List.prod_cons]
          ring
      · right
        refine ⟨T, σ.r g i i' * y, ⟨(g, i, i') :: M, ?_, ?_⟩, ?_⟩
        · simp only [List.map_cons, List.sum_cons]
          rw [hM, ← hL, w_cor, w_cor]
        · simp only [List.map_cons, List.prod_cons]
          rw [hy]
        · rw [he, hc.r]
          ring
