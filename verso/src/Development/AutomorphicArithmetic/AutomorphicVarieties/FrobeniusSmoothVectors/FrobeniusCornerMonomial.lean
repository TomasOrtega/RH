import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Use `revert a b`. Evaluate the decidable proposition.
-/
private theorem idx_cases (a b : Fin 3) :
    Odd (w 3 a - w 3 b) ∨ (a = 1 ∧ b = 1) ∨ ∃ i j, a = cor i ∧ b = cor j := by
  revert a b
  decide

/- English proof (translation)
Introduce `l _ k _ F K _ ρ σ hc j x hx`. Take `⟨L, hL, rfl⟩` from `hx`. Proceed by induction on `L generalizing j with`. Consider the case `nil => right`. Use `⟨[], 1, ⟨[], ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Simplify using `using hL`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Consider the case `cons s L ih`. Take `⟨g, a, b⟩` from `s`.

Simplify using `only [List.map_cons, List.sum_cons, List.prod_cons] at hL ⊢`. Break down `ih _ rfl with h | ⟨T, y, ⟨M, hM, hy⟩, he⟩` into its components or cases. Use `left`. Rewrite using `[h, mul_zero]`. Break down `idx_cases a b with hab | ⟨rfl, rfl⟩ | ⟨i, i', rfl, rfl⟩` into its components or cases.

Use `left`. Rewrite using `[hc.odd g a b hab, zero_mul]`. Use `right`. Use `⟨g :: T, y, ⟨M, ?_, hy⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hM, ← hL]`.

Simplify using the standard rewrite rules. Rewrite using `[he]`. Simplify using `only [List.map_cons, List.prod_cons]`. Expand and normalize the polynomial expressions, which then agree. Use `right`.

Use `⟨T, σ.r g i i' * y, ⟨(g, i, i') :: M, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [List.map_cons, List.sum_cons]`. Rewrite using `[hM, ← hL, w_cor, w_cor]`. Simplify using `only [List.map_cons, List.prod_cons]`. Rewrite using `[hy]`.

Rewrite using `[he, hc.r]`. Expand and normalize the polynomial expressions, which then agree.
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
