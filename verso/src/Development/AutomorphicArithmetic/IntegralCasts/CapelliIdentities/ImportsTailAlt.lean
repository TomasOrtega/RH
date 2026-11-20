import Mathlib

/- English proof (translation)
Introduce `F _ r a M hM`. Establish `hinj : Function.Injective M.mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]`. Conclude with `hM`. Establish `hrank : M.rank = a`.

Rewrite using `[Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]`. Take `⟨κ, f, hf, hsp, hli⟩` from `exists_linearIndependent' F M.row`. Use `haveI : Finite κ := Finite.of_injective f hf`. Use `letI : Fintype κ := Fintype.ofFinite κ`. Establish `hcard : Fintype.card κ = a`.

Rewrite using `[← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrank]`. Set `eqv : κ ≃ Fin a` to `Fintype.equivFinOfCardEq hcard`. Use `⟨f ∘ eqv.symm, ?_⟩` and prove the remaining obligations. Establish `hli2 : LinearIndependent F (M.submatrix (f ∘ eqv.symm) id).row`. Use `hli.comp eqv.symm eqv.symm.injective` as an intermediate fact.

Establish `h : (M.submatrix (f ∘ eqv.symm) id).row = (M.row ∘ f) ∘ eqv.symm`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `this`.

Establish `hu` using `Matrix.linearIndependent_rows_iff_isUnit.mp hli2`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero`.
-/
theorem UpperTheory.Reformulated.B.Yra1.main.{u_1} :
    ∀ {F : Type u_1} [inst : Field F] {r a : ℕ} (M : Matrix (Fin r) (Fin a) F),
      (∀ (z : Fin a → F), M.mulVec z = (0 : Fin r → F) → z = (0 : Fin a → F)) →
        ∃ (e : Fin a → Fin r), (M.submatrix e id).det ≠ (0 : F) := by
  intro F _ r a M hM
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
    exact hM
  have hrank : M.rank = a := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  obtain ⟨κ, f, hf, hsp, hli⟩ := exists_linearIndependent' F M.row
  haveI : Finite κ := Finite.of_injective f hf
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = a := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row, hrank]
  let eqv : κ ≃ Fin a := Fintype.equivFinOfCardEq hcard
  refine ⟨f ∘ eqv.symm, ?_⟩
  have hli2 : LinearIndependent F (M.submatrix (f ∘ eqv.symm) id).row := by
    have := hli.comp eqv.symm eqv.symm.injective
    have h : (M.submatrix (f ∘ eqv.symm) id).row = (M.row ∘ f) ∘ eqv.symm := by
      ext i j; rfl
    rw [h]; exact this
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hli2
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
