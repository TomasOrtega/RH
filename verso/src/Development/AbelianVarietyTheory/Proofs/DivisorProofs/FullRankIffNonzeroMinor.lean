import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hr`. Take `⟨κ, f, hinj, hspan, hli⟩` from `exists_linearIndependent' k Y.col`. Use `haveI : Finite κ := Finite.of_injective f hinj`. Use `haveI : Fintype κ := Fintype.ofFinite κ`.

Establish `hcard : Fintype.card κ = a`. Rewrite using `[← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hr]`. Set `e : κ ≃ Fin a` to `Fintype.equivFinOfCardEq hcard`. Set `J : Fin a ↪ Fin d` to `⟨f ∘ e.symm, hinj.comp e.symm.injective⟩`. Use `⟨J, ?_⟩` and prove the remaining obligations.

Establish `hc : (Y.submatrix id J).col = (Y.col ∘ f) ∘ e.symm`. Use function extensionality and compare the values at `j i`. Both sides reduce to the same expression. Establish `hli' : LinearIndependent k (Y.submatrix id J).col`. Rewrite using `[hc]`.

Conclude with `hli.comp e.symm e.symm.injective`. Establish `hu` using `Matrix.linearIndependent_cols_iff_isUnit.mp hli'`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero`. Introduce and unpack `⟨J, hJ⟩`. Establish `hu : IsUnit (Y.submatrix id J)` using `(Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hJ)`.

Establish `hli'` using `Matrix.linearIndependent_rows_iff_isUnit.mpr hu`. Establish `hr : (Y.submatrix id J).row = (LinearMap.funLeft k k J) ∘ Y.row`. Use function extensionality and compare the values at `i j`. Both sides reduce to the same expression. Rewrite `hli'` using `[hr]`.

Establish `hli` using `LinearIndependent.of_comp _ hli'`. Rewrite using `[Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli, Fintype.card_fin]`.
-/
theorem rank_eq_iff_exists_minor_ne_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) :
    Y.rank = a ↔ ∃ J, minor Y J ≠ 0 := by
  constructor
  · intro hr
    obtain ⟨κ, f, hinj, hspan, hli⟩ := exists_linearIndependent' k Y.col
    haveI : Finite κ := Finite.of_injective f hinj
    haveI : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = a := by
      rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols, hr]
    let e : κ ≃ Fin a := Fintype.equivFinOfCardEq hcard
    let J : Fin a ↪ Fin d := ⟨f ∘ e.symm, hinj.comp e.symm.injective⟩
    refine ⟨J, ?_⟩
    have hc : (Y.submatrix id J).col = (Y.col ∘ f) ∘ e.symm := by
      funext j i; rfl
    have hli' : LinearIndependent k (Y.submatrix id J).col := by
      rw [hc]; exact hli.comp e.symm e.symm.injective
    have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  · rintro ⟨J, hJ⟩
    have hu : IsUnit (Y.submatrix id J) := (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hJ)
    have hli' := Matrix.linearIndependent_rows_iff_isUnit.mpr hu
    have hr : (Y.submatrix id J).row = (LinearMap.funLeft k k J) ∘ Y.row := by
      funext i j; rfl
    rw [hr] at hli'
    have hli := LinearIndependent.of_comp _ hli'
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli, Fintype.card_fin]

end GlobalTheory.RankFibreKer
