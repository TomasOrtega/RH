import Development.EtaleCohomology.EtaleSheaves.ChowGraphCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterCompPf

/- English proof (translation)
The claim follows from `h.bc (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ l) l (𝟙 S))`.
-/
theorem isLine_iso_comp {L L' S : Scheme.{0}} (e : L' ⟶ L) [IsIso e] {l : L ⟶ S} (h : IsLine l) :
    IsLine (e ≫ l) :=
  h.bc (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ l) l (𝟙 S))

/- English proof (translation)
Consider the cases of `hk with`. Consider the case `iso k' hk' => exact IterLine.iso _ inferInstance`. Consider the case `comp l k' hl hk'`. Rewrite using `[← Category.assoc]`. Conclude with `IterLine.comp _ _ (isLine_iso_comp e hl) hk'`.
-/
theorem iterLine_iso_comp {T S Y : Scheme.{0}} {k : T ⟶ S} (hk : IterLine k) (e : Y ⟶ T) [IsIso e] :
    IterLine (e ≫ k) := by
  cases hk with
  | iso k' hk' => exact IterLine.iso _ inferInstance
  | comp l k' hl hk' =>
    rw [← Category.assoc]
    exact IterLine.comp _ _ (isLine_iso_comp e hl) hk'

/- English proof (translation)
Introduce `P T S l k hl hk`. Proceed by induction on `hl with`. Consider the case `iso e he => exact iterLine_iso_comp hk e`. Consider the case `comp l₁ k₁ hl₁ _ ih`. Rewrite using `[Category.assoc]`.

Conclude with `IterLine.comp _ _ hl₁ ih`.
-/
theorem IterComp_of : LateralTheory.E.ChowGraphCut.IterComp := by
  intro P T S l k hl hk
  induction hl with
  | iso e he => exact iterLine_iso_comp hk e
  | comp l₁ k₁ hl₁ _ ih =>
    rw [Category.assoc]
    exact IterLine.comp _ _ hl₁ ih

end LateralTheory.E.IterCompPf

end
