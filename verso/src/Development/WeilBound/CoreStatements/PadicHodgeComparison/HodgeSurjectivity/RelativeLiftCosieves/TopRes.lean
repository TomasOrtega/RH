import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Onto

/- English proof (translation)
Introduce `R _ C _ F U Q hU n`. Set `L : C ⥤ U.FullSubcategory` to `U.lift (𝟭 C) hU`. Establish `back : ∀ z : CH.Cn F n, ∀ s : ComposableArrows C n, (CH.Mor.restrict F U.ι).pullC n z (s ⋙ L) = z s` using `fun _ _ => rfl`. Use `⟨⟨fun z z' h => funext fun s => ?_, fun w => ⟨fun s => w (s ⋙ L), ?_⟩⟩, fun z => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← back z s, ← back z' s, h]`.

Use function extensionality and compare the values at `t`. Both sides reduce to the same expression. Introduce `hz s hs`. Rewrite using `[← back z s]`. Conclude with `hz (s ⋙ L) hs`.

Introduce `hz t ht`. Conclude with `hz (t ⋙ U.ι) ht`.
-/
theorem topRes_pf : TopRes := by
  intro R _ C _ F U Q hU n
  let L : C ⥤ U.FullSubcategory := U.lift (𝟭 C) hU
  have back : ∀ z : CH.Cn F n, ∀ s : ComposableArrows C n,
      (CH.Mor.restrict F U.ι).pullC n z (s ⋙ L) = z s := fun _ _ => rfl
  refine ⟨⟨fun z z' h => funext fun s => ?_, fun w => ⟨fun s => w (s ⋙ L), ?_⟩⟩, fun z => ⟨?_, ?_⟩⟩
  · rw [← back z s, ← back z' s, h]
  · funext t
    rfl
  · intro hz s hs
    rw [← back z s]
    exact hz (s ⋙ L) hs
  · intro hz t ht
    exact hz (t ⋙ U.ι) ht

end CrystallineSemistableComparison.Onto

end
