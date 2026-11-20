import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

/- English proof (translation)
Introduce `X _ D A R g hg hEq j k l`. Establish `hOopen : IsOpen (bdDom R j ∩ bdDom R k ∩ bdDom R l)` using `((isOpen_bdDom R j).inter (isOpen_bdDom R k)).inter (isOpen_bdDom R l)`. Establish `hOjl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R l` using `fun _ hy => ⟨hy.1.1, hy.2⟩`. Establish `hOjk : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R k` using `fun _ hy => hy.1`. Establish `hOkl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R k ∩ bdDom R l` using `fun _ hy => ⟨hy.1.2, hy.2⟩`.

Establish `hYo : Set.EqOn (g j l) (fun y => g j k y * g k l y) ((bdDom R j ∩ bdDom R k ∩ bdDom R l) ∩ R.Yo)`. Introduce and unpack `y ⟨hyO, hyY⟩`. Establish `hne : bdEq R l y ≠ 0` using `fun h0 => ((hHolo D A R l).2 y hyO.2).1 h0 hyY`. Establish `h1` using `hEq j l y (hOjl hyO)`. Establish `h2` using `hEq j k y (hOjk hyO)`.

Establish `h3` using `hEq k l y (hOkl hyO)`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises. Use `show g j l y * bdEq R l y = g j k y * g k l y * bdEq R l y`. Rewrite using `[← h1, h2, h3, mul_assoc]`. Establish `hall` using `hYo.of_subset_closure ((hg j l).mono hOjl) (((hg j k).mono hOjk).mul ((hg k l).mono hOkl)) Set.inter_subset_left ((hDense D A R).open_subset_closure_inter hOopen)`.

Introduce `y hy`. Conclude with `hall hy`.
-/
theorem BdCocycle.proof (hDense : RegYoDense.Statement) (hHolo : BdEqHolo.Statement) :
    BdCocycle.Statement := by
  intro X _ D A R g hg hEq j k l
  have hOopen : IsOpen (bdDom R j ∩ bdDom R k ∩ bdDom R l) :=
    ((isOpen_bdDom R j).inter (isOpen_bdDom R k)).inter (isOpen_bdDom R l)
  have hOjl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R l := fun _ hy => ⟨hy.1.1, hy.2⟩
  have hOjk : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R j ∩ bdDom R k := fun _ hy => hy.1
  have hOkl : bdDom R j ∩ bdDom R k ∩ bdDom R l ⊆ bdDom R k ∩ bdDom R l := fun _ hy => ⟨hy.1.2, hy.2⟩
  have hYo : Set.EqOn (g j l) (fun y => g j k y * g k l y)
      ((bdDom R j ∩ bdDom R k ∩ bdDom R l) ∩ R.Yo) := by
    rintro y ⟨hyO, hyY⟩
    have hne : bdEq R l y ≠ 0 := fun h0 => ((hHolo D A R l).2 y hyO.2).1 h0 hyY
    have h1 := hEq j l y (hOjl hyO)
    have h2 := hEq j k y (hOjk hyO)
    have h3 := hEq k l y (hOkl hyO)
    apply mul_right_cancel₀ hne
    show g j l y * bdEq R l y = g j k y * g k l y * bdEq R l y
    rw [← h1, h2, h3, mul_assoc]
  have hall := hYo.of_subset_closure ((hg j l).mono hOjl)
    (((hg j k).mono hOjk).mul ((hg k l).mono hOkl)) Set.inter_subset_left
    ((hDense D A R).open_subset_closure_inter hOopen)
  intro y hy
  exact hall hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
