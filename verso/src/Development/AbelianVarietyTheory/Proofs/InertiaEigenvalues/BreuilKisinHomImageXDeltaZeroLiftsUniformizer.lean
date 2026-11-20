import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

/- English proof (translation)
Introduce `l _ K bk C g`. Establish `hδX : (deltaS l bk.a).δ (X : (Wq l bk.a)⟦X⟧) = 0`. Establish `h` using `(deltaS l bk.a).φ_eq (X : (Wq l bk.a)⟦X⟧)`. Establish `h2 : (deltaS l bk.a).φ (X : (Wq l bk.a)⟦X⟧) = X ^ l` using `frobS_X l bk.a`. Rewrite `h` using `[h2]`.

Establish `h3 : (l : (Wq l bk.a)⟦X⟧) * (deltaS l bk.a).δ X = 0` using `by linear_combination -h`. Conclude with `(mul_eq_zero.1 h3).resolve_left (l_ne_zero l bk.a)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `g.f_δ (X : (Wq l bk.a)⟦X⟧)`. Express the relevant statement in the definitionally equal form `C.D.δ (g.f X) = 0`.

Rewrite using `[← h]`. Express the relevant statement in the definitionally equal form `g.f ((deltaS l bk.a).δ X) = 0`. Rewrite using `[hδX]`. Conclude with `g.f.map_zero`. Use `g.f_str (bk.str.symm (Ideal.Quotient.mk _ X)) X ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str (bk.str.symm (Ideal.Quotient.mk _ X))`. Rewrite using `[RingEquiv.apply_symm_apply]`.
-/
theorem hf_X_δ_and_str : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (g : Hom bk.prism C), C.D.δ (BK.hf g X) = 0 ∧ Ideal.Quotient.mk C.I (BK.hf g X) = C.str (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  intro l _ K bk C g
  have hδX : (deltaS l bk.a).δ (X : (Wq l bk.a)⟦X⟧) = 0 := by
    have h := (deltaS l bk.a).φ_eq (X : (Wq l bk.a)⟦X⟧)
    have h2 : (deltaS l bk.a).φ (X : (Wq l bk.a)⟦X⟧) = X ^ l := frobS_X l bk.a
    rw [h2] at h
    have h3 : (l : (Wq l bk.a)⟦X⟧) * (deltaS l bk.a).δ X = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h3).resolve_left (l_ne_zero l bk.a)
  refine ⟨?_, ?_⟩
  · have h := g.f_δ (X : (Wq l bk.a)⟦X⟧)
    change C.D.δ (g.f X) = 0
    rw [← h]
    change g.f ((deltaS l bk.a).δ X) = 0
    rw [hδX]
    exact g.f.map_zero
  · refine g.f_str (bk.str.symm (Ideal.Quotient.mk _ X)) X ?_
    change Ideal.Quotient.mk (Ideal.span {bk.E}) X = bk.str (bk.str.symm (Ideal.Quotient.mk _ X))
    rw [RingEquiv.apply_symm_apply]

end GlobalTheory.BSP
