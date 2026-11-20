import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Tri

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

namespace GlobalTheory.AmpleGen

/- English proof (translation)
Introduce `K _ A _ P hP U _ κ _ _ W hW hWU n`. Distinguish the cases in `hU : U = ⊤`. Substitute `hU` using the available equality. Establish `hWU' : ⨆ i, W i = ⊤` using `by rw [hWU]; simp`. Assume the negation of the conclusion as `h`.

Conclude with `hP n ⟨κ, inferInstance, inferInstance, W, hW, hWU', h⟩`. Establish `hb : U = ⊥`. Use `eq_bot_iff.2 fun x hx => (hU (eq_top_iff.2 fun y _ => ?_)).elim` and prove the remaining obligations. Establish `: Subsingleton (Sp K)` using `inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Rewrite using `[Subsingleton.elim y x]` and apply the resulting hypothesis.

Substitute `hb` using the available equality. Use `HomologicalComplex.ExactAt.of_isZero ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.AbLaw.cechLB_X, ModuleCat.isZero_iff_subsingleton]`. Use `⟨fun a b => funext fun s => ?_⟩` and prove the remaining obligations. Use `GlobalTheory.AbLaw.SecOnR.ext_of_cover _ (I := PEmpty) (fun i => i.elim) (fun i => i.elim) ?_ fun i => i.elim` and prove the remaining obligations.

Take `⟨i, hi⟩` from `Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos _ : 0 < s.1.card)`. Use `(biInf_le W hi).trans (((le_iSup W i).trans hWU.le).trans ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem isRelAcyclic_of_not_NV : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (P : LB A.left),
    (∀ j : ℕ, ¬ NV A P (j + 1)) → GlobalTheory.CxForm.IsRelAcyclic A.hom A.hom P := by
  intro K _ A _ P hP U _ κ _ _ W hW hWU n
  by_cases hU : U = ⊤
  · subst hU
    have hWU' : ⨆ i, W i = ⊤ := by rw [hWU]; simp
    by_contra h
    exact hP n ⟨κ, inferInstance, inferInstance, W, hW, hWU', h⟩
  · have hb : U = ⊥ := by
      refine eq_bot_iff.2 fun x hx => (hU (eq_top_iff.2 fun y _ => ?_)).elim
      have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      rwa [Subsingleton.elim y x]
    subst hb
    refine HomologicalComplex.ExactAt.of_isZero ?_
    rw [GlobalTheory.AbLaw.cechLB_X, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun a b => funext fun s => ?_⟩
    refine GlobalTheory.AbLaw.SecOnR.ext_of_cover _ (I := PEmpty) (fun i => i.elim) (fun i => i.elim) ?_ fun i => i.elim
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos _ : 0 < s.1.card)
    refine (biInf_le W hi).trans (((le_iSup W i).trans hWU.le).trans ?_)
    simp

end GlobalTheory.AmpleGen
