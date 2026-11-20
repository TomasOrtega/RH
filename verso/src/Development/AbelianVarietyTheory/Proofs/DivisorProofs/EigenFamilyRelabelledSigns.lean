import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelabDR

/- English proof (translation)
Establish `hk : (k : ℕ) < (letters O.S.Dw).length`. Rewrite using `[GlobalTheory.ShFam.Pad.length_letters O.S]`. Conclude with `k.2`. Rewrite using `[List.getElem?_eq_getElem hk]`. Both sides reduce to the same expression.
-/
theorem letters_getElem?_wholeL {D : D7} (O : Setup D) (k : Fin (D.R.f * O.N)) :
    (letters O.S.Dw)[(k : ℕ)]? = some (wholeL O k) := by
  have hk : (k : ℕ) < (letters O.S.Dw).length := by
    rw [GlobalTheory.ShFam.Pad.length_letters O.S]; exact k.2
  rw [List.getElem?_eq_getElem hk]
  rfl

/- English proof (translation)
Introduce `D O`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(x | k | k)`. Use `show rootSg O x = 1 ∨ rootSg O x = -1`. Unfold `rootSg`.

Use `split_ifs`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`.

Introduce and unpack `R (⟨t, i⟩ | k | k)`. Use `Or.inl ⟨rootL O (t, i), rfl, ?_⟩` and prove the remaining obligations. Establish `hp'` using `O.S.p_eq`. Establish `hq` using `O.S.rank_eq`. Use `show rootSym O.S.Dw (ArIn.ind ∅) (some R) (DV.tauEmb D t) i = Finsupp.single _ (rootSg O (t, i))`.

Unfold `rootSym rootSg`. Simplify using `only`. Distinguish the cases in `hi : (i : ℕ) < O.j`. Establish `hx : ((rootL O (t, i)).1, ((rootL O (t, i)).2 : ℕ)) = (DV.tauEmb D t, (i : ℕ))`. Unfold `rootL LieGen.rootLetter`.

Rewrite using `[dif_pos hi]`. Rewrite using `[if_pos (show (i : ℕ) < O.S.Dw.p by omega), if_pos hi, hx]`. Establish `hx : ((rootL O (t, i)).1, ((rootL O (t, i)).2 : ℕ)) = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t), O.S.Dw.p + O.S.Dw.q - 1 - (i : ℕ))`. Unfold `rootL LieGen.rootLetter`. Rewrite using `[dif_neg hi]`.

Simplify using `only [Prod.mk.injEq, true_and]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg (show ¬ (i : ℕ) < O.S.Dw.p by omega), if_neg hi, hx]`. Conclude with `Or.inr ⟨wholeL O k, k, rfl, letters_getElem?_wholeL O k, rfl⟩`. Conclude with `Or.inr ⟨wholeL O (Fin.rev k), (Fin.rev k : ℕ), rfl, letters_getElem?_wholeL O _, rfl⟩`.
-/
theorem fam_eq_single : ∀ (D : D7) (O : Setup D), (∀ i, GlobalTheory.RelabDR.sg O i = 1 ∨ GlobalTheory.RelabDR.sg O i = -1) ∧ ∀ (R : ℝ) (i : GlobalTheory.EigWhole.Var O), (∃ z, GlobalTheory.RelabDR.ix O i = .inl z ∧ GlobalTheory.EigWhole.fam O ∅ R i = Finsupp.single (ArIn.ind ∅, some R, .inl (z.1, (z.2 : ℕ))) (GlobalTheory.RelabDR.sg O i)) ∨ ∃ z k, GlobalTheory.RelabDR.ix O i = .inr z ∧ (letters O.S.Dw)[k]? = some z ∧ GlobalTheory.EigWhole.fam O ∅ R i = Finsupp.single (ArIn.ind ∅, some R, .inr k) (GlobalTheory.RelabDR.sg O i) := by
  intro D O
  refine ⟨?_, ?_⟩
  · rintro (x | k | k)
    · show rootSg O x = 1 ∨ rootSg O x = -1
      unfold rootSg
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro R (⟨t, i⟩ | k | k)
    · refine Or.inl ⟨rootL O (t, i), rfl, ?_⟩
      have hp' := O.S.p_eq
      have hq := O.S.rank_eq
      show rootSym O.S.Dw (ArIn.ind ∅) (some R) (DV.tauEmb D t) i = Finsupp.single _ (rootSg O (t, i))
      unfold rootSym rootSg
      dsimp only
      by_cases hi : (i : ℕ) < O.j
      · have hx : ((rootL O (t, i)).1, ((rootL O (t, i)).2 : ℕ)) = (DV.tauEmb D t, (i : ℕ)) := by
          unfold rootL LieGen.rootLetter
          rw [dif_pos hi]
        rw [if_pos (show (i : ℕ) < O.S.Dw.p by omega), if_pos hi, hx]
      · have hx : ((rootL O (t, i)).1, ((rootL O (t, i)).2 : ℕ)) =
            (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t), O.S.Dw.p + O.S.Dw.q - 1 - (i : ℕ)) := by
          unfold rootL LieGen.rootLetter
          rw [dif_neg hi]
          simp only [Prod.mk.injEq, true_and]
          omega
        rw [if_neg (show ¬ (i : ℕ) < O.S.Dw.p by omega), if_neg hi, hx]
    · exact Or.inr ⟨wholeL O k, k, rfl, letters_getElem?_wholeL O k, rfl⟩
    · exact Or.inr ⟨wholeL O (Fin.rev k), (Fin.rev k : ℕ), rfl, letters_getElem?_wholeL O _, rfl⟩

end GlobalTheory.RelabDR

end
