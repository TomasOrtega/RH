import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchBPf

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MB

open PositivityTheory.Rg.BcB.F.U (lpow lone)

def MatchBadIOf2 : Prop := M2 → LponeIdem → MatchBadI

/- English proof (translation)
Introduce `h2 hI E _ _ _ hU w hw n a b k hab hk K' hK hmem m`. Rewrite using `[hI E n w K' hK m]`. Establish `hM` using `h2 E hU w hw n a b k hab hk`. Establish `hf : lone K' = fun γ => ((K'.relIndex (KL n w) : ℕ) : ℂ) * (({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w)).indicator 1 γ)`. Use function extensionality and compare the values at `γ`.

Rewrite using `[mb_lone_apply]`. Distinguish the cases in `h : γ ∈ K'`. Establish `h' : γ ∈ ({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w))` using `(hmem γ).1 h`. Rewrite using `[if_pos h, Set.indicator_of_mem h', Pi.one_apply, mul_one]`. Establish `h' : γ ∉ ({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w))` using `fun h' => h ((hmem γ).2 h')`.

Simplify using `[h, h']`. Rewrite using `[hf]`. Establish `hM' : Match n a b w 1 ({γ : UL n w | γ.1 ∈ congK n w k}.indicator 1) (pairIndicatorMatch n a b w k)`. Use `hM using 2` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.

Unfold `pairIndicatorMatch congK`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> rfl`. Conclude with `mb_match_smul _ hM'`.
-/
theorem matchBadIOf2 : MatchBadIOf2 := by
  intro h2 hI E _ _ _ hU w hw n a b k hab hk K' hK hmem m
  rw [hI E n w K' hK m]
  have hM := h2 E hU w hw n a b k hab hk
  have hf : lone K' = fun γ => ((K'.relIndex (KL n w) : ℕ) : ℂ) *
      (({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w)).indicator 1 γ) := by
    funext γ
    rw [mb_lone_apply]
    by_cases h : γ ∈ K'
    · have h' : γ ∈ ({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w)) := (hmem γ).1 h
      rw [if_pos h, Set.indicator_of_mem h', Pi.one_apply, mul_one]
    · have h' : γ ∉ ({γ : UL n w | γ.1 ∈ congK n w k} : Set (UL n w)) := fun h' => h ((hmem γ).2 h')
      simp [h, h']
  rw [hf]
  have hM' : Match n a b w 1 ({γ : UL n w | γ.1 ∈ congK n w k}.indicator 1) (pairIndicatorMatch n a b w k) := by
    convert hM using 2
    · rfl
    · unfold pairIndicatorMatch congK
      congr 1
      split_ifs <;> rfl
  exact mb_match_smul _ hM'

end PositivityTheory.Rg.BcB.F.MB

end
