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
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Both sides reduce to the same expression.

Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
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
