import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Simplify using the standard rewrite rules. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
private theorem selectThrough {α β : Type} (f : α → β) (S : Set α) (a : α) (ha : a ∈ S) :
    ∃ P ⊆ S, a ∈ P ∧ Set.InjOn f P ∧ ∀ w ∈ S, ∃ w' ∈ P, f w' = f w := by
  classical
  haveI : Nonempty α := ⟨a⟩
  let g : β → α := fun b => if b = f a then a else Function.invFunOn f S b
  have hg : ∀ b ∈ f '' S, g b ∈ S ∧ f (g b) = b := by
    intro b hb
    by_cases h : b = f a
    · simp only [g, if_pos h]
      exact ⟨ha, h.symm⟩
    · simp only [g, if_neg h]
      exact ⟨Function.invFunOn_mem hb, Function.invFunOn_eq hb⟩
  refine ⟨g '' (f '' S), ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact (hg b hb).1
  · exact ⟨f a, ⟨a, ha, rfl⟩, by simp [g]⟩
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ h
    rw [(hg b hb).2, (hg c hc).2] at h
    rw [h]
  · intro w hw
    exact ⟨g (f w), ⟨f w, ⟨w, hw, rfl⟩, rfl⟩, (hg _ ⟨w, hw, rfl⟩).2⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Z.Sym.W.selectW :
    UpperTheory.V.Z.Sym.W.SelectW := by
  intro L _ _ _ X w₀ hw₀
  exact selectThrough _ X w₀ hw₀
