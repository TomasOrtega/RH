import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `haveI : Nonempty α := ⟨a⟩`. Set `g : β → α` to `fun b => if b = f a then a else Function.invFunOn f S b`. Establish `hg : ∀ b ∈ f '' S, g b ∈ S ∧ f (g b) = b`. Introduce `b hb`. Distinguish the cases in `h : b = f a`.

Simplify using `only [g, if_pos h]`. Conclude with `⟨ha, h.symm⟩`. Simplify using `only [g, if_neg h]`. Conclude with `⟨Function.invFunOn_mem hb, Function.invFunOn_eq hb⟩`. Use `⟨g '' (f '' S), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨b, hb, rfl⟩`. Conclude with `(hg b hb).1`. Conclude with `⟨f a, ⟨a, ha, rfl⟩, by simp [g]⟩`. Introduce and unpack `_ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ h`. Rewrite `h` using `[(hg b hb).2, (hg c hc).2]`.

Rewrite using `[h]`. Introduce `w hw`. Conclude with `⟨g (f w), ⟨f w, ⟨w, hw, rfl⟩, rfl⟩, (hg _ ⟨w, hw, rfl⟩).2⟩`.
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
Introduce `L _ _ _ X w₀ hw₀`. Conclude with `selectThrough _ X w₀ hw₀`.
-/
theorem UpperTheory.V.Z.Sym.W.selectW :
    UpperTheory.V.Z.Sym.W.SelectW := by
  intro L _ _ _ X w₀ hw₀
  exact selectThrough _ X w₀ hw₀
