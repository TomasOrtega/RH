import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `L _ _ _ X`. Break down `isEmpty_or_nonempty (Plc L) with hE | hN` into its components or cases. Use `⟨∅, Set.empty_subset _, Set.injOn_empty _, ?_⟩` and prove the remaining obligations. Introduce `w`. Conclude with `(IsEmpty.false w).elim`.

Use `set f : Plc L → _ := fun w : Plc L => w.under (𝓞 (Lp L)) with hf`. Establish `spec : ∀ w ∈ X, Classical.epsilon (fun v => v ∈ X ∧ f v = f w) ∈ X ∧ f (Classical.epsilon (fun v => v ∈ X ∧ f v = f w)) = f w` using `fun w hw => Classical.epsilon_spec (p := fun v => v ∈ X ∧ f v = f w) ⟨w, hw, rfl⟩`. Use `⟨(fun w => Classical.epsilon (fun v => v ∈ X ∧ f v = f w)) '' X, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Conclude with `(spec w hw).1`.

Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab`. Establish `hab' : f a = f b`. Use `hab` as an intermediate fact. Simplify using `only at this`. Rewrite `this` using `[(spec a ha).2, (spec b hb).2]`.

Conclude with `this`. Simplify using `only [hab']`. Introduce `w hw`. Conclude with `⟨_, ⟨w, hw, rfl⟩, (spec w hw).2⟩`.
-/
theorem UpperTheory.V.Z.Sym.Ga.select :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (X : Set (Plc L)), ∃ P ⊆ X, Set.InjOn (fun w : Plc L => w.under (𝓞 (Lp L))) P ∧ ∀ w ∈ X, ∃ w' ∈ P, w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) := by
  intro L _ _ _ X
  rcases isEmpty_or_nonempty (Plc L) with hE | hN
  · refine ⟨∅, Set.empty_subset _, Set.injOn_empty _, ?_⟩
    intro w
    exact (IsEmpty.false w).elim
  set f : Plc L → _ := fun w : Plc L => w.under (𝓞 (Lp L)) with hf
  have spec : ∀ w ∈ X, Classical.epsilon (fun v => v ∈ X ∧ f v = f w) ∈ X ∧
      f (Classical.epsilon (fun v => v ∈ X ∧ f v = f w)) = f w :=
    fun w hw => Classical.epsilon_spec (p := fun v => v ∈ X ∧ f v = f w) ⟨w, hw, rfl⟩
  refine ⟨(fun w => Classical.epsilon (fun v => v ∈ X ∧ f v = f w)) '' X, ?_, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (spec w hw).1
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have hab' : f a = f b := by
      have := hab
      simp only at this
      rw [(spec a ha).2, (spec b hb).2] at this
      exact this
    simp only [hab']
  · intro w hw
    exact ⟨_, ⟨w, hw, rfl⟩, (spec w hw).2⟩
