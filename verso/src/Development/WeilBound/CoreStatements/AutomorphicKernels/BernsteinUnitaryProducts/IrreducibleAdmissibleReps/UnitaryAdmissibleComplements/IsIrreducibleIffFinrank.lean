import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.Assembly

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir

namespace PositivityTheory.PfBern.Props2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Zero

variable {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X]

end Zero

section GL0

variable {G X : Type} [Group G] [Subsingleton G] [AddCommGroup X] [Module ℂ X]

def subrepIso (ρ : Representation ℂ G X) : Subrepresentation ρ ≃o Submodule ℂ X where
  toFun S := S.toSubmodule
  invFun U := ⟨U, fun g v hv => by rw [Subsingleton.elim g 1, map_one]; exact hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/- English proof (translation)
Unfold `Representation.IsIrreducible`. Conclude with `(PositivityTheory.PfBern.Props2.subrepIso ρ).isSimpleOrder_iff.trans ((isSimpleModule_iff ℂ X).symm.trans isSimpleModule_iff_finrank_eq_one)`.
-/
theorem isIrreducible_iff_finrank (ρ : Representation ℂ G X) :
    ρ.IsIrreducible ↔ Module.finrank ℂ X = 1 := by
  unfold Representation.IsIrreducible
  exact (PositivityTheory.PfBern.Props2.subrepIso ρ).isSimpleOrder_iff.trans
    ((isSimpleModule_iff ℂ X).symm.trans isSimpleModule_iff_finrank_eq_one)

/- English proof (translation)
Use `haveI : DiscreteTopology G := Subsingleton.discreteTopology`. Establish `hmem : ∀ z : Z, (fun _ : G => z) ∈ GlobalTheory.PRep.indSpace H σ`. Introduce `z`. Simplify using `[GlobalTheory.PRep.indSpace, Subsingleton.elim _ (1 : H)]`. Establish `hsmooth : ∀ v : GlobalTheory.PRep.indSpace H σ, v ∈ GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ)`.

Introduce `v`. Conclude with `isOpen_discrete _`. Set `e : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ) →ₗ[ℂ] Z` to `(LinearMap.proj (R := ℂ) (φ := fun _ : G => Z) 1).comp ((GlobalTheory.PRep.indSpace H σ).subtype.comp (GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ)).subtype)`. Establish `he_inj : Function.Injective e`. Introduce `v w hvw`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Rewrite using `[Subsingleton.elim g 1]`. Conclude with `hvw`.

Establish `he_surj : Function.Surjective e` using `fun z => ⟨⟨⟨fun _ => z, hmem z⟩, hsmooth _⟩, rfl⟩`. Conclude with `(LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩).finrank_eq`.
-/
theorem finrank_smoothPart_ind [TopologicalSpace G] [IsTopologicalGroup G] {Z : Type} [AddCommGroup Z]
    [Module ℂ Z] (H : Subgroup G) (σ : Representation ℂ H Z) :
    Module.finrank ℂ (smoothPart (ind H σ)) = Module.finrank ℂ Z := by
  haveI : DiscreteTopology G := Subsingleton.discreteTopology
  have hmem : ∀ z : Z, (fun _ : G => z) ∈ GlobalTheory.PRep.indSpace H σ := by
    intro z
    simp [GlobalTheory.PRep.indSpace, Subsingleton.elim _ (1 : H)]
  have hsmooth : ∀ v : GlobalTheory.PRep.indSpace H σ,
      v ∈ GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ) := by
    intro v
    exact isOpen_discrete _
  let e : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ) →ₗ[ℂ] Z :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : G => Z) 1).comp
      ((GlobalTheory.PRep.indSpace H σ).subtype.comp
        (GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ)).subtype)
  have he_inj : Function.Injective e := by
    intro v w hvw
    apply Subtype.ext
    apply Subtype.ext
    funext g
    rw [Subsingleton.elim g 1]
    exact hvw
  have he_surj : Function.Surjective e := fun z => ⟨⟨⟨fun _ => z, hmem z⟩, hsmooth _⟩, rfl⟩
  exact (LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩).finrank_eq

end GL0

instance subsingleton_GL0 : Subsingleton (GL (Fin 0) k) := inferInstance

/- English proof (translation)
Introduce `h₁ h₂`. Use `haveI : Subsingleton (GL (Fin (0 + 0)) k) := PositivityTheory.PfBern.Props2.subsingleton_GL0`. Rewrite `h₁`, `h₂`, the goal using `[PositivityTheory.PfBern.Props2.isIrreducible_iff_finrank]`. Use `erw [PositivityTheory.PfBern.Props2.finrank_smoothPart_ind]`. Rewrite using `[Module.finrank_tensorProduct (R := ℂ) (S := ℂ), h₁, h₂]`.
-/
theorem prodGL0Irreducible_at (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin 0) k) V) (π₂ : Representation ℂ (GL (Fin 0) k) W) :
    π₁.IsIrreducible → π₂.IsIrreducible → (prod₂ π₁ π₂).IsIrreducible := by
  intro h₁ h₂
  haveI : Subsingleton (GL (Fin (0 + 0)) k) := PositivityTheory.PfBern.Props2.subsingleton_GL0
  rw [PositivityTheory.PfBern.Props2.isIrreducible_iff_finrank] at h₁ h₂ ⊢
  erw [PositivityTheory.PfBern.Props2.finrank_smoothPart_ind]
  rw [Module.finrank_tensorProduct (R := ℂ) (S := ℂ), h₁, h₂]

end PositivityTheory.PfBern.Props2
