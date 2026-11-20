import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsBasisIsoFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

variable {Y : Scheme.{u}}

def globalSectionFamily (M : Y.Modules) (t : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun V => (M.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom t)
    (fun V W f => by
      change (M.presheaf.map f).hom ((M.presheaf.map _).hom t) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

def basisHom (M : Y.Modules) {n : ℕ} (s : Fin n → Γ(M, ⊤)) : freeModule Y n ⟶ M :=
  (SheafOfModules.freeHomEquiv M).symm (fun i => globalSectionFamily M (s i.down))

/- English proof (translation)
Establish `h1 : SheafOfModules.ιFree (R` using `Y.ringCatSheaf) (ULift.up i) ≫ basisHom M s = M.unitHomEquiv.symm (globalSectionFamily M (s i)) := by`. Use `(SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (basisHom M s) (ULift.up i)).symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `congrFun ((SheafOfModules.freeHomEquiv M).apply_symm_apply _) (ULift.up i)`. Establish `e1 : (M.unitHomEquiv (SheafOfModules.ιFree (R` using `Y.ringCatSheaf) (ULift.up i) ≫ basisHom M s)).val (op ⊤) = (globalSectionFamily M (s i)).val (op ⊤) := by`.

Use `congrArg (fun φ => (M.unitHomEquiv φ).val (op ⊤)) h1` as an intermediate fact. Simplify `this` using `only [Equiv.apply_symm_apply]`. Establish `e2 : (M.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op).hom (s i) = s i`. Rewrite using `[show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]`. Simplify using the standard rewrite rules.

Conclude with `e1.trans (by exact e2)`.
-/
theorem basisHom_app_stdSection (M : Y.Modules) {n : ℕ} (s : Fin n → Γ(M, ⊤)) (i : Fin n) :
    ((basisHom M s).app ⊤).hom (stdSection Y n i) = s i := by
  have h1 : SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i) ≫ basisHom M s =
      M.unitHomEquiv.symm (globalSectionFamily M (s i)) := by
    refine (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (basisHom M s) (ULift.up i)).symm.trans ?_
    congr 1
    exact congrFun ((SheafOfModules.freeHomEquiv M).apply_symm_apply _) (ULift.up i)
  have e1 : (M.unitHomEquiv (SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i) ≫
      basisHom M s)).val (op ⊤) = (globalSectionFamily M (s i)).val (op ⊤) := by
    have := congrArg (fun φ => (M.unitHomEquiv φ).val (op ⊤)) h1
    simpa only [Equiv.apply_symm_apply] using this
  have e2 : (M.presheaf.map (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op).hom (s i) = s i := by
    rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
    simp
  exact e1.trans (by exact e2)

/- English proof (translation)
Introduce `Y M n s hs`. Set `ψ` to `basisHom M s`. Establish `key : ∀ V : Y.Opens, (ψ.app V).hom ∘ (fun r : Fin n → Γ(Y, V) => ∑ i, r i • ((freeModule Y n).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (stdSection Y n i)) = (fun r : Fin n → Γ(Y, V) => ∑ i, r i • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (s i))`. Introduce `V`. Use function extensionality and compare the values at `r`.

Simplify using `only [Function.comp_apply, map_sum, Scheme.Modules.Hom.app_smul, app_map_apply, ψ, basisHom_app_stdSection]`. Establish `hV : ∀ V : Y.Opens, IsIso (ψ.app V)` using `fun V => (ConcreteCategory.isIso_iff_bijective _).mpr ((Function.Bijective.of_comp_iff _ (h Y n V le_top)).mp (by rw [key V]; exact hs V le_top))`. Establish `: IsIso ψ` using `Scheme.Modules.Hom.isIso_iff_isIso_app.mpr hV`. Conclude with `⟨(asIso ψ).symm⟩`.
-/
theorem BasisIsoFree.proof (h : FreeSheafBasis.Statement.{u}) : BasisIsoFree.Statement.{u} := by
  intro Y M n s hs
  let ψ := basisHom M s
  have key : ∀ V : Y.Opens, (ψ.app V).hom ∘
      (fun r : Fin n → Γ(Y, V) => ∑ i, r i •
        ((freeModule Y n).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (stdSection Y n i)) =
      (fun r : Fin n → Γ(Y, V) => ∑ i, r i • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (s i)) := by
    intro V
    funext r
    simp only [Function.comp_apply, map_sum, Scheme.Modules.Hom.app_smul, app_map_apply, ψ,
      basisHom_app_stdSection]
  have hV : ∀ V : Y.Opens, IsIso (ψ.app V) := fun V =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ((Function.Bijective.of_comp_iff _ (h Y n V le_top)).mp (by rw [key V]; exact hs V le_top))
  have : IsIso ψ := Scheme.Modules.Hom.isIso_iff_isIso_app.mpr hV
  exact ⟨(asIso ψ).symm⟩

end

end GroundTheory.Heights₂.Heights.Model
