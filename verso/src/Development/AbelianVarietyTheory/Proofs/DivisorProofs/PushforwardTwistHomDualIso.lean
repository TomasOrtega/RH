import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistHomModuleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushforwardHomAdjunctionIsoStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjFml

def homIsoLeft {X : Scheme.{0}} {F F' : X.Modules} (e : F ≅ F') (G : X.Modules) :
    homMod F G ≅ homMod F' G where
  hom := homMap e.inv (𝟙 G)
  inv := homMap e.hom (𝟙 G)
  hom_inv_id := by
    ext V φ : 3
    refine hom_ext fun W h s => ?_
    change homApp φ h ((e.hom ≫ e.inv).app W s) = _
    rw [e.hom_inv_id]; rfl
  inv_hom_id := by
    ext V φ : 3
    refine hom_ext fun W h s => ?_
    change homApp φ h ((e.inv ≫ e.hom).app W s) = _
    rw [e.inv_hom_id]; rfl

/- English proof (translation)
Use `h.isIso_toBidual_of_local_frames` as an intermediate fact. Establish `hθ : IsIso (DualPull.theta ρ (dual E))` using `DualPull.isIso_theta ρ h.dual`. Set `e₁ : (Scheme.Modules.pullback ρ).obj E ≅ homMod ((Scheme.Modules.pullback ρ).obj (dual E)) (structureModule Y)` to `(Scheme.Modules.pullback ρ).mapIso (asIso (cartierDualToBidual E)) ≪≫ @asIso _ _ _ _ (DualPull.theta ρ (dual E)) hθ`. Take `⟨e₂⟩` from `GlobalTheory.T.twist_hom_module_iso Y ((Scheme.Modules.pullback ρ).obj (dual E)) (structureModule Y) M`. Take `⟨e₃⟩` from `GlobalTheory.T.pushforward_hom_adjunction_iso X Y ρ (dual E) (twist (structureModule Y) M)`.

Conclude with `⟨(Scheme.Modules.pushforward ρ).mapIso ((twistFunctor M).mapIso e₁ ≪≫ e₂) ≪≫ e₃⟩`.
-/
theorem nonempty_iso_dual (X Y : Scheme.{0}) (ρ : Y ⟶ X) (E : X.Modules) (r : ℕ) (h : IsVB E r)
    (M : LB Y) :
    Nonempty ((Scheme.Modules.pushforward ρ).obj (twist ((Scheme.Modules.pullback ρ).obj E) M) ≅
      homMod (dual E) ((Scheme.Modules.pushforward ρ).obj (twist (structureModule Y) M))) := by
  have := h.isIso_toBidual_of_local_frames
  have hθ : IsIso (DualPull.theta ρ (dual E)) := DualPull.isIso_theta ρ h.dual
  let e₁ : (Scheme.Modules.pullback ρ).obj E ≅
      homMod ((Scheme.Modules.pullback ρ).obj (dual E)) (structureModule Y) :=
    (Scheme.Modules.pullback ρ).mapIso (asIso (cartierDualToBidual E)) ≪≫
      @asIso _ _ _ _ (DualPull.theta ρ (dual E)) hθ
  obtain ⟨e₂⟩ := GlobalTheory.T.twist_hom_module_iso Y ((Scheme.Modules.pullback ρ).obj (dual E)) (structureModule Y) M
  obtain ⟨e₃⟩ := GlobalTheory.T.pushforward_hom_adjunction_iso X Y ρ (dual E) (twist (structureModule Y) M)
  exact ⟨(Scheme.Modules.pushforward ρ).mapIso ((twistFunctor M).mapIso e₁ ≪≫ e₂) ≪≫ e₃⟩

/- English proof (translation)
Introduce `X Y ρ E r h M _`. Use `⟨nonempty_iso_dual X Y ρ E r h M, ?_⟩` and prove the remaining obligations. Use `h.isIso_toBidual_of_local_frames` as an intermediate fact. Take `⟨e⟩` from `nonempty_iso_dual X Y ρ (dual E) r h.dual M`. Conclude with `⟨e ≪≫ homIsoLeft (asIso (cartierDualToBidual E)).symm _⟩`.
-/
theorem projection_formula : ∀ (X Y : Scheme.{0}) (ρ : Y ⟶ X) (E : X.Modules) (r : ℕ), IsVB E r → ∀ (M : LB Y), M.IsLB → Nonempty ((Scheme.Modules.pushforward ρ).obj (twist ((Scheme.Modules.pullback ρ).obj E) M) ≅ homMod (dual E) ((Scheme.Modules.pushforward ρ).obj (twist (structureModule Y) M))) ∧ Nonempty ((Scheme.Modules.pushforward ρ).obj (twist ((Scheme.Modules.pullback ρ).obj (dual E)) M) ≅ homMod E ((Scheme.Modules.pushforward ρ).obj (twist (structureModule Y) M))) := by
  intro X Y ρ E r h M _
  refine ⟨nonempty_iso_dual X Y ρ E r h M, ?_⟩
  have := h.isIso_toBidual_of_local_frames
  obtain ⟨e⟩ := nonempty_iso_dual X Y ρ (dual E) r h.dual M
  exact ⟨e ≪≫ homIsoLeft (asIso (cartierDualToBidual E)).symm _⟩

end GlobalTheory.ProjFml
