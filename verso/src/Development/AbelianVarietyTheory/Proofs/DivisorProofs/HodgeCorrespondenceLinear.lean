import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeSub

/- English proof (translation)
Establish `E : hV.fromSpec.appLE V ⊤ e = (Scheme.ΓSpecIso Γ(T, V)).inv`. Rewrite using `[Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]`. Rewrite using `[show (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id, Category.comp_id]`. Rewrite using `[E]`. Conclude with `Iso.inv_hom_id_apply _ _`.
-/
theorem gammaSpecIso_fromSpec_appLE {T : Scheme.{0}} {V : T.Opens} (hV : IsAffineOpen V)
    (e : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V) (r : Γ(T, V)) :
    (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom (hV.fromSpec.appLE V ⊤ e r) = r := by
  have E : hV.fromSpec.appLE V ⊤ e = (Scheme.ΓSpecIso Γ(T, V)).inv := by
    rw [Scheme.Hom.appLE, hV.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rw [show (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [E]
  exact Iso.inv_hom_id_apply _ _

/- English proof (translation)
Introduce `T A _ V hV s s' c c' r hs hs'`. Use `⟨fun v h hv w we => ?_, fun v h hv w we => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hs v h hv w we, hs' v h hv w we, map_add]`. Establish `key : ∀ (a b : Γ((Scheme.Modules.pullback hV.fromSpec).obj (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A), ⊤)), (GlobalTheory.TanFibre.form w we).app ⊤ (a + b) = (GlobalTheory.TanFibre.form w we).app ⊤ a + (GlobalTheory.TanFibre.form w we).app ⊤ b` using `fun a b => map_add _ a b`. Establish `key2 : ∀ (y z : Γ(structureModule (Sp Γ(T, V)), ⊤)), (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom (y + z) = (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom y + (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom z` using `fun y z => map_add _ y z`.

Rewrite using `[key, key2]`. Rewrite using `[map_smul, hs v h hv w we, GlobalTheory.QCoh.pullbackSections_smul]`. Establish `key : ∀ (a : Γ(Sp Γ(T, V), ⊤)) (x : Γ((Scheme.Modules.pullback hV.fromSpec).obj (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A), ⊤)), (GlobalTheory.TanFibre.form w we).app ⊤ (a • x) = a • (GlobalTheory.TanFibre.form w we).app ⊤ x` using `fun a x => Scheme.Modules.Hom.app_smul _ a x`. Establish `key2 : ∀ (a : Γ(Sp Γ(T, V), ⊤)) (y : Γ(structureModule (Sp Γ(T, V)), ⊤)), (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom (a • y) = (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom a * (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom y` using `fun a y => map_mul _ a y`. Rewrite using `[key, key2, gammaSpecIso_fromSpec_appLE, smul_eq_mul]`.
-/
theorem corr_add_smul : ∀ {T : Scheme.{0}} (A : Over T) [GrpObj A] (V : T.Opens) (hV : IsAffineOpen V)
    (s s' : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V)) (c c' : primDR (onAff A hV)) (r : Γ(T, V)),
    GlobalTheory.HodgeSub.Corr A hV s c → GlobalTheory.HodgeSub.Corr A hV s' c' →
      GlobalTheory.HodgeSub.Corr A hV (s + s') (c + c') ∧ GlobalTheory.HodgeSub.Corr A hV (r • s) (r • c) := by
  intro T A _ V hV s s' c c' r hs hs'
  refine ⟨fun v h hv w we => ?_, fun v h hv w we => ?_⟩
  · rw [map_add, hs v h hv w we, hs' v h hv w we, map_add]
    have key : ∀ (a b : Γ((Scheme.Modules.pullback hV.fromSpec).obj (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A), ⊤)),
        (GlobalTheory.TanFibre.form w we).app ⊤ (a + b) = (GlobalTheory.TanFibre.form w we).app ⊤ a + (GlobalTheory.TanFibre.form w we).app ⊤ b :=
      fun a b => map_add _ a b
    have key2 : ∀ (y z : Γ(structureModule (Sp Γ(T, V)), ⊤)),
        (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom (y + z) =
          (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom y + (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom z :=
      fun y z => map_add _ y z
    rw [key, key2]
  · rw [map_smul, hs v h hv w we, GlobalTheory.QCoh.pullbackSections_smul]
    have key : ∀ (a : Γ(Sp Γ(T, V), ⊤)) (x : Γ((Scheme.Modules.pullback hV.fromSpec).obj (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A), ⊤)),
        (GlobalTheory.TanFibre.form w we).app ⊤ (a • x) = a • (GlobalTheory.TanFibre.form w we).app ⊤ x :=
      fun a x => Scheme.Modules.Hom.app_smul _ a x
    have key2 : ∀ (a : Γ(Sp Γ(T, V), ⊤)) (y : Γ(structureModule (Sp Γ(T, V)), ⊤)),
        (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom (a • y) =
          (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom a * (Scheme.ΓSpecIso (CommRingCat.of Γ(T, V))).hom y :=
      fun a y => map_mul _ a y
    rw [key, key2, gammaSpecIso_fromSpec_appLE, smul_eq_mul]

end GlobalTheory.HodgeSub
