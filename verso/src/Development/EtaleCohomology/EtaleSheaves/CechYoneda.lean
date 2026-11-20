import Development.EtaleCohomology.EtaleSheaves.CechSigmaOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigma_xy1Pf_Yo
open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev

def eW {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    yoneda.obj (widePullback B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≅
      widePullback (yoneda.obj B) (fun _ : Fin (n + 1) => yoneda.obj A) (fun _ => yoneda.map p) :=
  preservesLimitIso yoneda (WidePullbackShape.wideCospan B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≪≫
    HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

/- English proof (translation)
Simplify using `only [eW, Iso.trans_hom, WidePullback.π]`. Use `erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]`. Simplify using `only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]`. Conclude with `Category.comp_id _`.
-/
theorem eW_π {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) (i : Fin (n + 1)) :
    (eW p n).hom ≫ WidePullback.π _ i = yoneda.map (WidePullback.π _ i) := by
  simp only [eW, Iso.trans_hom, WidePullback.π]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

/- English proof (translation)
Simplify using `only [eW, Iso.trans_hom, WidePullback.base]`. Use `erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]`. Simplify using `only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]`. Conclude with `Category.comp_id _`.
-/
theorem eW_base {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    (eW p n).hom ≫ WidePullback.base _ = yoneda.map (WidePullback.base _) := by
  simp only [eW, Iso.trans_hom, WidePullback.base]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

/- English proof (translation)
Introduce `A B C D p q s n`. Use `⟨(Arrow.isoMk (eW p n) (eW q n) ?_).symm⟩` and prove the remaining obligations. Apply `WidePullback.hom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `only [Arrow.mk_hom, Category.assoc]`.

Use `erw [Arrow.mapCechNerve_app, WidePullback.lift_π]`. Use `erw [← Category.assoc, eW_π, Category.assoc, eW_π]`. Express the relevant statement in the definitionally equal form `yoneda.map _ ≫ yoneda.map s.left = yoneda.map _ ≫ yoneda.map _`. Simplify using `only [wpMap]`. Use `erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_π]`.

Simplify using `only [Arrow.mk_hom, Category.assoc] erw [Arrow.mapCechNerve_app, WidePullback.lift_base] erw [← Category.assoc, eW_base, Category.assoc, eW_base]`. Express the relevant statement in the definitionally equal form `yoneda.map _ ≫ yoneda.map s.right = yoneda.map _ ≫ yoneda.map _`. Simplify using `only [wpMap]`. Use `erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_base]`.
-/
theorem cechYoneda : CechYoneda := by
  intro A B C D p q s n
  refine ⟨(Arrow.isoMk (eW p n) (eW q n) ?_).symm⟩
  apply WidePullback.hom_ext
  · intro i
    simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_π]
    erw [← Category.assoc, eW_π, Category.assoc, eW_π]
    change yoneda.map _ ≫ yoneda.map s.left = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_π]
  · simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_base]
    erw [← Category.assoc, eW_base, Category.assoc, eW_base]
    change yoneda.map _ ≫ yoneda.map s.right = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_base]

/- English proof (translation)
The claim follows from `LateralTheory.E.CechSigma_xy1Pf_Lev.CechSigma_of cechYoneda hS`.
-/
theorem CechSigma_of (hS : SchemeLevel) : ZariskiLocalCech.CechSigma :=
  LateralTheory.E.CechSigma_xy1Pf_Lev.CechSigma_of cechYoneda hS

end LateralTheory.E.CechSigma_xy1Pf_Yo
