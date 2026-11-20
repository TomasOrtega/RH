import Development.EtaleCohomology.EtaleSheaves.KummerInduction
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.ContStepPf LateralTheory.E.StepKPf

namespace LateralTheory.E.RestrPf

/- English proof (translation)
Rewrite using `[Functor.map_comp, pull_comp, h, map_zero]`.
-/
theorem pull_zero {q : ℕ} {n i : ℤ} {A B C : Scheme.{0}} (a : A ⟶ B) (b : B ⟶ C) (y : Ht q (sch.obj C) n i)
    (h : pull _ (sch.map b) _ _ y = 0) : pull _ (sch.map (a ≫ b)) _ _ y = 0 := by
  rw [Functor.map_comp, pull_comp, h, map_zero]

/- English proof (translation)
Introduce `h q J _ _ D c hc ha hcs hqs hu j0 X e U hU pU`. Establish `: ∀ {a b : J} (g : a ⟶ b), IsAffineHom (D.map g)` using `ha`. Set `W : (D.obj j0).Opens` to `e.hom ⁻¹ᵁ U`. Establish `haff : ∀ {a b : Over j0} (g : a ⟶ b), IsAffineHom ((opensDiagram D j0 W).map g)` using `fun g => inferInstance`. Establish `hcpt : ∀ a : Over j0, CompactSpace ((opensDiagram D j0 W).obj a)` using `fun a => isCompact_iff_compactSpace.mp ((D.map a.hom).isCompact_preimage hU)`.

Establish `hqs' : ∀ a : Over j0, QuasiSeparatedSpace ((opensDiagram D j0 W).obj a)` using `fun a => by`. Use `hqs a.left` as an intermediate fact. Conclude with `(D.map a.hom ⁻¹ᵁ W).isOpen.isOpenEmbedding_subtypeVal.quasiSeparatedSpace`. Establish `hu' : ∀ a : Over j0, IsUnit (q : Γ((opensDiagram D j0 W).obj a, ⊤))` using `fun a => by show IsUnit (q : Γ((D.map a.hom ⁻¹ᵁ W).toScheme, ⊤))`. Simplify using `using (hu a.left).map (Scheme.Hom.appTop (Scheme.Opens.ι (D.map a.hom ⁻¹ᵁ W))).hom`.

Establish `hiso : Nonempty ((opensDiagram D j0 W).obj (Over.mk (𝟙 j0)) ≅ U.toScheme)`. Use `⟨(D.obj j0).isoOfEq ?_ ≪≫ asIso (e.hom ∣_ U)⟩` and prove the remaining obligations. Simplify using `[W]`. Establish `P` using `pU q (opensDiagram D j0 W) (opensCone D c j0 W) (isLimitOpensCone D c hc j0 W) haff hcpt hqs' hu' (Over.mk (𝟙 j0)) hiso`. Introduce `n i`.

Take `⟨P1, P2⟩` from `P n i`. Use `⟨fun x => ?_, fun k f y hy => ?_⟩` and prove the remaining obligations. Take `⟨j', y, hy⟩` from `P1 x`. Conclude with `⟨j'.left, j'.hom, y, hy⟩`. Take `⟨k', g', hg'⟩` from `P2 (Over.mk f) y hy`.

Use `⟨k'.left, g'.left, ?_⟩` and prove the remaining obligations. Establish `hle : lv D e U (g'.left ≫ f) ≤ D.map k'.hom ⁻¹ᵁ W`. Rewrite using `[← Over.w g']`. Conclude with `le_rfl`. Set `ι0 : (lv D e U (g'.left ≫ f)).toScheme ⟶ (opensDiagram D j0 W).obj k'` to `(D.obj k'.left).homOfLE hle`.

Establish `heq : rD D e U f g'.left = ι0 ≫ (opensDiagram D j0 W).map g'`. Apply `(cancel_mono (lv D e U f).ι).mp` to reduce the goal to its premises. Establish `e1 : (opensDiagram D j0 W).map g' ≫ (D.map (Over.mk f).hom ⁻¹ᵁ W).ι = (D.map k'.hom ⁻¹ᵁ W).ι ≫ D.map g'.left` using `Scheme.Hom.resLE_comp_ι _ _`. Establish `e2 : ι0 ≫ (D.map k'.hom ⁻¹ᵁ W).ι = (lv D e U (g'.left ≫ f)).ι` using `Scheme.homOfLE_ι _ _`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[heq]`. Conclude with `pull_zero ι0 ((opensDiagram D j0 W).map g') y hg'`.
-/
theorem Restr_of : Restr := by
  intro h q J _ _ D c hc ha hcs hqs hu j0 X e U hU pU
  have : ∀ {a b : J} (g : a ⟶ b), IsAffineHom (D.map g) := ha
  let W : (D.obj j0).Opens := e.hom ⁻¹ᵁ U
  have haff : ∀ {a b : Over j0} (g : a ⟶ b), IsAffineHom ((opensDiagram D j0 W).map g) := fun g => inferInstance
  have hcpt : ∀ a : Over j0, CompactSpace ((opensDiagram D j0 W).obj a) := fun a =>
    isCompact_iff_compactSpace.mp ((D.map a.hom).isCompact_preimage hU)
  have hqs' : ∀ a : Over j0, QuasiSeparatedSpace ((opensDiagram D j0 W).obj a) := fun a => by
    have := hqs a.left
    exact (D.map a.hom ⁻¹ᵁ W).isOpen.isOpenEmbedding_subtypeVal.quasiSeparatedSpace
  have hu' : ∀ a : Over j0, IsUnit (q : Γ((opensDiagram D j0 W).obj a, ⊤)) := fun a => by
    show IsUnit (q : Γ((D.map a.hom ⁻¹ᵁ W).toScheme, ⊤))
    simpa using (hu a.left).map (Scheme.Hom.appTop (Scheme.Opens.ι (D.map a.hom ⁻¹ᵁ W))).hom
  have hiso : Nonempty ((opensDiagram D j0 W).obj (Over.mk (𝟙 j0)) ≅ U.toScheme) := by
    refine ⟨(D.obj j0).isoOfEq ?_ ≪≫ asIso (e.hom ∣_ U)⟩
    simp [W]
  have P := pU q (opensDiagram D j0 W) (opensCone D c j0 W) (isLimitOpensCone D c hc j0 W) haff hcpt hqs' hu'
    (Over.mk (𝟙 j0)) hiso
  intro n i
  obtain ⟨P1, P2⟩ := P n i
  refine ⟨fun x => ?_, fun k f y hy => ?_⟩
  · obtain ⟨j', y, hy⟩ := P1 x
    exact ⟨j'.left, j'.hom, y, hy⟩
  · obtain ⟨k', g', hg'⟩ := P2 (Over.mk f) y hy
    refine ⟨k'.left, g'.left, ?_⟩
    have hle : lv D e U (g'.left ≫ f) ≤ D.map k'.hom ⁻¹ᵁ W := by
      rw [← Over.w g']; exact le_rfl
    let ι0 : (lv D e U (g'.left ≫ f)).toScheme ⟶ (opensDiagram D j0 W).obj k' := (D.obj k'.left).homOfLE hle
    have heq : rD D e U f g'.left = ι0 ≫ (opensDiagram D j0 W).map g' := by
      apply (cancel_mono (lv D e U f).ι).mp
      have e1 : (opensDiagram D j0 W).map g' ≫ (D.map (Over.mk f).hom ⁻¹ᵁ W).ι =
          (D.map k'.hom ⁻¹ᵁ W).ι ≫ D.map g'.left := Scheme.Hom.resLE_comp_ι _ _
      have e2 : ι0 ≫ (D.map k'.hom ⁻¹ᵁ W).ι = (lv D e U (g'.left ≫ f)).ι := Scheme.homOfLE_ι _ _
      calc rD D e U f g'.left ≫ (lv D e U f).ι = (lv D e U (g'.left ≫ f)).ι ≫ D.map g'.left :=
            Scheme.Hom.resLE_comp_ι _ _
        _ = (ι0 ≫ (D.map k'.hom ⁻¹ᵁ W).ι) ≫ D.map g'.left := by rw [e2]
        _ = ι0 ≫ ((D.map k'.hom ⁻¹ᵁ W).ι ≫ D.map g'.left) := Category.assoc _ _ _
        _ = ι0 ≫ ((opensDiagram D j0 W).map g' ≫ (D.map (Over.mk f).hom ⁻¹ᵁ W).ι) :=
            congrArg (fun t => ι0 ≫ t) e1.symm
        _ = (ι0 ≫ (opensDiagram D j0 W).map g') ≫ (lv D e U f).ι := (Category.assoc _ _ _).symm
    rw [heq]; exact pull_zero ι0 ((opensDiagram D j0 W).map g') y hg'

end LateralTheory.E.RestrPf
