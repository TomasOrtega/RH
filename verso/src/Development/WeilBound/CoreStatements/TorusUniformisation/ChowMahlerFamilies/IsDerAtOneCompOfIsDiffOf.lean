import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FunctionDerivativeEndomorphism

/- English proof (translation)
Unfold `BT.valAt`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE v F ⊤ ⊤ ⊤ le_top le_top]`. Both sides reduce to the same expression.
-/
theorem valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (v : Spec (CommRingCat.of B) ⟶ X) (F : X ⟶ Y)
    (s : Γ(Y, ⊤)) :
    BT.valAt v ⊤ le_top ((F.appLE ⊤ ⊤ le_top).hom s) = BT.valAt (v ≫ F) ⊤ le_top s := by
  unfold BT.valAt
  rw [← Scheme.Hom.appLE_comp_appLE v F ⊤ ⊤ ⊤ le_top le_top]
  rfl

/- English proof (translation)
Set `g₀ : Over.mk (Γ.G.hom ≫ x) ⟶ G` to `Over.homMk i h.isOver`. Establish `h0 : g₀ ^ N = 1` using `(h.kernel Γ.G g₀).2 ⟨𝟙 _, by simp [g₀]⟩`. Establish `h1 : (g₀ ≫ a) ^ N = 1`. Rewrite using `[← MonObj.pow_comp, h0, MonObj.one_comp]`. Take `⟨b, hb⟩` from `(h.kernel Γ.G (g₀ ≫ a)).1 h1`.

Conclude with `⟨b, hb⟩`.
-/
theorem exists_endo {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : QFGroup R T) {S : Scheme.{0}}
    (G : Over S) [GrpObj G] (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left) (N : ℕ)
    (h : Γ.IsTorsionAlong G x N i) (a : G ⟶ G) [IsMonHom a] :
    ∃ b : Γ.G ⟶ Γ.G, b.left ≫ i = i ≫ a.left := by
  let g₀ : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have h0 : g₀ ^ N = 1 := (h.kernel Γ.G g₀).2 ⟨𝟙 _, by simp [g₀]⟩
  have h1 : (g₀ ≫ a) ^ N = 1 := by
    rw [← MonObj.pow_comp, h0, MonObj.one_comp]
  obtain ⟨b, hb⟩ := (h.kernel Γ.G (g₀ ≫ a)).1 h1
  exact ⟨b, hb⟩

end PositivityTheory.Xgn.FunctionDerivativeEndomorphism

/- English proof (translation)
Introduce `R _ _ T _ Γ S G _ _ x i N h L _ _ M a _ B hB α hα f w hd`. Take `⟨b, hb⟩` from `PositivityTheory.Xgn.FunctionDerivativeEndomorphism.exists_endo Γ G x i N h a`. Take `⟨s, hs, hv⟩` from `hd`. Use `⟨(b.left.appLE ⊤ ⊤ le_top).hom s, ?_, ?_⟩` and prove the remaining obligations. Introduce `t`.

Rewrite using `[PositivityTheory.Xgn.FunctionDerivativeEndomorphism.valAt_comp]`. Establish `ht : Γ.pt t ≫ b = Γ.pt (α t)` using `h.inj _ _ _ (by`. Rewrite using `[Over.comp_left, Category.assoc, hb, hα])`. Establish `e` using `congrArg Over.Hom.left ht`. Rewrite `e` using `[Over.comp_left]`.

Rewrite using `[e]`. Conclude with `hs (α t)`. Introduce `e`. Take `⟨v, hv1, hv2, -⟩` from `hv e`. Take `⟨v', hv1', hv2', hv3'⟩` from `hv (B e)`.

Use `⟨v, hv1, hv2, ?_⟩` and prove the remaining obligations. Rewrite using `[PositivityTheory.Xgn.FunctionDerivativeEndomorphism.valAt_comp]`. Set `Y : Over (Spec (CommRingCat.of R))` to `Over.mk (v' ≫ Γ.G.hom)`. Establish `hw : (v ≫ b.left) ≫ Γ.G.hom = Y.hom`. Simplify using `only [Y, Over.mk_hom, Category.assoc, Over.w]`.

Rewrite using `[hv1, hv1']`. Establish `hvv` using `h.inj Y (Over.homMk (v ≫ b.left) hw) (Over.homMk v' rfl) (by`. Simplify using `only [Over.homMk_left, Category.assoc]`. Rewrite using `[hb, ← Category.assoc, hv2, hv2', hB e, Over.comp_left, Category.assoc])`. Establish `e2` using `congrArg Over.Hom.left hvv`.

Simplify using `only [Over.homMk_left] at e2`. Rewrite using `[e2, hv3']`. Simplify using `only [LinearMap.comp_apply, map_one]`.
-/
theorem PositivityTheory.Xgn.isDerAtOne_comp_of_isDiffOf : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (i : Γ.G.left ⟶ G.left) (N : ℕ), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (a : G ⟶ G) [IsMonHom a] (B : L →ₗ[R] L), M.IsDiffOf a B → ∀ (α : T →* T), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) → ∀ (f : T → R) (w : Module.Dual R L), Γ.IsDerAtOne i M N f w → Γ.IsDerAtOne i M N (fun t => f (α t)) (w ∘ₗ B) := by
  intro R _ _ T _ Γ S G _ _ x i N h L _ _ M a _ B hB α hα f w hd
  obtain ⟨b, hb⟩ := PositivityTheory.Xgn.FunctionDerivativeEndomorphism.exists_endo Γ G x i N h a
  obtain ⟨s, hs, hv⟩ := hd
  refine ⟨(b.left.appLE ⊤ ⊤ le_top).hom s, ?_, ?_⟩
  · intro t
    rw [PositivityTheory.Xgn.FunctionDerivativeEndomorphism.valAt_comp]
    have ht : Γ.pt t ≫ b = Γ.pt (α t) := h.inj _ _ _ (by
      rw [Over.comp_left, Category.assoc, hb, hα])
    have e := congrArg Over.Hom.left ht
    rw [Over.comp_left] at e
    rw [e]
    exact hs (α t)
  · intro e
    obtain ⟨v, hv1, hv2, -⟩ := hv e
    obtain ⟨v', hv1', hv2', hv3'⟩ := hv (B e)
    refine ⟨v, hv1, hv2, ?_⟩
    rw [PositivityTheory.Xgn.FunctionDerivativeEndomorphism.valAt_comp]
    let Y : Over (Spec (CommRingCat.of R)) := Over.mk (v' ≫ Γ.G.hom)
    have hw : (v ≫ b.left) ≫ Γ.G.hom = Y.hom := by
      simp only [Y, Over.mk_hom, Category.assoc, Over.w]
      rw [hv1, hv1']
    have hvv := h.inj Y (Over.homMk (v ≫ b.left) hw) (Over.homMk v' rfl) (by
      simp only [Over.homMk_left, Category.assoc]
      rw [hb, ← Category.assoc, hv2, hv2', hB e, Over.comp_left, Category.assoc])
    have e2 := congrArg Over.Hom.left hvv
    simp only [Over.homMk_left] at e2
    rw [e2, hv3']
    simp only [LinearMap.comp_apply, map_one]
