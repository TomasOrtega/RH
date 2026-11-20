import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntOIsLocalRing
import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanActMat

attribute [local instance] Over.cartesianMonoidalCategory

open scoped MonObj

/- English proof (translation)
Introduce `E _ _ _ H X t R _ x g e he`. Establish `h1 : spMap (RingHom.id R) = 𝟙 _` using `Spec.map_id _`. Establish `h2 : dualMap (RingHom.id R) = RingHom.id _`. Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [Formalism.L2.Pj.dualMap]`.

Establish `h3 : spMap (dualMap (RingHom.id R)) = 𝟙 _` using `by rw [h2]; exact Spec.map_id _`. Establish `hU : ∀ w, IsTanAtG t x w → ∃! a : Fin g → R, IsCombAtG t x e a w`. Establish `h` using `he.2 R (RingHom.id R)`. Simplify using `only [h1, h3, Category.id_comp] at h`. Conclude with `h`.

Set `u : Fin g → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G` to `fun i => GlobalTheory.LieMet.tanOf (he.1 i)`. Establish `hli : LinearIndependent R u`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `ha : IsCombAtG t x e c (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (0 : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G)).left` using `(GlobalTheory.LieMet.isComb_iff u c 0).2 hc.symm`.

Establish `hb : IsCombAtG t x e 0 (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (0 : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G)).left` using `(GlobalTheory.LieMet.isComb_iff u 0 0).2 (by simp)`. Use `(hU _ (GlobalTheory.LieMet.isTan_tv 0)).unique ha hb` as an intermediate fact. Introduce `i`. Conclude with `congrFun this i`. Establish `hsp : ⊤ ≤ Submodule.span R (Set.range u)`.

Introduce `W _`. Take `⟨a, ha, -⟩` from `hU _ (GlobalTheory.LieMet.isTan_tv W)`. Rewrite using `[(GlobalTheory.LieMet.isComb_iff u a W).1 ha]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Set `B` to `Module.Basis.mk hli hsp`.

Establish `hB : ∀ j, B j = u j` using `fun j => Module.Basis.mk_apply hli hsp j`. Set `ρ : 𝓞 E →+* Matrix (Fin g) (Fin g) R` to `(LinearMap.toMatrixAlgEquiv B).toRingHom.comp (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act)`. Establish `hcol : ∀ a i, IsCombAtG t x e (fun j => ρ a j i) (e i ≫ (t.act.act a).left)`. Introduce `a i`. Establish `hρ : (fun j => ρ a j i) = fun j => B.repr (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (u i)) j`.

Use function extensionality and compare the values at `j`. Use `show LinearMap.toMatrixAlgEquiv B (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a) j i = _`. Rewrite using `[LinearMap.toMatrixAlgEquiv_apply, hB]`. Rewrite using `[hρ]`. Use `(GlobalTheory.LieMet.isComb_iff u (fun j => B.repr (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (u i)) j) (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (u i))).2 ?_` and prove the remaining obligations.

Use `conv_lhs => rw [← B.sum_repr (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (u i))]`. Simplify using `only [hB]`. Use `⟨ρ, ?_⟩` and prove the remaining obligations. Introduce `K _ ψ a cf w hw`. Establish `hT : ∀ j, IsTanAtG t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e j)` using `fun j => GlobalTheory.LieMet.isTan_map ψ rfl (he.1 j)`.

Establish `hw' : IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ e j ≫ (t.act.act a).left) cf (w ≫ (t.act.act a).left)`. Use `t.act.hom a` as an intermediate fact. Establish `hw0` using `(isCombAtG_iff t _ (fun j => ovT (hT j)) cf w).1 hw`. Establish `h` using `(isCombAtG_iff t _ (fun j => ovT (hT j) ≫ t.act.act a) cf (w ≫ (t.act.act a).left)).2 (by`. Rewrite using `[← combT_post, Over.comp_left, hw0])`.

Conclude with `h`. Use `tanLinG _ hT _ _ cf _ (fun i => ?_) hw'` and prove the remaining obligations. Establish `h` using `GlobalTheory.LatDRFree.comb_map t ψ (hcol a i)`. Conclude with `h`.
-/
theorem exists_actMatrix_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), GlobalTheory.LineNorm.IsTanBasis t x e → ∃ ρ : 𝓞 E →+* Matrix (Fin g) (Fin g) R, ∀ (K : Type) [CommRing K] (ψ : R →+* K) (a : 𝓞 E) (cf : Fin g → K) (w : Sp (DualNumber K) ⟶ t.G.left), IsCombAtG t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) cf w → IsCombAtG t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ e i) (((ρ a).map ψ).mulVec cf) (w ≫ (t.act.act a).left) := by
  intro E _ _ _ H X t R _ x g e he
  classical
  have h1 : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap]
  have h3 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hU : ∀ w, IsTanAtG t x w → ∃! a : Fin g → R, IsCombAtG t x e a w := by
    have h := he.2 R (RingHom.id R)
    simp only [h1, h3, Category.id_comp] at h
    exact h
  let u : Fin g → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G := fun i => GlobalTheory.LieMet.tanOf (he.1 i)
  have hli : LinearIndependent R u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have ha : IsCombAtG t x e c (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (0 : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G)).left :=
      (GlobalTheory.LieMet.isComb_iff u c 0).2 hc.symm
    have hb : IsCombAtG t x e 0 (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (0 : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G)).left :=
      (GlobalTheory.LieMet.isComb_iff u 0 0).2 (by simp)
    have := (hU _ (GlobalTheory.LieMet.isTan_tv 0)).unique ha hb
    intro i
    exact congrFun this i
  have hsp : ⊤ ≤ Submodule.span R (Set.range u) := by
    intro W _
    obtain ⟨a, ha, -⟩ := hU _ (GlobalTheory.LieMet.isTan_tv W)
    rw [(GlobalTheory.LieMet.isComb_iff u a W).1 ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let B := Module.Basis.mk hli hsp
  have hB : ∀ j, B j = u j := fun j => Module.Basis.mk_apply hli hsp j
  let ρ : 𝓞 E →+* Matrix (Fin g) (Fin g) R :=
    (LinearMap.toMatrixAlgEquiv B).toRingHom.comp (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act)
  have hcol : ∀ a i, IsCombAtG t x e (fun j => ρ a j i) (e i ≫ (t.act.act a).left) := by
    intro a i
    have hρ : (fun j => ρ a j i) = fun j => B.repr (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (u i)) j := by
      funext j
      show LinearMap.toMatrixAlgEquiv B (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a) j i = _
      rw [LinearMap.toMatrixAlgEquiv_apply, hB]
    rw [hρ]
    refine (GlobalTheory.LieMet.isComb_iff u (fun j => B.repr (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (u i)) j)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (u i))).2 ?_
    conv_lhs => rw [← B.sum_repr (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR t.act a (u i))]
    simp only [hB]
  refine ⟨ρ, ?_⟩
  intro K _ ψ a cf w hw
  have hT : ∀ j, IsTanAtG t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ e j) :=
    fun j => GlobalTheory.LieMet.isTan_map ψ rfl (he.1 j)
  have hw' : IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ e j ≫ (t.act.act a).left) cf
      (w ≫ (t.act.act a).left) := by
    have := t.act.hom a
    have hw0 := (isCombAtG_iff t _ (fun j => ovT (hT j)) cf w).1 hw
    have h := (isCombAtG_iff t _ (fun j => ovT (hT j) ≫ t.act.act a) cf (w ≫ (t.act.act a).left)).2 (by
      rw [← combT_post, Over.comp_left, hw0])
    exact h
  refine tanLinG _ hT _ _ cf _ (fun i => ?_) hw'
  have h := GlobalTheory.LatDRFree.comb_map t ψ (hcol a i)
  exact h

end GlobalTheory.TanActMat
