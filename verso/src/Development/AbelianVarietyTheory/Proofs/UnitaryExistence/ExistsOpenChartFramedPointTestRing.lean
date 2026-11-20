import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMapStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasisStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversalStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZeroStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionNowhereZeroOfPullbackTripleStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReducedFiniteTypeIffTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsChartEigenframe

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

/- English proof (translation)
Introduce `τ`. Establish `hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ`. Establish `e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ}` using `e.subtypeEquiv (fun _ => Iff.rfl)`. Establish `e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ)` using `Equiv.sigmaSubtype τ`. Rewrite using `[Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]`.

Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Use `hcard.trans ?_` and prove the remaining obligations. Unfold `Datum.mult`. Rewrite using `[if_pos h]`. Use `hcard.trans ?_` and prove the remaining obligations.

Unfold `Datum.mult`. Rewrite using `[if_neg h]`.
-/
theorem isTypeFn_of_enum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => (e j).1) := by
  intro τ
  have hcard : Nat.card {i // (e i).1 = τ} = Dw.mult τ := by
    have e2 : {i // (e i).1 = τ} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    have e3 : {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ} ≃ Fin (Dw.mult τ) := Equiv.sigmaSubtype τ
    rw [Nat.card_congr (e2.trans e3), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_pos h]
  · refine hcard.trans ?_
    unfold Datum.mult
    rw [if_neg h]

/- English proof (translation)
Introduce `hS E _ _ _ H Dw l Xo c z`. Set `e` to `(Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm`. Take `⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩` from `GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_of_enum Dw e) z`. Set `x : Sp R ⟶ Xo.X` to `jR ≫ pullback.fst _ _`. Establish `hb : TanBasis x (fun i => (v i).left ≫ m.cm.F)` using `((GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv`.

Set `u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)` to `fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F`. Establish `htan : ∀ τ i, IsTanAt x (u τ i)` using `fun τ i => hb.1 _`. Establish `heig : ∀ τ i, IsEigAt c τ (u τ i)`. Introduce `τ i a`. Establish `h` using `hev (e.symm ⟨τ, i⟩) a`.

Simplify using `only [Equiv.apply_symm_apply] at h`. Establish `h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left = spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left` using `h`. Use `show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F`. Rewrite using `[Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]`. Establish `hb' : TanBasis x (fun j => u (e j).1 (e j).2)`.

Establish `: (fun j => u (e j).1 (e j).2) = fun i => (v i).left ≫ m.cm.F`. Use function extensionality and compare the values at `j`. Use `show (v (e.symm (e j))).left ≫ m.cm.F = _`. Rewrite using `[Equiv.symm_apply_apply]`. Rewrite using `[this]`.

Conclude with `hb`. Establish `hbasis` using `(GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l Xo c R x u _ e htan heig).2 hb'`. Take `⟨s, hsn⟩` from `GlobalTheory.T.exists_fibreSection_nowhereZero_of_pullbackTriple E H Dw l Xo R x o.t m.toSABMap th hth`. Establish `hgen` using `GlobalTheory.T.fibreSectionGenerates_of_nowhereZero hS E H Dw l Xo R x s hsn`. Establish `hx : x ≫ Xo.s = sOf c R`.

Establish `h1 : x ≫ Xo.s = (jR ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom`. Rewrite using `[Category.assoc, Category.assoc]`. Conclude with `congrArg (jR ≫ ·) pullback.condition`. Rewrite using `[h1, hs, sOf]`. Conclude with `(Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm`.

Set `y : FrPt Xo c R` to `⟨x, hx, u, htan, heig, hbasis, s, hgen⟩`. Take `⟨p, ⟨f⟩⟩` from `(GlobalTheory.reduced_finiteType_iff_testRing c.F).1 R hft hred`. Take `⟨y₀, hy₀⟩` from `GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c R p.R f.symm.toAlgHom y`. Establish `hiso : IsIso (spMap f.symm.toAlgHom.toRingHom)` using `inferInstanceAs (IsIso (Spec.map f.symm.toRingEquiv.toCommRingCatIso.hom))`. Use `⟨p, spMap f.symm.toAlgHom.toRingHom ≫ jR, y₀, ⟨inferInstance, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hy₀.1, Category.assoc]`. Rewrite using `[Category.assoc, hs]`. Use `(Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm.trans (congrArg Spec.map ?_)` and prove the remaining obligations. Use extensionality with `a`. Conclude with `f.symm.commutes a`.

Take `⟨q', hq'⟩` from `(spMap f.symm.toAlgHom.toRingHom).surjective q`. Conclude with `⟨q', by rw [Scheme.Hom.comp_apply, hq', hq]⟩`.
-/
theorem exists_openChart_testRing : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (z : Xo.XF c), ∃ (p : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R), OpenChart j y₀ ∧ z ∈ Set.range j := by
  intro hS E _ _ _ H Dw l Xo c z
  classical
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (Dw.mult τ))).symm
  obtain ⟨R, _, _, jR, o, v, th, hft, hred, hjR, ⟨q, hq⟩, hs, ⟨m⟩, hv, hev, hth, -⟩ :=
    GlobalTheory.ModuliChart.exists_chart_eigenframe hS E H Dw l Xo c _ _ (isTypeFn_of_enum Dw e) z
  let x : Sp R ⟶ Xo.X := jR ≫ pullback.fst _ _
  have hb : TanBasis x (fun i => (v i).left ≫ m.cm.F) :=
    ((GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal E H Dw l Xo R x o.t.G m.cm.F m.cart).2 _ v).1 hv
  let u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left) :=
    fun τ i => (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
  have htan : ∀ τ i, IsTanAt x (u τ i) := fun τ i => hb.1 _
  have heig : ∀ τ i, IsEigAt c τ (u τ i) := by
    intro τ i a
    have h := hev (e.symm ⟨τ, i⟩) a
    simp only [Equiv.apply_symm_apply] at h
    have h' : (v (e.symm ⟨τ, i⟩)).left ≫ (o.t.act.act a).left =
      spMap (epsMul (algebraMap c.F R (embK c τ a))) ≫ (v (e.symm ⟨τ, i⟩)).left := h
    show ((v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F) ≫ _ = _ ≫ (v (e.symm ⟨τ, i⟩)).left ≫ m.cm.F
    rw [Category.assoc, ← m.act a, ← Category.assoc, h', Category.assoc]
  have hb' : TanBasis x (fun j => u (e j).1 (e j).2) := by
    have : (fun j => u (e j).1 (e j).2) = fun i => (v i).left ≫ m.cm.F := by
      funext j
      show (v (e.symm (e j))).left ≫ m.cm.F = _
      rw [Equiv.symm_apply_apply]
    rw [this]; exact hb
  have hbasis := (GlobalTheory.T.eigenBasis_iff_tangentBasis E H Dw l Xo c R x u _ e htan heig).2 hb'
  obtain ⟨s, hsn⟩ := GlobalTheory.T.exists_fibreSection_nowhereZero_of_pullbackTriple E H Dw l Xo R x o.t m.toSABMap th hth
  have hgen := GlobalTheory.T.fibreSectionGenerates_of_nowhereZero hS E H Dw l Xo R x s hsn
  have hx : x ≫ Xo.s = sOf c R := by
    have h1 : x ≫ Xo.s = (jR ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (jR ≫ ·) pullback.condition
    rw [h1, hs, sOf]
    exact (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm
  let y : FrPt Xo c R := ⟨x, hx, u, htan, heig, hbasis, s, hgen⟩
  obtain ⟨p, ⟨f⟩⟩ := (GlobalTheory.reduced_finiteType_iff_testRing c.F).1 R hft hred
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c R p.R f.symm.toAlgHom y
  have hiso : IsIso (spMap f.symm.toAlgHom.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map f.symm.toRingEquiv.toCommRingCatIso.hom))
  refine ⟨p, spMap f.symm.toAlgHom.toRingHom ≫ jR, y₀, ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · rw [hy₀.1, Category.assoc]
  · rw [Category.assoc, hs]
    refine (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)).symm.trans (congrArg Spec.map ?_)
    ext a
    exact f.symm.commutes a
  · obtain ⟨q', hq'⟩ := (spMap f.symm.toAlgHom.toRingHom).surjective q
    exact ⟨q', by rw [Scheme.Hom.comp_apply, hq', hq]⟩

end GlobalTheory.Frames
