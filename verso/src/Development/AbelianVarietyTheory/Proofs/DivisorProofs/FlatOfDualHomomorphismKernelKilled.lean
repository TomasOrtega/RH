import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDual
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueHomExtensionSemiAbelianNormal

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualHomFlat

/- English proof (translation)
Use `letI : GrpObj ((Over.pullback s).obj A) := Functor.grpObjObj`. Use `letI : GrpObj ((Over.pullback s).obj B) := Functor.grpObjObj`. Establish `hA'` using `GlobalTheory.isAbelianScheme_pullback_obj s A hA`. Establish `hB'` using `GlobalTheory.isAbelianScheme_pullback_obj s B hB`. Take `⟨gA, hgA⟩` from `GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj A) hA'`.

Take `⟨gB, hgB⟩` from `GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj B) hB'`. Set `Ak : AV.AbVar K` to `{ X := (Over.pullback s).obj A, ab := hA', dim := gA, smooth := hgA }`. Set `Bk : AV.AbVar K` to `{ X := (Over.pullback s).obj B, ab := hB', dim := gB, smooth := hgB }`. Establish `key : ∀ {X Y : Over S} (a : X ⟶ Y), ((Over.pullback s).map a).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ a.left` using `fun a ↦ pullback.lift_fst _ _ _`. Set `h : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj B).left ⟶ (A ⊗ B).left` to `(Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s`.

Establish `h₁ : h ≫ (fst A B).left = (fst ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫ pullback.fst A.hom s`. Simplify using `only [h, Category.assoc]`. Rewrite using `[← key, ← Category.assoc, ← Over.comp_left]`. Rewrite using `[show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (fst A B) = fst _ _ by simp]`. Establish `h₂ : h ≫ (snd A B).left = (snd ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫ pullback.fst B.hom s`.

Simplify using `only [h, Category.assoc]`. Rewrite using `[← key, ← Category.assoc, ← Over.comp_left]`. Rewrite using `[show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (snd A B) = snd _ _ by simp]`. Establish `hP' : (P.pull h).IsLB` using `pull_isLB hd.isLB _`. Establish `hd' : IsDual Ak.X Bk.X (P.pull h)` using `IsDual.baseChange (isGrpPullback_pullback A s) (isGrpPullback_pullback B s) h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd`.

Establish `hdim : gB = gA` using `DualTower.dim_eq_of_isDual Ak Bk (P.pull h) hd'`. Substitute `hdim` using the available equality. Establish `: LocallyQuasiFinite ((Over.pullback s).map la).left` using `MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange s la) inferInstance`. Conclude with `(IsogenyQuasiInverse.flat_surjective_of_field _ _ gB hA' hB' hgA hgB _).1`.
-/
theorem geomFibre_flat (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left)
    (la : A ⟶ B) [IsMonHom la] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hd : IsDual A B P)
    [LocallyQuasiFinite la.left] (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) :
    Flat ((Over.pullback s).map la).left := by
  letI : GrpObj ((Over.pullback s).obj A) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback s).obj B) := Functor.grpObjObj
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  obtain ⟨gA, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj A) hA'
  obtain ⟨gB, hgB⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj B) hB'
  let Ak : AV.AbVar K := { X := (Over.pullback s).obj A, ab := hA', dim := gA, smooth := hgA }
  let Bk : AV.AbVar K := { X := (Over.pullback s).obj B, ab := hB', dim := gB, smooth := hgB }
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback s).map a).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst A.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst B.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (snd A B) = snd _ _ by simp]
  have hP' : (P.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual Ak.X Bk.X (P.pull h) := IsDual.baseChange (isGrpPullback_pullback A s)
    (isGrpPullback_pullback B s) h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have hdim : gB = gA := DualTower.dim_eq_of_isDual Ak Bk (P.pull h) hd'
  subst hdim
  have : LocallyQuasiFinite ((Over.pullback s).map la).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange s la)
      inferInstance
  exact (IsogenyQuasiInverse.flat_surjective_of_field _ _ gB hA' hB' hgA hgB _).1

end GlobalTheory.DualHomFlat

namespace GlobalTheory.DualHomFlat

/- English proof (translation)
Introduce `S A B _ _ Q la d hA hB hd _ hla hdpos hker`. Use `hA.smooth` as an intermediate fact. Use `hB.smooth` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `hB.proper` as an intermediate fact.

Establish `: LocallyOfFiniteType (la.left ≫ B.hom)` using `by rw [Over.w]; infer_instance`. Establish `: LocallyOfFiniteType la.left` using `locallyOfFiniteType_of_comp _ B.hom`. Establish `: QuasiCompact (la.left ≫ B.hom)` using `by rw [Over.w]; infer_instance`. Establish `: QuasiCompact la.left` using `QuasiCompact.of_comp _ B.hom`. Establish `hSA` using `isSemiAbelian_of_isAbelianScheme A hA`.

Establish `: LocallyQuasiFinite la.left` using `locallyQuasiFinite_of_finite_geometric_ker _ A B la hla inferInstance inferInstance fun Ω _ _ t => by`. Use `HomExt.finite_torsion_points hSA t hdpos` as an intermediate fact. Conclude with `Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ d = 1}) (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e => Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ d = 1} => z.1) e)`. Establish `h1 : IsProper (la.left ≫ B.hom)` using `by rw [Over.w]; infer_instance`. Establish `: IsProper la.left` using `IsProper.of_comp _ B.hom`.

Establish `hf : IsFinite la.left` using `.of_isProper_of_locallyQuasiFinite _`. Conclude with `flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S A B la inferInstance inferInstance inferInstance hf fun K _ _ t => geomFibre_flat S A B Q la hA hB hd K t`.
-/
theorem main : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left)
    (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q →
    IsDual B A (swap Q) → IsMonHom la → 0 < d →
    (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Flat la.left := by
  intro S A B _ _ Q la d hA hB hd _ hla hdpos hker
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have : LocallyOfFiniteType (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType la.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact la.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite la.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B la hla inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hdpos
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ d = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ d = 1} => z.1) e)
  have h1 : IsProper (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper la.left := IsProper.of_comp _ B.hom
  have hf : IsFinite la.left := .of_isProper_of_locallyQuasiFinite _
  exact flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S A B la inferInstance
    inferInstance inferInstance hf fun K _ _ t => geomFibre_flat S A B Q la hA hB hd K t

end GlobalTheory.DualHomFlat
