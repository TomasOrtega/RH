import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.AbelianSchemeSpreadsOverLocalization
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimSmoothSurjectiveTotal
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularCurve

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hodge

/- English proof (translation)
Rewrite using `[GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk]`. Conclude with `iSup_le fun x ↦ GroundTheory.Arith.SchemeCoh.ringKrullDim_stalk_le_of_smoothOfRelativeDimension g f x`.
-/
theorem topologicalKrullDim_le_of_smooth {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Sp k) (g : ℕ)
    (hf : SmoothOfRelativeDimension g f) : topologicalKrullDim X ≤ g := by
  rw [GlobalTheory.SmoothDimTotal.topologicalKrullDim_eq_iSup_stalk]
  exact iSup_le fun x ↦ GroundTheory.Arith.SchemeCoh.ringKrullDim_stalk_le_of_smoothOfRelativeDimension g f x

/- English proof (translation)
Use `GlobalTheory.subsingleton_coh_of_isProjOver (PositivityTheory.Xgn.AbelianSchemeSpreading.isProjOver_abelian k A hA) _ ?_` and prove the remaining obligations. Use `lt_of_le_of_lt ((topologicalKrullDim_subspace_le _ _).trans (topologicalKrullDim_le_of_smooth A.hom g hg)) ?_` and prove the remaining obligations. Conclude with `hn` after adjusting the coercions.
-/
theorem subsingleton_coh_abelian (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (g n : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (hn : g < n) :
    Subsingleton (GlobalTheory.coh (GlobalTheory.structureModule A.left) n) := by
  refine GlobalTheory.subsingleton_coh_of_isProjOver (PositivityTheory.Xgn.AbelianSchemeSpreading.isProjOver_abelian k A hA) _ ?_
  refine lt_of_le_of_lt ((topologicalKrullDim_subspace_le _ _).trans
    (topologicalKrullDim_le_of_smooth A.hom g hg)) ?_
  exact_mod_cast hn

/- English proof (translation)
Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hm : (⟨x, hx⟩ : LinearMap.ker (dn F (n + 1))) ∈ (LinearMap.range (dn F n)).comap (LinearMap.ker (dn F (n + 1))).subtype` using `(Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)`. Conclude with `hm`.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `LinearMap.congr_fun hdd y`.
-/
theorem exact_of_subsingleton_Hs {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (n : ℕ) (hdd : dn F (n + 1) ∘ₗ dn F n = 0) (h : Subsingleton (Hs F n)) :
    Function.Exact (dn F n) (dn F (n + 1)) := by
  intro x
  constructor
  · intro hx
    have hm : (⟨x, hx⟩ : LinearMap.ker (dn F (n + 1))) ∈
        (LinearMap.range (dn F n)).comap (LinearMap.ker (dn F (n + 1))).subtype :=
      (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
    exact hm
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hdd y

/- English proof (translation)
Introduce `R _ A _ g hA hg hR P _ _ S n hn`. Use `letI := hR.toField`. Establish `hsep : IsSeparated A.hom`. Use `hA.proper` as an intermediate fact. Use `infer_instance`.

Take `⟨e⟩` from `(hCmp R A.left A.hom hsep P S).2 n`. Establish `hs : Subsingleton (GlobalTheory.coh (GlobalTheory.structureModule A.left) (n + 1))` using `subsingleton_coh_abelian R A g (n + 1) hA hg (Nat.lt_succ_of_le hn)`. Conclude with `exact_of_subsingleton_Hs _ n ((hCx R _ (OSys A.hom S)).1 n) e.toEquiv.subsingleton`.
-/
theorem vanSt (hCx : CxSt) (hCmp : CmpSt) : VanSt := by
  intro R _ A _ g hA hg hR P _ _ S n hn
  letI := hR.toField
  have hsep : IsSeparated A.hom := by
    have := hA.proper
    infer_instance
  obtain ⟨e⟩ := (hCmp R A.left A.hom hsep P S).2 n
  have hs : Subsingleton (GlobalTheory.coh (GlobalTheory.structureModule A.left) (n + 1)) :=
    subsingleton_coh_abelian R A g (n + 1) hA hg (Nat.lt_succ_of_le hn)
  exact exact_of_subsingleton_Hs _ n ((hCx R _ (OSys A.hom S)).1 n) e.toEquiv.subsingleton

end GlobalTheory.CompanionTheory.Hodge
