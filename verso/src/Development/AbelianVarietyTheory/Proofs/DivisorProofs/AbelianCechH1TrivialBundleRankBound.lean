import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyTrivialBundleAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.AbCoh.FDimField

/- English proof (translation)
Introduce `K _ A _ g hA hsm κ _ _ D hD hcov`. Set `L` to `AlgebraicClosure K`. Set `f : Sp L ⟶ Sp K` to `spMap (algebraMap K L)`. Set `A' : Over (Sp L)` to `(Over.pullback f).obj A`. Set `π : A'.left ⟶ A.left` to `pullback.fst A.hom f`.

Establish `hGP : IsGrpPullback A' A (spMap (algebraMap K L)) π` using `isGrpPullback_pullback A f`. Establish `H : IsPullback π A'.hom A.hom (Spec.map (CommRingCat.ofHom (algebraMap K L)))` using `hGP.1`. Take `⟨hA', hg'⟩` from `GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback (algebraMap K L) A A' π g hGP hA hsm`. Use `haveI := hA.proper`. Use `haveI := GlobalTheory.isAffineHom_diagonal_of_isSeparated A.hom`.

Establish `hDs` using `GlobalTheory.isAffineOpen_finset_biInf hD`. Set `D' : κ → A'.left.Opens` to `fun i => π ⁻¹ᵁ D i`. Establish `hD' : ∀ i, IsAffineOpen (D' i)` using `fun i => GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback H (hD i)`. Establish `hcov' : ⨆ i, D' i = ⊤` using `by show ⨆ i, π ⁻¹ᵁ D i = ⊤`. Rewrite using `[← Scheme.Hom.preimage_iSup, hcov]`.

Both sides reduce to the same expression. Take `⟨hfin', hrank', -⟩` from `GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two L A' g hA' hg' κ D' hD' hcov'`. Take `⟨c, hc⟩` from `(GlobalTheory.CechPic.iso_triv_iff (LB.triv A.left)).1 ((GlobalTheory.CechPic.setoid A.left).iseqv.refl ⟨LB.triv A.left, LB.isLB_triv A.left⟩)`. Take `⟨w, hw⟩` from `(GlobalTheory.CechPic.iso_triv_iff ((LB.triv A.left).pull π)).2 ⟨LB.genPull (LB.triv A.left) c π, LB.isGen_genPull (LB.triv A.left) c hc π⟩`. Set `C` to `GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D`.

Take `⟨e₃⟩` from `GlobalTheory.FieldChangeInter.nonempty_homology_equiv L C 1`. Establish `e₄` using `((HomologicalComplex.homologyFunctor _ _ 1).mapIso (GlobalTheory.AbLaw.cechLBBaseChangeIso (LB.isLB_triv A.left) H (fun s hs => hDs s hs))).toLinearEquiv`. Establish `e₅` using `(HomologicalComplex.homologyMapIso (GlobalTheory.AbLaw.cechLBCongr A'.hom D' (LB.isLB_triv A'.left) (LB.isLB_pull (LB.isLB_triv A.left) π) w hw) 1).toLinearEquiv`. Set `E : (L ⊗[K] C.homology 1) ≃ₗ[L] (GlobalTheory.AbLaw.cechLB A'.hom (LB.triv A'.left) D').homology 1` to `e₃.symm ≪≫ₗ e₄ ≪≫ₗ e₅.symm`. Use `haveI := hfin' 1`.

Use `haveI : Module.Finite L (L ⊗[K] C.homology 1) := Module.Finite.equiv E.symm`. Establish `hfinK : Module.Finite K (C.homology 1)`. Establish `h1 : Module.rank L (L ⊗[K] C.homology 1) < Cardinal.aleph0` using `Module.rank_lt_aleph0 L _`. Rewrite `h1` using `[Module.rank_baseChange, Cardinal.lift_id]`. Conclude with `Module.rank_lt_aleph0_iff.1 h1`.

Use `⟨hfinK, le_of_eq ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.finrank_baseChange (R := L), E.finrank_eq]`. Conclude with `hrank'`.
-/
theorem cechLB_triv_finite_finrank_one_le : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → Module.Finite K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ∧ Module.finrank K ((GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D).homology 1) ≤ g := by
  intro K _ A _ g hA hsm κ _ _ D hD hcov
  let L := AlgebraicClosure K
  let f : Sp L ⟶ Sp K := spMap (algebraMap K L)
  let A' : Over (Sp L) := (Over.pullback f).obj A
  let π : A'.left ⟶ A.left := pullback.fst A.hom f
  have hGP : IsGrpPullback A' A (spMap (algebraMap K L)) π := isGrpPullback_pullback A f
  have H : IsPullback π A'.hom A.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) := hGP.1
  obtain ⟨hA', hg'⟩ :=
    GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback (algebraMap K L) A A' π g hGP hA hsm
  haveI := hA.proper
  haveI := GlobalTheory.isAffineHom_diagonal_of_isSeparated A.hom
  have hDs := GlobalTheory.isAffineOpen_finset_biInf hD
  let D' : κ → A'.left.Opens := fun i => π ⁻¹ᵁ D i
  have hD' : ∀ i, IsAffineOpen (D' i) := fun i => GlobalTheory.AbLaw.isAffineOpen_preimage_of_isPullback H (hD i)
  have hcov' : ⨆ i, D' i = ⊤ := by
    show ⨆ i, π ⁻¹ᵁ D i = ⊤
    rw [← Scheme.Hom.preimage_iSup, hcov]; rfl
  obtain ⟨hfin', hrank', -⟩ :=
    GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two L A' g hA' hg' κ D' hD' hcov'

  obtain ⟨c, hc⟩ := (GlobalTheory.CechPic.iso_triv_iff (LB.triv A.left)).1 ((GlobalTheory.CechPic.setoid A.left).iseqv.refl ⟨LB.triv A.left, LB.isLB_triv A.left⟩)
  obtain ⟨w, hw⟩ := (GlobalTheory.CechPic.iso_triv_iff ((LB.triv A.left).pull π)).2
    ⟨LB.genPull (LB.triv A.left) c π, LB.isGen_genPull (LB.triv A.left) c hc π⟩
  let C := GlobalTheory.AbLaw.cechLB A.hom (LB.triv A.left) D
  obtain ⟨e₃⟩ := GlobalTheory.FieldChangeInter.nonempty_homology_equiv L C 1
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ 1).mapIso
    (GlobalTheory.AbLaw.cechLBBaseChangeIso (LB.isLB_triv A.left) H (fun s hs => hDs s hs))).toLinearEquiv
  have e₅ := (HomologicalComplex.homologyMapIso
    (GlobalTheory.AbLaw.cechLBCongr A'.hom D' (LB.isLB_triv A'.left) (LB.isLB_pull (LB.isLB_triv A.left) π) w hw) 1).toLinearEquiv
  let E : (L ⊗[K] C.homology 1) ≃ₗ[L] (GlobalTheory.AbLaw.cechLB A'.hom (LB.triv A'.left) D').homology 1 :=
    e₃.symm ≪≫ₗ e₄ ≪≫ₗ e₅.symm
  haveI := hfin' 1
  haveI : Module.Finite L (L ⊗[K] C.homology 1) := Module.Finite.equiv E.symm
  have hfinK : Module.Finite K (C.homology 1) := by
    have h1 : Module.rank L (L ⊗[K] C.homology 1) < Cardinal.aleph0 := Module.rank_lt_aleph0 L _
    rw [Module.rank_baseChange, Cardinal.lift_id] at h1
    exact Module.rank_lt_aleph0_iff.1 h1
  refine ⟨hfinK, le_of_eq ?_⟩
  rw [← Module.finrank_baseChange (R := L), E.finrank_eq]
  exact hrank'

end GlobalTheory.AbCoh.FDimField
