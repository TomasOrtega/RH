import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePreimmersionIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforward
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericFibreDegree

/- English proof (translation)
Introduce `B Y _ _ f G j s hpb hP hd hne`. Take `⟨hpre, -, -, hint⟩` from `GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s hpb`. Take `⟨hGint, hjη⟩` from `hint hne`. Establish `hu (w : G) : w = genericPoint G`. Establish `h0 : Order.krullDim (IrreducibleCloseds G) ≤ 0` using `(by simpa using hd : topologicalKrullDim G ≤ 0)`.

Use `Order.krullDim_nonpos_iff_forall_isMax.1 h0 ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩` as an intermediate fact. Conclude with `IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this ⟨Set.univ, IrreducibleSpace.isIrreducible_univ G, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec G)`. Use `haveI : IsAffine G := by`. Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (X := G) (x := genericPoint G) (U := ⊤) trivial`. Establish `hUt : U = ⊤`.

Use extensionality with `w`. Conclude with `⟨fun _ => trivial, fun _ => by rw [hu w]; exact hxU⟩`. Substitute `hUt` using the available equality. Use `haveI : IsAffine (⊤ : G.Opens).toScheme := hU`. Conclude with `IsAffine.of_isIso G.topIso.inv`.

Use `haveI : IsProper s := CommonModel.isProper_of_isProjOver hP`. Use `haveI : IsFinite s := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩`. Establish `hsη : s (genericPoint G) = genericPoint (Sp B.functionField)` using `Subsingleton.elim _ _`. Establish `h1` using `GlobalTheory.ProjFin.finrank_app_eq_residueDegree s hsη (U := ⊤) (isAffineOpen_top _) trivial`. Establish `h2 : f.residueDegree (genericPoint Y) = s.residueDegree (genericPoint G)`.

Establish `e` using `congrArg (fun h => Scheme.Hom.residueDegree h (genericPoint G)) hpb.w`. Simplify using `only [CurveDegreesCompare.residueDegree_comp] at e`. Rewrite `e` using `[CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks j, CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks (B.fromSpecStalk (genericPoint B)), mul_one, one_mul, hjη]`. Conclude with `e`. Use `letI := algebraΓOfHom s`.

Establish `h3 : Module.finrank B.functionField Γ(G, ⊤) = s.residueDegree (genericPoint G)`. Use `Eq.trans ?_ h1` and prove the remaining obligations. Use `letI := (s.app ⊤).hom.toAlgebra`. Conclude with `Algebra.finrank_eq_of_equiv_equiv (Scheme.ΓSpecIso (CommRingCat.of B.functionField)).symm.commRingCatIsoToRingEquiv (RingEquiv.refl _) rfl`. Use `haveI hfin : Module.Finite B.functionField Γ(G, ⊤) := by`.

Establish `hf : (s.app ⊤).hom.Finite` using `IsFinite.finite_app s ⊤ (isAffineOpen_top _)`. Establish `hi : ((Scheme.ΓSpecIso (CommRingCat.of B.functionField)).inv).hom.Finite` using `RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B.functionField)).inv).2`. Conclude with `hf.comp hi`. Use `haveI : Nontrivial Γ(G, ⊤) := inferInstance`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[h2, ← h3]`. Conclude with `Module.finrank_pos.ne'`. Rewrite using `[chi_structureModule_of_isAffine, h3, h2]`.
-/
theorem chi_eq_residueDegree : ∀ (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (f : Y ⟶ B)
    (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField),
    IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsProjOver s →
    topologicalKrullDim G ≤ (0 : ℕ) → Nonempty G → f.residueDegree (genericPoint Y) ≠ 0 ∧
      (letI := algebraΓOfHom s; chi B.functionField (structureModule G)) =
        f.residueDegree (genericPoint Y) := by
  intro B Y _ _ f G j s hpb hP hd hne
  obtain ⟨hpre, -, -, hint⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s hpb
  obtain ⟨hGint, hjη⟩ := hint hne

  have hu (w : G) : w = genericPoint G := by
    have h0 : Order.krullDim (IrreducibleCloseds G) ≤ 0 := (by simpa using hd : topologicalKrullDim G ≤ 0)
    have := Order.krullDim_nonpos_iff_forall_isMax.1 h0
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ G, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec G)

  haveI : IsAffine G := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := G) (x := genericPoint G)
      (U := ⊤) trivial
    have hUt : U = ⊤ := by
      ext w
      exact ⟨fun _ => trivial, fun _ => by rw [hu w]; exact hxU⟩
    subst hUt
    haveI : IsAffine (⊤ : G.Opens).toScheme := hU
    exact IsAffine.of_isIso G.topIso.inv
  haveI : IsProper s := CommonModel.isProper_of_isProjOver hP
  haveI : IsFinite s := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hsη : s (genericPoint G) = genericPoint (Sp B.functionField) := Subsingleton.elim _ _
  have h1 := GlobalTheory.ProjFin.finrank_app_eq_residueDegree s hsη (U := ⊤) (isAffineOpen_top _) trivial

  have h2 : f.residueDegree (genericPoint Y) = s.residueDegree (genericPoint G) := by
    have e := congrArg (fun h => Scheme.Hom.residueDegree h (genericPoint G)) hpb.w
    simp only [CurveDegreesCompare.residueDegree_comp] at e
    rw [CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks j,
      CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks (B.fromSpecStalk (genericPoint B)),
      mul_one, one_mul, hjη] at e
    exact e
  letI := algebraΓOfHom s

  have h3 : Module.finrank B.functionField Γ(G, ⊤) = s.residueDegree (genericPoint G) := by
    refine Eq.trans ?_ h1
    letI := (s.app ⊤).hom.toAlgebra
    exact Algebra.finrank_eq_of_equiv_equiv
      (Scheme.ΓSpecIso (CommRingCat.of B.functionField)).symm.commRingCatIsoToRingEquiv
      (RingEquiv.refl _) rfl
  haveI hfin : Module.Finite B.functionField Γ(G, ⊤) := by
    have hf : (s.app ⊤).hom.Finite := IsFinite.finite_app s ⊤ (isAffineOpen_top _)
    have hi : ((Scheme.ΓSpecIso (CommRingCat.of B.functionField)).inv).hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B.functionField)).inv).2
    exact hf.comp hi
  haveI : Nontrivial Γ(G, ⊤) := inferInstance
  refine ⟨?_, ?_⟩
  · rw [h2, ← h3]
    exact Module.finrank_pos.ne'
  · rw [chi_structureModule_of_isAffine, h3, h2]

end GlobalTheory.GenericFibreDegree
