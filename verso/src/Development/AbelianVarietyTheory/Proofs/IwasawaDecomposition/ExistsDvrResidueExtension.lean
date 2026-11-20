import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
open IsLocalRing GlobalTheory.LN Polynomial IntermediateField

namespace GlobalTheory

/- English proof (translation)
Introduce `A _ _ L _ φ hφ hK W _ _ _ hW α hα`. Take `⟨hd, hc, h0⟩` from `(cDvr_iff W).1 hW`. Set `K` to `ResidueField A`. Use `letI : Algebra K L := φ.toAlgebra`. Use `haveI : FiniteDimensional K L := hφ`.

Take `⟨θ, hθ⟩` from `Field.exists_primitive_element K L`. Establish `hθi : IsIntegral K θ` using `.of_finite K θ`. Set `β : K →+* ResidueField W` to `ResidueField.map α`. Take `⟨q, hq1, hq2, hq3⟩` from `Polynomial.lifts_and_degree_eq_and_monic (Polynomial.map_surjective (residue W) residue_surjective ((minpoly K θ).map β)) ((minpoly.monic hθi).map β)`. Set `F` to `FractionRing W`.

Use `haveI : CharZero F := IsFractionRing.charZero_of_isFractionRing W`. Set `M` to `(q.map (algebraMap W F)).SplittingField`. Use `haveI : FaithfulSMul W M := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful W F M`. Use `haveI : Module.Finite W (integralClosure W M) := IsIntegralClosure.finite W F M (integralClosure W M)`. Use `haveI hVd : IsDiscreteValuationRing (integralClosure W M) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr W F M`.

Use `haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap F M).injective`. Establish `hdeg : ((q.map (algebraMap W F)).map (algebraMap F M)).degree ≠ 0`. Rewrite using `[degree_map_eq_of_injective (algebraMap F M).injective, degree_map_eq_of_injective (IsFractionRing.injective W F), hq2, degree_map, degree_eq_natDegree (minpoly.ne_zero hθi)]`. Conclude with `(minpoly.natDegree_pos hθi).ne'` after adjusting the coercions. Take `⟨x, hx⟩` from `Splits.exists_eval_eq_zero (SplittingField.splits _) hdeg`.

Establish `hxq : aeval x q = 0`. Rewrite `hx` using `[Polynomial.map_map, eval_map, ← IsScalarTower.algebraMap_eq]`. Rewrite using `[aeval_def]`. Conclude with `hx`. Set `V` to `integralClosure W M`.

Set `y : V` to `⟨x, q, hq3, hxq⟩`. Establish `hyq : aeval y q = 0` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `(integralClosure W M).val (aeval y q) = 0`. Rewrite using `[← Polynomial.aeval_algHom_apply]`. Conclude with `hxq)`.

Set `f : W →+* V` to `algebraMap W V`. Use `haveI hfl : IsLocalHom f := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom W M`. Set `ψ : K →+* ResidueField V` to `(ResidueField.map f).comp β`. Establish `hψ : eval₂ ψ (residue V y) (minpoly K θ) = 0`. Establish `e1` using `congrArg (residue V) hyq`.

Rewrite `e1` using `[map_zero, aeval_def, hom_eval₂]`. Establish `e2 : (residue V).comp (algebraMap W V) = (ResidueField.map f).comp (residue W)`. Use extensionality with `w`. Simplify using `[f]`. Rewrite `e1` using `[e2, ← eval₂_map, hq1, eval₂_map]`.

Conclude with `e1`. Use `letI : Algebra K (ResidueField V) := ψ.toAlgebra`. Set `pb` to `IntermediateField.adjoin.powerBasis hθi`. Set `τ : K⟮θ⟯ →ₐ[K] ResidueField V` to `pb.lift (residue V y) (by`. Rewrite using `[IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, aeval_def]`.

Conclude with `hψ)`. Set `σ : L →ₐ[K] ResidueField V` to `τ.comp ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv).symm.toAlgHom`. Use `⟨V, inferInstance, inferInstance, inferInstance, f, (cDvr_iff V).2 ⟨hVd, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local W V, inferInstance⟩, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj W M, hfl, σ.toRingHom, fun a => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `σ (algebraMap K L (residue A a)) = _`. Rewrite using `[σ.commutes]`.

Express the relevant statement in the definitionally equal form `ResidueField.map f (ResidueField.map α (residue A a)) = _`. Simplify using `[ResidueField.map_residue]`.
-/
theorem exists_cDvr_residue_lift : ∀ {A : Type} [CommRing A] [IsLocalRing A] {L : Type} [Field L] (φ : ResidueField A →+* L), φ.Finite → CharZero (ResidueField A) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (α : A →+* W), IsLocalHom α → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ ∃ σ : L →+* ResidueField V, ∀ a : A, σ (φ (residue A a)) = residue V (f (α a)) := by
  intro A _ _ L _ φ hφ hK W _ _ _ hW α hα
  obtain ⟨hd, hc, h0⟩ := (cDvr_iff W).1 hW
  let K := ResidueField A
  letI : Algebra K L := φ.toAlgebra
  haveI : FiniteDimensional K L := hφ
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K L
  have hθi : IsIntegral K θ := .of_finite K θ
  let β : K →+* ResidueField W := ResidueField.map α
  obtain ⟨q, hq1, hq2, hq3⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.map_surjective (residue W) residue_surjective ((minpoly K θ).map β)) ((minpoly.monic hθi).map β)
  let F := FractionRing W
  haveI : CharZero F := IsFractionRing.charZero_of_isFractionRing W
  let M := (q.map (algebraMap W F)).SplittingField
  haveI : FaithfulSMul W M := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful W F M
  haveI : Module.Finite W (integralClosure W M) := IsIntegralClosure.finite W F M (integralClosure W M)
  haveI hVd : IsDiscreteValuationRing (integralClosure W M) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr W F M
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap F M).injective
  have hdeg : ((q.map (algebraMap W F)).map (algebraMap F M)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (algebraMap F M).injective,
      degree_map_eq_of_injective (IsFractionRing.injective W F), hq2, degree_map,
      degree_eq_natDegree (minpoly.ne_zero hθi)]
    exact_mod_cast (minpoly.natDegree_pos hθi).ne'
  obtain ⟨x, hx⟩ := Splits.exists_eval_eq_zero (SplittingField.splits _) hdeg
  have hxq : aeval x q = 0 := by
    rw [Polynomial.map_map, eval_map, ← IsScalarTower.algebraMap_eq] at hx
    rw [aeval_def]; exact hx
  let V := integralClosure W M
  let y : V := ⟨x, q, hq3, hxq⟩
  have hyq : aeval y q = 0 := Subtype.ext (by
    change (integralClosure W M).val (aeval y q) = 0
    rw [← Polynomial.aeval_algHom_apply]; exact hxq)
  let f : W →+* V := algebraMap W V
  haveI hfl : IsLocalHom f := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom W M
  let ψ : K →+* ResidueField V := (ResidueField.map f).comp β
  have hψ : eval₂ ψ (residue V y) (minpoly K θ) = 0 := by
    have e1 := congrArg (residue V) hyq
    rw [map_zero, aeval_def, hom_eval₂] at e1
    have e2 : (residue V).comp (algebraMap W V) = (ResidueField.map f).comp (residue W) := by
      ext w; simp [f]
    rw [e2, ← eval₂_map, hq1, eval₂_map] at e1
    exact e1
  letI : Algebra K (ResidueField V) := ψ.toAlgebra
  let pb := IntermediateField.adjoin.powerBasis hθi
  let τ : K⟮θ⟯ →ₐ[K] ResidueField V := pb.lift (residue V y) (by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, aeval_def]; exact hψ)
  let σ : L →ₐ[K] ResidueField V :=
    τ.comp ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv).symm.toAlgHom
  refine ⟨V, inferInstance, inferInstance, inferInstance, f,
    (cDvr_iff V).2 ⟨hVd, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local W V, inferInstance⟩,
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj W M, hfl, σ.toRingHom, fun a => ?_⟩
  change σ (algebraMap K L (residue A a)) = _
  rw [σ.commutes]
  change ResidueField.map f (ResidueField.map α (residue A a)) = _
  simp [ResidueField.map_residue]

end GlobalTheory
