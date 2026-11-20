import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteMulByNatAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsBasisMemOfSpanEqTopOfSemilocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsQuotientSchemeOfFiniteFlatSubgroup
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbelianQuotientField

open AffineQuotient AbelianQuotient

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `K _ _ A _ hA H _ i hi hmono hfin`. Use `hA.comm` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `hA.smooth` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact.

Establish `hflat : Flat H.hom` using `inferInstance`. Establish `: IsCommMonObj H` using `⟨by`. Rewrite using `[← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]⟩`. Take `⟨N, hN, hH⟩` from `GlobalTheory.FiniteFlatKilled.main K H hfin hflat`. Establish `: IsLocallyNoetherian A.left` using `LocallyOfFiniteType.isLocallyNoetherian A.hom`.

Establish `: IsFinite (𝟙 A ^ N : A ⟶ A).left` using `GlobalTheory.T.isFinite_mulByNat_abelianVariety K A hA N hN`. Establish `: IsFinite H.hom` using `hfin`. Take `⟨Λ, _, _, _, _, e, _⟩` from `exists_hopfAlgebra K H`. Establish `hi' : i ^ N = 1`. Rewrite using `[← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]`.

Take `⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩` from `exists_quotient_hopf (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal) (e.hom ≫ i) (𝟙 A ^ N) (by`. Rewrite using `[comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow, ← comp_pow i, hi', comp_one, comp_one, _root_.one_mul])`. Establish `hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q`. Apply the tactic sequence `refine h₅.of_iso (whiskerRightIso e A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [comp_mul]`. Establish `: Flat q.left` using `h₃`.

Establish `: Surjective q.left` using `h₄`. Establish `: IsFinite q.left` using `h₂`. Establish `: IsFinite π.left` using `h₁`. Take `⟨inst, hcomm, hhom, hker⟩` from `exists_grpObj i q hq`. Use `⟨Q, inst, ?_, q, hhom, h₂, h₃, h₄, hker⟩` and prove the remaining obligations.

Establish `hπ : π.left ≫ A.hom = Q.hom` using `Over.w π`. Establish `: IsSeparated Q.hom` using `by rw [← hπ]; infer_instance`. Establish `: LocallyOfFiniteType Q.hom` using `by rw [← hπ]; infer_instance`. Establish `hw : q.left ≫ Q.hom = A.hom` using `Over.w q`. Use `GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected` as an intermediate fact.

Establish `: Flat (q.left ≫ Q.hom)` using `by rw [hw]; infer_instance`. Establish `: UniversallyClosed (q.left ≫ Q.hom)` using `by rw [hw]; infer_instance`. Establish `: GeometricallyReduced (q.left ≫ Q.hom)` using `by rw [hw]; infer_instance`. Establish `: GeometricallyConnected (q.left ≫ Q.hom)` using `by rw [hw]; infer_instance`. Use `flat_of_comp_of_flat_of_surjective q.left Q.hom` as an intermediate fact.

Use `UniversallyClosed.of_comp_surjective q.left Q.hom` as an intermediate fact. Use `geometricallyReduced_of_comp q.left Q.hom` as an intermediate fact. Establish `: LocallyOfFinitePresentation Q.hom` using `inferInstance`. Conclude with `⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩`.
-/
theorem exists_quotient : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A), IsMonHom i → Mono i → IsFinite H.hom → ∃ (A' : Over (Sp K)) (_ : GrpObj A'), IsAbelianScheme A' ∧ ∃ q : A ⟶ A', IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsPullback i (toUnit H) q η[A'] := by
  intro K _ _ A _ hA H _ i hi hmono hfin
  have := hA.comm
  have := hA.proper
  have := hA.smooth
  have := hA.geomConnected
  have hflat : Flat H.hom := inferInstance
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := GlobalTheory.FiniteFlatKilled.main K H hfin hflat
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsFinite (𝟙 A ^ N : A ⟶ A).left := GlobalTheory.T.isFinite_mulByNat_abelianVariety K A hA N hN
  have : IsFinite H.hom := hfin
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra K H
  have hi' : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf
    (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal)
    (e.hom ≫ i) (𝟙 A ^ N) (by
      rw [comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
        ← comp_pow i, hi', comp_one, comp_one, _root_.one_mul])
  have hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
    refine h₅.of_iso (whiskerRightIso e A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]
  have : Flat q.left := h₃
  have : Surjective q.left := h₄
  have : IsFinite q.left := h₂
  have : IsFinite π.left := h₁
  obtain ⟨inst, hcomm, hhom, hker⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, ?_, q, hhom, h₂, h₃, h₄, hker⟩
  have hπ : π.left ≫ A.hom = Q.hom := Over.w π
  have : IsSeparated Q.hom := by rw [← hπ]; infer_instance
  have : LocallyOfFiniteType Q.hom := by rw [← hπ]; infer_instance
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩

end GlobalTheory.AbelianQuotientField
