import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubmatrixMulOfVanish
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosBlockMulKosD
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignInsert
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtension
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TorsSqMap
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KaFormHomogeneous
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantFromIntersectionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsL2ValFieldOrDvrSplitKernelStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CmpValBaseChangeSimilitudeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscriminantEqJacobianCompleteIntersectionDvrStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KaFiniteUnit

/- English proof (translation)
Use `letI := σ.toAlgebra`. Use `letI := τ.toAlgebra`. Take `⟨M, hM⟩` from `Ideal.exists_maximal (TensorProduct L F E)`. Conclude with `⟨TensorProduct L F E ⧸ M, Ideal.Quotient.field M, (Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeLeftRingHom, (Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeRight.toRingHom, RingHom.ext fun v => congrArg (Ideal.Quotient.mk M) (RingHom.congr_fun (Algebra.TensorPr …`.
-/
theorem exists_common_field {L F E : Type} [Field L] [Field F] [Field E] (σ : L →+* F) (τ : L →+* E) :
    ∃ (Ω : Type) (_ : Field Ω) (i : F →+* Ω) (g : E →+* Ω), g.comp τ = i.comp σ := by
  letI := σ.toAlgebra
  letI := τ.toAlgebra
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct L F E)
  exact ⟨TensorProduct L F E ⧸ M, Ideal.Quotient.field M,
    (Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk M).comp Algebra.TensorProduct.includeRight.toRingHom,
    RingHom.ext fun v => congrArg (Ideal.Quotient.mk M)
      (RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := L) (A := F) (B := E)) v).symm⟩

/- English proof (translation)
Use `letI := f.toAlgebra`. Use `haveI : FaithfulSMul O F := (faithfulSMul_iff_algebraMap_injective O F).2 hf`. Use `letI := FractionRing.liftAlgebra O F`. Set `L` to `IntermediateField.adjoin (FractionRing O) (S : Set F)`. Use `haveI : Algebra.EssFiniteType (FractionRing O) L := IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite S.finite_toSet)`.

Use `haveI : Algebra.EssFiniteType O (FractionRing O) := Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors O)`. Use `haveI : Algebra.EssFiniteType O L := Algebra.EssFiniteType.comp O (FractionRing O) L`. Use `haveI : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 fun a b h => hf (congrArg Subtype.val h)`. Take `⟨V, hV, hle⟩` from `exists_discreteValuationSubring_dominating_of_essFiniteType (R := O) (L := L) (IsDiscreteValuationRing.not_isField O)`. Take `⟨hm, hloc⟩` from `(localSubring_range_le_valuationSubring_iff_isLocalHom _ V).1 hle`.

Set `O'` to `AdicCompletion (IsLocalRing.maximalIdeal V) V`. Establish `hc : Function.Injective (algebraMap V O')` using `algebraMap_adicCompletion_injective_of_dvr V`. Establish `hc' : Function.Injective ((algebraMap O' (FractionRing O')).comp (algebraMap V O'))` using `(IsFractionRing.injective O' _).comp hc`. Set `τ : L →+* FractionRing O'` to `IsFractionRing.lift (A := V) hc'`. Take `⟨Ω, _, i, g, hg⟩` from `exists_common_field (algebraMap L F) τ`.

Use `⟨L, inferInstance, algebraMap L F, V, (algebraMap O L).codRestrict V hm, O', inferInstance, inferInstance, inferInstance, inferInstance, algebraMap V O', Ω, inferInstance, i, g.comp (algebraMap O' _), fun a ha => ?_, RingHom.ext fun _ => rfl, RingHom.isLocalHom_comp _ _, g.inject …` and prove the remaining obligations. Conclude with `⟨⟨a, IntermediateField.subset_adjoin _ _ ha⟩, rfl⟩`. Establish `e : algebraMap O' (FractionRing O') (algebraMap V O' v) = τ (algebraMap V L v)` using `(IsFractionRing.lift_algebraMap hc' v).symm`. Express the relevant statement in the definitionally equal form `g (algebraMap O' (FractionRing O') (algebraMap V O' v)) = i (algebraMap L F (algebraMap V L v))`. Rewrite using `[e]`.

Conclude with `RingHom.congr_fun hg _`.
-/
theorem exists_complete_extension {O F : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
    (f : O →+* F) (hf : Function.Injective f) (S : Finset F) :
    ∃ (L : Type) (_ : Field L) (σ : L →+* F) (V : ValuationSubring L) (j₀ : O →+* V) (O' : Type) (_ : CommRing O')
      (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O')
      (c : V →+* O') (Ω : Type) (_ : Field Ω) (i : F →+* Ω) (g : O' →+* Ω),
      (∀ a ∈ S, a ∈ Set.range σ) ∧ σ.comp ((algebraMap V L).comp j₀) = f ∧ IsLocalHom (c.comp j₀) ∧
      Function.Injective g ∧ g.comp c = i.comp (σ.comp (algebraMap V L)) := by
  letI := f.toAlgebra
  haveI : FaithfulSMul O F := (faithfulSMul_iff_algebraMap_injective O F).2 hf
  letI := FractionRing.liftAlgebra O F
  let L := IntermediateField.adjoin (FractionRing O) (S : Set F)
  haveI : Algebra.EssFiniteType (FractionRing O) L :=
    IntermediateField.essFiniteType_iff.mpr (IntermediateField.fg_adjoin_of_finite S.finite_toSet)
  haveI : Algebra.EssFiniteType O (FractionRing O) := Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors O)
  haveI : Algebra.EssFiniteType O L := Algebra.EssFiniteType.comp O (FractionRing O) L
  haveI : FaithfulSMul O L := (faithfulSMul_iff_algebraMap_injective O L).2 fun a b h => hf (congrArg Subtype.val h)
  obtain ⟨V, hV, hle⟩ := exists_discreteValuationSubring_dominating_of_essFiniteType (R := O) (L := L)
    (IsDiscreteValuationRing.not_isField O)
  obtain ⟨hm, hloc⟩ := (localSubring_range_le_valuationSubring_iff_isLocalHom _ V).1 hle
  let O' := AdicCompletion (IsLocalRing.maximalIdeal V) V
  have hc : Function.Injective (algebraMap V O') := algebraMap_adicCompletion_injective_of_dvr V
  have hc' : Function.Injective ((algebraMap O' (FractionRing O')).comp (algebraMap V O')) :=
    (IsFractionRing.injective O' _).comp hc
  let τ : L →+* FractionRing O' := IsFractionRing.lift (A := V) hc'
  obtain ⟨Ω, _, i, g, hg⟩ := exists_common_field (algebraMap L F) τ
  refine ⟨L, inferInstance, algebraMap L F, V, (algebraMap O L).codRestrict V hm, O', inferInstance, inferInstance,
    inferInstance, inferInstance, algebraMap V O', Ω, inferInstance, i, g.comp (algebraMap O' _), fun a ha => ?_,
    RingHom.ext fun _ => rfl, RingHom.isLocalHom_comp _ _, g.injective.comp (IsFractionRing.injective O' _),
    RingHom.ext fun v => ?_⟩
  · exact ⟨⟨a, IntermediateField.subset_adjoin _ _ ha⟩, rfl⟩
  · have e : algebraMap O' (FractionRing O') (algebraMap V O' v) = τ (algebraMap V L v) :=
      (IsFractionRing.lift_algebraMap hc' v).symm
    change g (algebraMap O' (FractionRing O') (algebraMap V O' v)) = i (algebraMap L F (algebraMap V L v))
    rw [e]
    exact RingHom.congr_fun hg _

/- English proof (translation)
Use `haveI := Fintype.ofFinite T`. Use `choose S hS using fun a => KaLift.exists_finset_descend π f (p a) (hp a)`. Take `⟨L, _, σ, V, j₀, O', _, _, _, _, c, Ω, _, i, g, h₁, h₂, h₃, h₄, h₅⟩` from `exists_complete_extension f hf (Finset.univ.biUnion S)`. Use `⟨O', _, ‹_›, ‹_›, ‹_›, c.comp j₀, Ω, _, i, g, h₃, h₄, ?_, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.comp_assoc, h₅, ← h₂]`.

Both sides reduce to the same expression. Take `⟨q₁, e₁, e₂⟩` from `hS a L σ _ h₂ fun b hb => h₁ b (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hb⟩)`. Take `⟨q₂, e₃, e₄⟩` from `exists_valuativeExtension (V := V) (K := L) π (spMap j₀) q₁ (e₂.trans (spMap_comp _ _))`. Establish `e₅ : spMap (algebraMap V L) ≫ q₂ = q₁` using `e₃`. Use `⟨spMap c ≫ q₂, by rw [Category.assoc, e₄, spMap_comp], ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.assoc, ← spMap_comp, h₅, spMap_comp, spMap_comp, Category.assoc, Category.assoc, e₅, e₁]`.
-/
theorem exists_points_extension {O F : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
    (f : O →+* F) (hf : Function.Injective f) {X : Scheme.{0}} (π : X ⟶ Sp O) [IsProper π] {T : Type} [Finite T]
    (p : T → (Sp F ⟶ X)) (hp : ∀ a, p a ≫ π = spMap f) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O') O') (j : O →+* O') (Ω : Type) (_ : Field Ω) (i : F →+* Ω)
      (g : O' →+* Ω), IsLocalHom j ∧ Function.Injective g ∧ g.comp j = i.comp f ∧
      ∀ a, ∃ q : Sp O' ⟶ X, q ≫ π = spMap j ∧ spMap g ≫ q = spMap i ≫ p a := by
  classical
  haveI := Fintype.ofFinite T
  choose S hS using fun a => KaLift.exists_finset_descend π f (p a) (hp a)
  obtain ⟨L, _, σ, V, j₀, O', _, _, _, _, c, Ω, _, i, g, h₁, h₂, h₃, h₄, h₅⟩ :=
    exists_complete_extension f hf (Finset.univ.biUnion S)
  refine ⟨O', _, ‹_›, ‹_›, ‹_›, c.comp j₀, Ω, _, i, g, h₃, h₄, ?_, fun a => ?_⟩
  · rw [← RingHom.comp_assoc, h₅, ← h₂]
    rfl
  · obtain ⟨q₁, e₁, e₂⟩ := hS a L σ _ h₂ fun b hb => h₁ b (Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hb⟩)
    obtain ⟨q₂, e₃, e₄⟩ := exists_valuativeExtension (V := V) (K := L) π (spMap j₀) q₁ (e₂.trans (spMap_comp _ _))
    have e₅ : spMap (algebraMap V L) ≫ q₂ = q₁ := e₃
    refine ⟨spMap c ≫ q₂, by rw [Category.assoc, e₄, spMap_comp], ?_⟩
    rw [← Category.assoc, ← spMap_comp, h₅, spMap_comp, spMap_comp, Category.assoc, Category.assoc, e₅, e₁]

/- English proof (translation)
Set `I` to `Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩`. Establish `hr : Set.range I.subschemeι = Z`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]`. Both sides reduce to the same expression. Use `haveI : Finite I.subscheme := by haveI := hfin.to_subtype`.

Conclude with `Finite.of_injective (fun y => (⟨I.subschemeι y, hr.le ⟨y, rfl⟩⟩ : Z)) fun a b e => I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val e)`. Use `haveI : LocallyQuasiFinite (I.subschemeι ≫ π) := .of_finite_preimage_singleton _ fun _ => Set.toFinite _`. Establish `hp` using `(IsPullback.of_hasPullback I.subschemeι φ).paste_vert h`. Use `haveI : LocallyQuasiFinite (pullback.snd I.subschemeι φ ≫ π') := MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) hp ‹_›`. Use `haveI : QuasiCompact (pullback.snd I.subschemeι φ ≫ π') := MorphismProperty.of_isPullback (P := @QuasiCompact) hp inferInstance`.

Use `(((pullback.snd I.subschemeι φ ≫ π').finite_preimage_singleton p).image (pullback.snd I.subschemeι φ)).subset fun y hy => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `hr.ge hy.2`. Take `⟨b, -, hb⟩` from `Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback I.subschemeι φ) a y ha`. Conclude with `⟨b, (congrArg π' hb).trans hy.1, hb⟩`.
-/
theorem finite_preimage_fibre {X X' S S' : Scheme.{0}} {φ : X' ⟶ X} {π' : X' ⟶ S'} {π : X ⟶ S} {t : S' ⟶ S}
    [LocallyOfFiniteType π] [QuasiCompact π] (h : IsPullback φ π' π t) {Z : Set X} (hZ : IsClosed Z) (hfin : Z.Finite)
    (p : S') : {y : X' | π' y = p ∧ φ y ∈ Z}.Finite := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨Z, hZ⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  haveI : Finite I.subscheme := by
    haveI := hfin.to_subtype
    exact Finite.of_injective (fun y => (⟨I.subschemeι y, hr.le ⟨y, rfl⟩⟩ : Z))
      fun a b e => I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val e)
  haveI : LocallyQuasiFinite (I.subschemeι ≫ π) := .of_finite_preimage_singleton _ fun _ => Set.toFinite _
  have hp := (IsPullback.of_hasPullback I.subschemeι φ).paste_vert h
  haveI : LocallyQuasiFinite (pullback.snd I.subschemeι φ ≫ π') :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) hp ‹_›
  haveI : QuasiCompact (pullback.snd I.subschemeι φ ≫ π') :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hp inferInstance
  refine (((pullback.snd I.subschemeι φ ≫ π').finite_preimage_singleton p).image
    (pullback.snd I.subschemeι φ)).subset fun y hy => ?_
  obtain ⟨a, ha⟩ := hr.ge hy.2
  obtain ⟨b, -, hb⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback I.subschemeι φ) a y ha
  exact ⟨b, (congrArg π' hb).trans hy.1, hb⟩

/- English proof (translation)
Establish `hd : al.det ≠ 0` using `fun h0 => by`. Use `congrArg Matrix.det h` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one]`. Conclude with `pow_ne_zero _ (by exact_mod_cast (by omega : m ≠ 0)) this.symm`. Establish `e : (al * al.transpose - (m : ℤ) • 1) * al = 0`.

Rewrite using `[Matrix.sub_mul, Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_self]`. Establish `e'` using `congrArg (· * al.adjugate) e`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.zero_mul, Matrix.mul_smul, Matrix.mul_one] at e'`. Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 e').resolve_left hd)`.
-/
theorem mul_transpose_of_transpose_mul {al : Matrix (Fin 4) (Fin 4) ℤ} {m : ℕ} (hm : 1 ≤ m)
    (h : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    al * al.transpose = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  have hd : al.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, _root_.mul_one] at this
    exact pow_ne_zero _ (by exact_mod_cast (by omega : m ≠ 0)) this.symm
  have e : (al * al.transpose - (m : ℤ) • 1) * al = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_self]
  have e' := congrArg (· * al.adjugate) e
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.zero_mul, Matrix.mul_smul, Matrix.mul_one] at e'
  exact sub_eq_zero.1 ((smul_eq_zero.1 e').resolve_left hd)

/- English proof (translation)
Establish `e : ∏ c, (∏ r', ξ r' ^ al r' c) ^ al r c = 1` using `by simp [hξ]`. Establish `e₂ : ∀ r', ∏ c, (ξ r' ^ al r' c) ^ al r c = ξ r' ^ (if r' = r then (m : ℤ) else 0)` using `fun r' => by`. Use `congrFun (congrFun (mul_transpose_of_transpose_mul hm h) r') r` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, _root_.mul_one, mul_zero] at this`. Rewrite using `[← this]`.

Simplify using `only [← zpow_mul, Fin.prod_univ_four, Fin.sum_univ_four, zpow_add]`. Simplify using `only [← Finset.prod_zpow] at e`. Rewrite `e` using `[Finset.prod_comm]`. Simplify using `only [e₂] at e`. Rewrite `e` using `[Finset.prod_eq_single r (fun b _ hb => by simp [hb]) (by simp)]`.

Simplify using `using e`.
-/
theorem pow_eq_one_of_ker {G : Type} [CommGroup G] {al : Matrix (Fin 4) (Fin 4) ℤ} {m : ℕ} (hm : 1 ≤ m)
    (h : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (ξ : Fin 4 → G)
    (hξ : ∀ c, ∏ r, ξ r ^ al r c = 1) (r : Fin 4) : ξ r ^ m = 1 := by
  have e : ∏ c, (∏ r', ξ r' ^ al r' c) ^ al r c = 1 := by simp [hξ]
  have e₂ : ∀ r', ∏ c, (ξ r' ^ al r' c) ^ al r c = ξ r' ^ (if r' = r then (m : ℤ) else 0) := fun r' => by
    have := congrFun (congrFun (mul_transpose_of_transpose_mul hm h) r') r
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
      _root_.mul_one, mul_zero] at this
    rw [← this]
    simp only [← zpow_mul, Fin.prod_univ_four, Fin.sum_univ_four, zpow_add]
  simp only [← Finset.prod_zpow] at e
  rw [Finset.prod_comm] at e
  simp only [e₂] at e
  rw [Finset.prod_eq_single r (fun b _ hb => by simp [hb]) (by simp)] at e
  simpa using e

/- English proof (translation)
Take `⟨he, hg, F, hp, hw, hr, hs, hF, hε, hv⟩` from `H`. Take `⟨he', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩` from `H'`. Establish `g` using `(isGen_iff w).1 hw`. Establish `g'` using `(isGen_iff w').1 hw'`. Take `⟨w'', T⟩` from `exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB`.

Establish `he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A`. Rewrite using `[← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]`. Use `⟨w'', ⟨he'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl, (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩, fun l s s' s'' h h' j k hle => fn_ext fun y hy => ?_⟩` and prove the remaining obligations. Establish `r₀` using `(maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr`. Establish `r₁` using `(maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'`.

Establish `r₂` using `T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁`. Rewrite `r₂` using `[← spMap_comp]`. Conclude with `(maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _ (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂`. Use `KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_chart x'.P.isLB (φ' z)`.

Establish `a` using `KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi`. Establish `b` using `KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk`. Rewrite using `[T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]`. Rewrite using `[RingHom.comp_apply, hF, hF', RingHom.comp_apply]`. Rewrite using `[RingHom.comp_apply, hε, hε']`.

Rewrite using `[← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]`. Both sides reduce to the same expression. Take `⟨i, hi⟩` from `exists_chart x'.P.isLB (φ' y)`. Establish `hj : φ (φ' y) ∈ x.P.L.U (j PUnit.unit)` using `mem_pull (F := φ' ≫ φ).1 hy.1`. Establish `a` using `KeyBasis.via_val (w := w) (n := l) (a' := s'.f) (a := s.f) h (𝟙 _ ≫ φ') y hj hi`.

Establish `b` using `KeyBasis.via_val (w := w') (n := l) (a' := s''.f) (a := s'.f) h' (𝟙 _) y hi hy.2`. Establish `t` using `T _ (𝟙 _) y (j PUnit.unit) i k hj hi hy.2`. Rewrite `a` using `[b, ← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, ← t]`. Use `(gs_appLE (φ' ≫ φ) _ _ hle (𝟙 _) y hy _).trans (a.trans ?_)` and prove the remaining obligations. Use `Eq.trans (congrArg₂ (· * ·) ?_ (gs_res _ y _ hy _).symm) (gs_mul _ y _ hy _ _).symm` and prove the remaining obligations.

Set `v : Γ(x''.P.A.left, (x.P.L.pull (φ' ≫ φ)).U j ⊓ x''.P.L.U k)ˣ` to `w''.s (j, k)`. Conclude with `((congrArg (gs (𝟙 _) y _) (Units.val_pow_eq_pow_val v l).symm).trans ((gs_unit (𝟙 _) y _ hy _).trans (congrArg Units.val (map_pow _ _ _)))).symm`.
-/
theorem keyVia_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'}
    {x'' : KeyIn R''} {f : R →+* R'} {f' : R' →+* R''} {φ w φ' w'} (H : KeyVia x' x f φ w)
    (H' : KeyVia x'' x' f' φ' w') : ∃ w'', KeyVia x'' x (f'.comp f) (φ' ≫ φ) w'' ∧
      ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l), SecVia x' x φ w s' s → SecVia x'' x' φ' w' s'' s' →
        SecVia x'' x (φ' ≫ φ) w'' s'' s := by
  obtain ⟨he, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨he', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' x.P.isLB x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec x.P.A := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨w'', ⟨he'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩,
    fun l s s' s'' h h' j k hle => fn_ext fun y hy => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).2 r₂
  · refine KeyPow.appLE_eq_of_stalk w'' x.th x''.th fun z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' z)
    have a := KeyComp.stalk_of_appLE_eq w x.th x'.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := KeyComp.stalk_of_appLE_eq w' x'.th x''.th hs' (𝟙 _) z i k hi hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl
  · obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' y)
    have hj : φ (φ' y) ∈ x.P.L.U (j PUnit.unit) := mem_pull (F := φ' ≫ φ).1 hy.1
    have a := KeyBasis.via_val (w := w) (n := l) (a' := s'.f) (a := s.f) h (𝟙 _ ≫ φ') y hj hi
    have b := KeyBasis.via_val (w := w') (n := l) (a' := s''.f) (a := s'.f) h' (𝟙 _) y hi hy.2
    have t := T _ (𝟙 _) y (j PUnit.unit) i k hj hi hy.2
    rw [b, ← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, ← t] at a
    refine (gs_appLE (φ' ≫ φ) _ _ hle (𝟙 _) y hy _).trans (a.trans ?_)
    refine Eq.trans (congrArg₂ (· * ·) ?_ (gs_res _ y _ hy _).symm) (gs_mul _ y _ hy _ _).symm
    let v : Γ(x''.P.A.left, (x.P.L.pull (φ' ≫ φ)).U j ⊓ x''.P.L.U k)ˣ := w''.s (j, k)
    exact ((congrArg (gs (𝟙 _) y _) (Units.val_pow_eq_pow_val v l).symm).trans
      ((gs_unit (𝟙 _) y _ hy _).trans (congrArg Units.val (map_pow _ _ _)))).symm

/- English proof (translation)
Use `choose h h₁ h₂ using ((KeyVia.main _ _ x x' f).2 φ w H).2.1`. Take `⟨_, _, _, hp, -⟩` from `H`. Set `D : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f) ⟶ 𝟙_ (Over (Sp R))` to `Over.homMk (spMap f) ((Category.comp_id _).trans (Category.id_comp _).symm)`. Use `⟨MonoidHom.mk' h fun a b => (h₂ _ _ ?_).symm, fun a b e => ?_, fun z z' => ⟨fun e => e ▸ h₁ z, h₂ z z'⟩⟩` and prove the remaining obligations. Establish `e` using `hp.2 _ (h a) (h b) (D ≫ a) (D ≫ b) (h₁ a).symm (h₁ b).symm`.

Rewrite `e` using `[← MonObj.comp_mul]`. Conclude with `e.symm`. Establish `e' : h a = h b` using `e haveI := x.P.isAb.proper haveI : IsDominant (spMap f) := ⟨by`. Use `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by` as an intermediate fact. Rewrite using `[(RingHom.injective_iff_ker_eq_bot f).1 hf]`.

Conclude with `bot_le)`. Conclude with `this⟩`. Use `Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) (f := a.left) (g := b.left) x.P.A.hom ((Over.w a).trans (Over.w b).symm) (spMap f) ?_)` and prove the remaining obligations. Conclude with `(h₁ a).symm.trans ((congrArg (·.left ≫ φ) e').trans (h₁ b))`.
-/
theorem exists_pull_hom {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'}
    {f : R →+* R'} {φ w} (H : KeyVia x' x f φ w) (hf : Function.Injective f) :
    ∃ h : Pt x →* Pt x', Function.Injective h ∧ ∀ z z', z' = h z ↔ z'.left ≫ φ = spMap f ≫ z.left := by
  choose h h₁ h₂ using ((KeyVia.main _ _ x x' f).2 φ w H).2.1
  obtain ⟨_, _, _, hp, -⟩ := H
  let D : Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap f) ⟶ 𝟙_ (Over (Sp R)) :=
    Over.homMk (spMap f) ((Category.comp_id _).trans (Category.id_comp _).symm)
  refine ⟨MonoidHom.mk' h fun a b => (h₂ _ _ ?_).symm, fun a b e => ?_, fun z z' => ⟨fun e => e ▸ h₁ z, h₂ z z'⟩⟩
  · have e := hp.2 _ (h a) (h b) (D ≫ a) (D ≫ b) (h₁ a).symm (h₁ b).symm
    rw [← MonObj.comp_mul] at e
    exact e.symm
  · have e' : h a = h b := e
    haveI := x.P.isAb.proper
    haveI : IsDominant (spMap f) := ⟨by
      have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2 (by
        rw [(RingHom.injective_iff_ker_eq_bot f).1 hf]; exact bot_le)
      exact this⟩
    refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) (f := a.left) (g := b.left) x.P.A.hom
      ((Over.w a).trans (Over.w b).symm) (spMap f) ?_)
    exact (h₁ a).symm.trans ((congrArg (·.left ≫ φ) e').trans (h₁ b))

/- English proof (translation)
Take `⟨-, -, -, het, -⟩` from `laws.mulN (Sp R) x.P _ hN1`. Use `haveI := het (by`. Use `hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom` as an intermediate fact. Rewrite using `[map_natCast] at this)` and apply the resulting hypothesis. Use `haveI := x.P.isAb.proper`.

Establish `e₁` using `KaLift.apply_closedPoint_eq x.P.A.hom a.left b.left (Over.w _) (Over.w _) p h`. Establish `e₂ : spMap (IsLocalRing.residue R) (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R` using `IsLocalRing.comap_closedPoint (IsLocalRing.residue R)`. Establish `e₃ : ∀ c : Pt x, (spMap (IsLocalRing.residue R) ≫ c.left) ≫ x.P.A.hom = spMap (IsLocalRing.residue R)` using `fun c => (Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue R) ≫ ·) (Over.w c)).trans (Category.comp_id _))`. Establish `e₄` using `KaLift.eq_of_apply_eq x.P.A.hom _ IsLocalRing.residue_surjective _ _ (e₃ a) (e₃ b) ((congrArg a.left e₂).trans (e₁.trans (congrArg b.left e₂).symm))`. Establish `e₅ : a ≫ Out.mulA x.P.A N = b ≫ Out.mulA x.P.A N`.

Rewrite using `[Out.mulA, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, ha, hb]`. Conclude with `Over.OverMorphism.ext (eq_of_isLocalRing_of_unramified (R := CommRingCat.of R) (Out.mulA x.P.A N).left (congrArg CommaMorphism.left e₅) (spMap (IsLocalRing.residue R)) ⟨_, e₂⟩ e₄)`.
-/
theorem eq_of_pow_eq_one (laws : Out.Laws) {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : KeyIn R) {N : ℕ}
    (hN1 : 1 ≤ N) (hN : IsUnit (N : R)) {a b : Pt x} (ha : a ^ N = 1) (hb : b ^ N = 1) (p : Sp R) (h : a.left p = b.left p) :
    a = b := by
  obtain ⟨-, -, -, het, -⟩ := laws.mulN (Sp R) x.P _ hN1
  haveI := het (by
    have := hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at this)
  haveI := x.P.isAb.proper
  have e₁ := KaLift.apply_closedPoint_eq x.P.A.hom a.left b.left (Over.w _) (Over.w _) p h
  have e₂ : spMap (IsLocalRing.residue R) (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
  have e₃ : ∀ c : Pt x, (spMap (IsLocalRing.residue R) ≫ c.left) ≫ x.P.A.hom = spMap (IsLocalRing.residue R) :=
    fun c => (Category.assoc _ _ _).trans ((congrArg (spMap (IsLocalRing.residue R) ≫ ·) (Over.w c)).trans
      (Category.comp_id _))
  have e₄ := KaLift.eq_of_apply_eq x.P.A.hom _ IsLocalRing.residue_surjective _ _ (e₃ a) (e₃ b)
    ((congrArg a.left e₂).trans (e₁.trans (congrArg b.left e₂).symm))
  have e₅ : a ≫ Out.mulA x.P.A N = b ≫ Out.mulA x.P.A N := by
    rw [Out.mulA, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, ha, hb]
  exact Over.OverMorphism.ext (eq_of_isLocalRing_of_unramified (R := CommRingCat.of R) (Out.mulA x.P.A N).left
    (congrArg CommaMorphism.left e₅) (spMap (IsLocalRing.residue R)) ⟨_, e₂⟩ e₄)

open EtBaseChange in

/- English proof (translation)
Take `⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩` from `H`. Establish `hφ : ⊤ ≤ (z'.left ≫ φ) ⁻¹ᵁ x.P.L.U c` using `fun p _ => by`. Rewrite using `[hz]`. Conclude with `h (show spMap f p ∈ ⊤ from trivial)`. Establish `hW` using `le_inf_pull (T := R') z'.left c c' hφ h'`.

Set `u : R'ˣ` to `Units.map (valH (T := R') z'.left _ hW).toMonoidHom (w.s (fun _ => c, c'))`. Establish `hu : valT (T` using `R') z'.left ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val = u := valT_eq _ _ hW _`. Use `⟨u, fun l sg sg' hsg => ?_, fun hzero => ?_⟩` and prove the remaining obligations. Establish `e` using `valT_via (T := R') hsg z'.left c c' hφ h'`. Rewrite `e` using `[hu]`.

Use `(_root_.mul_comm _ _).trans (e.symm.trans ?_)` and prove the remaining obligations. Conclude with `(congrArg (fun q => valT (T := R') q (x.P.L.U c) (sg.f c)) hz).trans (valT_spMap f z.left h _)`. Establish `ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T` using `DualNumber R) ((toUnit (epsR R) ≫ z) * x.v (k.cast hg)).left (x.P.L.U c) ((s (i.cast hg)).f c))) = (u : R') ^ n * TrivSqZeroExt.snd (valT (T := DualNumber R') ((toUnit (epsR R') ≫ z') * x'.v k).left (x'.P.L.U c') ((s' i).f c')) := fun i k => by`. Establish `t` using `translate_comp hp F hF₁ z z' hz (x.v (k.cast hg)) (x'.v k) (hv k)`. Establish `l₁` using `translate_le z (x.v (k.cast hg)) (x.basis.1 _) h`.

Establish `l₂` using `translate_le z' (x'.v k) (x'.basis.1 _) h'`. Establish `l₃ : ⊤ ≤ (((toUnit (epsR R') ≫ z') * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U c` using `fun p _ => by`. Rewrite using `[t]`. Conclude with `l₁ (show spMap F p ∈ ⊤ from trivial)`. Establish `e` using `valT_via (T := DualNumber R') (hs i) _ c c' l₃ l₂`.

Establish `e₂` using `(congrArg (fun q => valT (T := DualNumber R') q (x.P.L.U c) ((s (i.cast hg)).f c)) t).trans (valT_spMap F _ l₁ _)`. Use `(snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)` and prove the remaining obligations. Use `(snd_pow_mul _ _ _ ((fst_valT_translate z' (x'.v k) (x'.basis.1 _) h' _).trans (hzero i))).trans ?_` and prove the remaining obligations. Conclude with `congrArg (· ^ n * _) ((fst_valT_translate z' (x'.v k) (x'.basis.1 _) hW _).trans hu)`. Unfold `jac`.

Rewrite using `[RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n, pow_mul]`. Establish `hc : x.P.g = Fintype.card (Fin x'.P.g)` using `hg.symm.trans (Fintype.card_fin _).symm`. Use `(congrArg (fun m => ((u : R') ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)` and prove the remaining obligations. Use `congr 1`. Use extensionality with `i k`.

Conclude with `(ent i k).symm`.
-/
theorem exists_unit_val_jac {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    {n : ℕ} (hg : x'.P.g = x.P.g) {s : Fin x.P.g → RR x n} {s' : Fin x'.P.g → RR x' n} (H : KeyVia x' x f φ w)
    (hs : ∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) {z : Pt x} {z' : Pt x'}
    (hz : z'.left ≫ φ = spMap f ≫ z.left) {c c'} (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ z'.left ⁻¹ᵁ x'.P.L.U c') :
    ∃ u : R'ˣ, (∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l), SecVia x' x φ w sg' sg →
      valT (T := R') z'.left (x'.P.L.U c') (sg'.f c') * (u : R') ^ l = f (valT (T := R) z.left (x.P.L.U c) (sg.f c))) ∧
      ((∀ i, valT (T := R') z'.left (x'.P.L.U c') ((s' i).f c') = 0) →
        jac x' s' z' c' * (u : R') ^ (x.P.g * n) = f (jac x s z c)) := by
  obtain ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ := H
  have hφ : ⊤ ≤ (z'.left ≫ φ) ⁻¹ᵁ x.P.L.U c := fun p _ => by
    rw [hz]
    exact h (show spMap f p ∈ ⊤ from trivial)
  have hW := le_inf_pull (T := R') z'.left c c' hφ h'
  let u : R'ˣ := Units.map (valH (T := R') z'.left _ hW).toMonoidHom (w.s (fun _ => c, c'))
  have hu : valT (T := R') z'.left ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val = u :=
    valT_eq _ _ hW _
  refine ⟨u, fun l sg sg' hsg => ?_, fun hzero => ?_⟩
  · have e := valT_via (T := R') hsg z'.left c c' hφ h'
    rw [hu] at e
    refine (_root_.mul_comm _ _).trans (e.symm.trans ?_)
    exact (congrArg (fun q => valT (T := R') q (x.P.L.U c) (sg.f c)) hz).trans (valT_spMap f z.left h _)
  · have ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z) * x.v (k.cast hg)).left
        (x.P.L.U c) ((s (i.cast hg)).f c))) = (u : R') ^ n * TrivSqZeroExt.snd (valT (T := DualNumber R')
          ((toUnit (epsR R') ≫ z') * x'.v k).left (x'.P.L.U c') ((s' i).f c')) := fun i k => by
      have t := translate_comp hp F hF₁ z z' hz (x.v (k.cast hg)) (x'.v k) (hv k)
      have l₁ := translate_le z (x.v (k.cast hg)) (x.basis.1 _) h
      have l₂ := translate_le z' (x'.v k) (x'.basis.1 _) h'
      have l₃ : ⊤ ≤ (((toUnit (epsR R') ≫ z') * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U c := fun p _ => by
        rw [t]
        exact l₁ (show spMap F p ∈ ⊤ from trivial)
      have e := valT_via (T := DualNumber R') (hs i) _ c c' l₃ l₂
      have e₂ := (congrArg (fun q => valT (T := DualNumber R') q (x.P.L.U c) ((s (i.cast hg)).f c)) t).trans
        (valT_spMap F _ l₁ _)
      refine (snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)
      refine (snd_pow_mul _ _ _ ((fst_valT_translate z' (x'.v k) (x'.basis.1 _) h' _).trans (hzero i))).trans ?_
      exact congrArg (· ^ n * _) ((fst_valT_translate z' (x'.v k) (x'.basis.1 _) hW _).trans hu)
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n,
      pow_mul]
    have hc : x.P.g = Fintype.card (Fin x'.P.g) := hg.symm.trans (Fintype.card_fin _).symm
    refine (congrArg (fun m => ((u : R') ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)
    congr 1
    ext i k
    exact (ent i k).symm

/- English proof (translation)
Take `⟨i, hi⟩` from `exists_chart x.P.isLB (z.left (IsLocalRing.closedPoint R))`. Conclude with `⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map z.left.continuous).mem_open (x.P.L.U i).isOpen hi⟩`.
-/
theorem exists_chart_point {R : Type} [CommRing R] [IsLocalRing R] {x : KeyIn R} (z : Pt x) :
    ∃ i, ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U i := by
  obtain ⟨i, hi⟩ := exists_chart x.P.isLB (z.left (IsLocalRing.closedPoint R))
  exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map z.left.continuous).mem_open (x.P.L.U i).isOpen hi⟩

/- English proof (translation)
Take `⟨hz₁, hz₂, hz₃, hz₄, hz₅⟩` from `E`. Use `choose ch' hch' using fun a => exists_chart_point (z' a)`. Use `choose u hval hjac using fun a => exists_unit_val_jac hg H hs (hz' a) (hz₁ a) (hch' a)`. Take `⟨_, _, F, hp, -⟩` from `H`. Establish `hzero : ∀ a i, valT (T` using `R') (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by`.

Establish `e` using `hval a n _ _ (hs i)`. Rewrite `e` using `[hz₂, map_zero]`. Conclude with `((u a).isUnit.pow n).mul_left_eq_zero.1 e`. Use `⟨ch', hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Conclude with `isUnit_of_mul_isUnit_left (hjac a (hzero a) ▸ (hz₃ a).map f)`.

Use `hz₄ a a' h (spMap f p) ?_` and prove the remaining obligations. Establish `e₁` using `congrArg (fun q => q p) (hz' a)`. Establish `e₂` using `congrArg (fun q => q p) (hz' a')`. Conclude with `e₁.symm.trans ((congrArg φ e).trans e₂)`. Take `⟨a, p, hp'⟩` from `hz₅ (φ y) fun i h => hy (i.cast hg.symm) (EtBaseChange.mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)`.

Establish `sq : IsPullback (spMap f) (z' a).left (z a).left φ`. Use `IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm` and prove the remaining obligations. Establish `e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _` using `Over.w (z' a)`. Establish `e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _` using `Over.w (z a)`. Rewrite using `[e₁, e₂]`.

Conclude with `IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp R')) (f := 𝟙 (Sp R)) (g := spMap f) ⟨by simp⟩`. Take `⟨q, -, hq⟩` from `Scheme.exists_preimage_of_isPullback sq p y hp'`. Conclude with `⟨a, q, hq⟩`.
-/
theorem etZ_pull {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'}
    {φ w} {n d : ℕ} (hg : x'.P.g = x.P.g) {s : Fin x.P.g → RR x n} {s' : Fin x'.P.g → RR x' n} (H : KeyVia x' x f φ w)
    (hs : ∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) {z : Fin d → Pt x} {z' : Fin d → Pt x'} {ch}
    (hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left) (E : EtZ x s z ch) : ∃ ch', EtZ x' s' z' ch' := by
  obtain ⟨hz₁, hz₂, hz₃, hz₄, hz₅⟩ := E
  choose ch' hch' using fun a => exists_chart_point (z' a)
  choose u hval hjac using fun a => exists_unit_val_jac hg H hs (hz' a) (hz₁ a) (hch' a)
  obtain ⟨_, _, F, hp, -⟩ := H
  have hzero : ∀ a i, valT (T := R') (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by
    have e := hval a n _ _ (hs i)
    rw [hz₂, map_zero] at e
    exact ((u a).isUnit.pow n).mul_left_eq_zero.1 e
  refine ⟨ch', hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩
  · exact isUnit_of_mul_isUnit_left (hjac a (hzero a) ▸ (hz₃ a).map f)
  · refine hz₄ a a' h (spMap f p) ?_
    have e₁ := congrArg (fun q => q p) (hz' a)
    have e₂ := congrArg (fun q => q p) (hz' a')
    exact e₁.symm.trans ((congrArg φ e).trans e₂)
  · obtain ⟨a, p, hp'⟩ := hz₅ (φ y) fun i h =>
      hy (i.cast hg.symm) (EtBaseChange.mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)
    have sq : IsPullback (spMap f) (z' a).left (z a).left φ := by
      refine IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm
      have e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _ := Over.w (z' a)
      have e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _ := Over.w (z a)
      rw [e₁, e₂]
      exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp R')) (f := 𝟙 (Sp R)) (g := spMap f) ⟨by simp⟩
    obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq p y hp'
    exact ⟨a, q, hq⟩

/- English proof (translation)
Simplify using `only [kaForm, tComb, map_mul, map_zpow, map_pow, map_prod]`.
-/
theorem kaForm_map' {R R' : Type} [CommRing R] [CommRing R'] (F : Rˣ →* R'ˣ) (g n l l' : ℕ) (t t' J : Rˣ)
    (lam lam' : ℕ → Rˣ) : F (kaForm g n l l' t t' lam lam' J) =
      kaForm g n l l' (F t) (F t') (fun j => F (lam j)) (fun j => F (lam' j)) (F J) := by
  simp only [kaForm, tComb, map_mul, map_zpow, map_pow, map_prod]

/- English proof (translation)
Introduce `j i h`. Rewrite using `[map_mul, map_mul, ha j i h, hb j i h, ← hk, pow_add, _root_.mul_mul_mul_comm]`.
-/
theorem via_mul' {X Y : Scheme.{0}} {L : LB X} {L' : LB Y} {φ : Y ⟶ X} {w : LB.Iso L' (L.pull φ)} {l l' k : ℕ}
    (hk : l + l' = k) {a' b' : ∀ i, Γ(Y, L'.U i)} {a b : ∀ j, Γ(X, L.U j)} (ha : KeyVia.Via w l a' a)
    (hb : KeyVia.Via w l' b' b) : KeyVia.Via w k (fun i => a' i * b' i) (fun j => a j * b j) := by
  intro j i h
  rw [map_mul, map_mul, ha j i h, hb j i h, ← hk, pow_add, _root_.mul_mul_mul_comm]

/- English proof (translation)
Take `⟨-, -, -, ⟨hP, -⟩, -⟩` from `hx`. Establish `H` using `KeyVia.Via.comb (w := w) (l := k) (b' := fun i => (b' i).f) (b := fun i => (b i).f) f x.P.A.hom x'.P.A.hom hP.w hb c`. Establish `H'` using `via_mul' (w := w) hk (a' := s'.f) (b' := e'.f) (a := s.f) (b := e.f) hs he`. Establish `H''` using `(congrArg (KeyVia.Via w k _) (funext hc)).mp H'`. Conclude with `fun i => congrFun (KeyVia.Via.unique x.P.isLB H'' H) i`.
-/
theorem coords_mul' {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    (hx : KeyVia x' x f φ w) {n l k N : ℕ} (hk : n + l = k) {s : RR x n} {s' : RR x' n} {e : RR x l} {e' : RR x' l}
    {b : Fin N → RR x k} {b' : Fin N → RR x' k} {c : Fin N → R} (hs : SecVia x' x φ w s' s)
    (he : SecVia x' x φ w e' e) (hb : ∀ i, SecVia x' x φ w (b' i) (b i))
    (hc : Coords x b c (fun i => (show Γ(x.P.A.left, x.P.L.U i) from s.f i) * (show Γ(x.P.A.left, x.P.L.U i) from e.f i))) :
    Coords x' b' (fun i => f (c i))
      (fun i => (show Γ(x'.P.A.left, x'.P.L.U i) from s'.f i) * (show Γ(x'.P.A.left, x'.P.L.U i) from e'.f i)) := by
  obtain ⟨-, -, -, ⟨hP, -⟩, -⟩ := hx
  have H := KeyVia.Via.comb (w := w) (l := k) (b' := fun i => (b' i).f) (b := fun i => (b i).f) f x.P.A.hom
    x'.P.A.hom hP.w hb c
  have H' := via_mul' (w := w) hk (a' := s'.f) (b' := e'.f) (a := s.f) (b := e.f) hs he
  have H'' := (congrArg (KeyVia.Via w k _) (funext hc)).mp H'
  exact fun i => congrFun (KeyVia.Via.unique x.P.isLB H'' H) i

/- English proof (translation)
Establish `e : (kosD m ev).map f = kosD (fun i j j' => (m i j j').map f) (fun j => (ev j).map f)`. Use extensionality with `p q`. Apply the tactic sequence `rcases p with p | a <;> rcases q with ⟨I, k⟩ | b <;> simp [kosD, apply_ite f]`. Take `⟨t, rfl⟩` from `(TorsionUnique.torsSq_unique _ _ _ _ t t hC H H).2`. Establish `H'` using `e ▸ torsSq_map R _ kdeg _ F f _ H`.

Establish `hC' : IsCx kdeg (kosD (fun i j j' => (m i j j').map f) (fun j => (ev j).map f))`. Rewrite using `[← e]`. Conclude with `⟨fun p q h => by rw [Matrix.map_apply, hC.1 p q h, map_zero], by rw [← Matrix.map_mul, hC.2, Matrix.map_zero _ (map_zero f)]⟩`. Take `⟨P, rfl⟩` from `(Matrix.isUnit_iff_isUnit_det Q).2 hQ.isUnit`. Take `⟨t', h₁, h₂⟩` from `torsSq_kosD_conj F g d N (fun i j j' => (m i j j').map f) (fun i j j' => (m i j j').map f) (fun j => (ev j).map f) ev' (fun _ => 1) P⁻¹ (Units.map f.toMonoidHom t) (fun i j _ => by simp) (by rw [hev, ← Matrix.mul_assoc, Units.inv_mul]; simp) hC' H'`.

Simplify using `only [map_one, one_zpow, Finset.prod_const_one, _root_.mul_one, map_inv, inv_pow, mul_inv_eq_iff_eq_mul] at h₂`. Rewrite `h₁` using `[h₂]`. Conclude with `h₁`.
-/
theorem torsSq_kosD_mul {R F : Type} [CommRing R] [Field F] (f : R →+* F) {g d : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (ev' : ∀ j, Matrix (Fin d) (Fin (N j)) F) (Q : Matrix (Fin d) (Fin d) F) (t : R) (hQ : Q.det ≠ 0)
    (hev : ev' 0 = Q * (ev 0).map f) (hC : IsCx kdeg (kosD m ev)) (H : TorsSq kdeg (kosD m ev) t) :
    TorsSq kdeg (kosD (fun i j j' => (m i j j').map f) ev') (f t * Q.det ^ 2) := by
  have e : (kosD m ev).map f = kosD (fun i j j' => (m i j j').map f) (fun j => (ev j).map f) := by
    ext p q
    rcases p with p | a <;> rcases q with ⟨I, k⟩ | b <;> simp [kosD, apply_ite f]
  obtain ⟨t, rfl⟩ := (TorsionUnique.torsSq_unique _ _ _ _ t t hC H H).2
  have H' := e ▸ torsSq_map R _ kdeg _ F f _ H
  have hC' : IsCx kdeg (kosD (fun i j j' => (m i j j').map f) (fun j => (ev j).map f)) := by
    rw [← e]
    exact ⟨fun p q h => by rw [Matrix.map_apply, hC.1 p q h, map_zero],
      by rw [← Matrix.map_mul, hC.2, Matrix.map_zero _ (map_zero f)]⟩
  obtain ⟨P, rfl⟩ := (Matrix.isUnit_iff_isUnit_det Q).2 hQ.isUnit
  obtain ⟨t', h₁, h₂⟩ := torsSq_kosD_conj F g d N (fun i j j' => (m i j j').map f) (fun i j j' => (m i j j').map f)
    (fun j => (ev j).map f) ev' (fun _ => 1) P⁻¹ (Units.map f.toMonoidHom t) (fun i j _ => by simp)
    (by rw [hev, ← Matrix.mul_assoc, Units.inv_mul]; simp) hC' H'
  simp only [map_one, one_zpow, Finset.prod_const_one, _root_.mul_one, map_inv, inv_pow, mul_inv_eq_iff_eq_mul] at h₂
  rw [h₂] at h₁
  exact h₁

/- English proof (translation)
Substitute `hd` using the available equality. Take `⟨⟨A', ab, g', sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩` from `x'`. Take `rfl : g' = x.P.g` from `hg`. Set `x' : KeyIn F` to `⟨⟨A', ab, x.P.g, sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩`. Establish `hp : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f)` using `hx.choose_spec.choose_spec.choose_spec.1.1`.

Use `choose ch hch using fun a => exists_chart_point (z a)`. Use `choose u hval hjac using fun a => exists_unit_val_jac (x := x) (x' := x') rfl hx hs (hz a) (hch a) (E.1 a)`. Use `replace hjac := fun a => hjac a (E.2.1 a)`. Establish `hzero : ∀ a i, valT (T` using `O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0 := fun a i => hf ((hval a n _ _ (hs i)).symm.trans ((congrArg (· * _) (E.2.1 a i)).trans ((zero_mul _).trans (map_zero f).symm)))`. Establish `hne : ∀ a, f (jac x s (z a) (ch a)) ≠ 0` using `fun a => hjac a ▸ ((E.2.2.1 a).mul ((u a).isUnit.pow _)).ne_zero`.

Establish `hinj : Function.Injective z` using `fun a a' e => by`. Assume the negation of the conclusion as `h`. Establish `e₂ : (z' a).left = (z' a').left` using `hp.hom_ext (by rw [hz, hz, e]) ((Over.w _).trans (Over.w _).symm)`. Conclude with `E.2.2.2.1 a a' h (IsLocalRing.closedPoint F) (by rw [e₂])`. Establish `hcov : ∀ y : x.P.A.left, x.P.A.hom y ≠ IsLocalRing.closedPoint O → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y` using `fun y hy₀ hy => by`.

Establish `e : x.P.A.hom y = spMap f (IsLocalRing.closedPoint F)`. Use `PrimeSpectrum.ext ?_` and prove the remaining obligations. Establish `e₁ : PrimeSpectrum.asIdeal (x.P.A.hom y) = (⊥ : Ideal O)`. Assume the negation of the conclusion as `h`. Conclude with `hy₀ (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime h (PrimeSpectrum.isPrime _))))`.

Use `e₁.trans (Eq.symm ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.comap f (IsLocalRing.maximalIdeal F) = ⊥`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`. Conclude with `Ideal.comap_bot_of_injective f hf`. Take `⟨y', rfl, -⟩` from `Scheme.exists_preimage_of_isPullback hp y (IsLocalRing.closedPoint F) e`.

Take `⟨a, p, rfl⟩` from `E.2.2.2.2 y' fun i h => hy i (KaLift.mem_nonzeroLocus_of_via (hs i) y' h)`. Conclude with `⟨a, spMap f p, (congrArg (fun q => q p) (hz a)).symm⟩`. Establish `hex` using `((KeyVia.main O F x x' f).2 φ w hx).1`. Set `J : Fˣ` to `Units.mk0 (f (∏ a, jac x s (z a) (ch a))) (by`. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun a _ => hne a)`. Establish `key : ∀ k, k = l ∨ k = l' → x.P.g * n < k → ∃ (b' : ∀ j, Fin ((k - j * n) ^ x.P.g) → RR x' (k - j * n)) (lam : ℕ → Oˣ) (t e : Oˣ) (dl : Fˣ), (∀ j ≤ x.P.g, IsBasis x' (b' j) ∧ IsSquareDeterminantComparison x' (k - j * n) (al (k - j * n)) (b' j) (Units.map f.toMonoidHom (lam j))) ∧ …`. Introduce `k hk hl`. Establish `hpos : ∀ j ≤ x.P.g, 1 ≤ k - j * n` using `fun j hj => by`. Establish `h₁ : j * n ≤ x.P.g * n` using `Nat.mul_le_mul_right n hj`.

Use linear arithmetic over natural numbers and integers. Establish `hb : ∀ j, ∃ b : Fin ((k - j * n) ^ x.P.g) → RR x (k - j * n), ∃ lam : Oˣ, j ≤ x.P.g → IsBasis x b ∧ IsSquareDeterminantComparison x (k - j * n) (al (k - j * n)) b lam` using `fun j => by`. Distinguish the cases in `hj : j ≤ x.P.g`. Take `⟨b, hb⟩` from `(T.basis_powerSections_local_baseChange laws O x (k - j * n) (hpos j hj)).1`. Take `⟨ξ, h₁, h₂⟩` from `hξ k hk j hj`.

Use `haveI := x.P.isAb.comm`. Establish `h₃ : ∀ I r, ξ I r ^ (k - j * n) = 1` using `fun I r => pow_eq_one_of_ker (hpos j hj) (hadm.2.2.2 _) (ξ I) (fun c => (List.prod_ofFn).symm.trans (h₂ I c)) r`. Take `⟨lam, hlam⟩` from `T.exists_l2Val_field_or_dvr_split_kernel laws O x _ _ b ξ (hO _ (hpos j hj)) (hadm.2.2.2 _) hb (fun I I' hI p => by`. Assume the negation of the conclusion as `h`. Use `hI (h₁ (funext fun r => ?_))` and prove the remaining obligations.

Conclude with `eq_of_pow_eq_one laws x (hpos j hj) (hO _ (hpos j hj)) (h₃ I r) (h₃ I' r) p (not_not.1 fun h' => h ⟨r, h'⟩)) h₂`. Conclude with `⟨b, lam, fun _ => ⟨hb, hlam⟩⟩`. Conclude with `⟨fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, 1, fun h => absurd h hj⟩`. Use `choose b lam hb using hb`. Take `⟨m, hm⟩` from `(KoszulCx.koszul_isCx O x n k _ s b z ch hl fun j hj => (hb j hj).1).1`.

Take `⟨ev, Pm, t, h₁, h₂, h₃, e, h₄⟩` from `T.discriminant_eq_jacobian_complete_intersection_dvr laws O x n k _ s b m z ch (by have := hadm.1; omega) hl (fun j hj => (hb j hj).1) hm hfin hch hzero (fun a h => hne a (by rw [h, map_zero])) hinj hcov`. Take `⟨t, rfl⟩` from `(TorsionUnique.torsSq_unique _ _ _ _ t t h₂ h₃ h₃).2`. Establish `hdl : f Pm.det ≠ 0` using `fun h => J.ne_zero (by`. Express the relevant statement in the definitionally equal form `f _ = 0`. Rewrite using `[← h₄, map_mul, map_pow, h]`.

Use the proof step `simp)`. Use `choose b' hb' using fun j i => (hex _ (b j i)).exists`. Use `⟨b', lam, t, e, Units.mk0 _ hdl, fun j hj => ⟨?_, ?_⟩, ⟨fun i j j' => (m i j j').map f, fun i j hj i' => ?_, ?_⟩, Units.ext ?_⟩` and prove the remaining obligations. Conclude with `(T.basis_powerSections_local_baseChange laws O x _ (hpos j hj)).2 (b j) (hb j hj).1 F f x' φ w (b' j) hx (hb' j)`. Conclude with `T.l2ComparisonNumber_baseChange_similitude_alt O F x x' f φ w _ _ rfl (b j) (b' j) (lam j) (hadm.2.2.2 _) hx (hb' j) (hb j hj).2`.

Establish `h₅ : (j + 1) * n ≤ x.P.g * n` using `Nat.mul_le_mul_right n hj`. Establish `h₆ : n + (k - (j + 1) * n) = k - j * n`. Rewrite `h₅`, the goal using `[Nat.add_mul, Nat.one_mul]`. Use linear arithmetic over natural numbers and integers. Conclude with `coords_mul' hx h₆ (hs i) (hb' (j + 1) i') (hb' j) (hm i j hj i')`.

Establish `hdet : (Matrix.diagonal (fun a => (((u a ^ (k - 0 * n))⁻¹ : Fˣ) : F)) * Pm.map f).det = (((∏ a, u a) ^ (-(k : ℤ)) : Fˣ) : F) * f Pm.det`. Rewrite using `[Matrix.det_mul, Matrix.det_diagonal, ← Units.coe_prod, Finset.prod_inv_distrib, Finset.prod_pow, RingHom.map_det, Nat.zero_mul, Nat.sub_zero, zpow_neg, zpow_natCast]`. Both sides reduce to the same expression. Establish `H` using `torsSq_kosD_mul f m ev (fun j => Matrix.of fun a i => valT (T := F) (z' a).left (x'.P.L.U (ch' a)) ((b' j i).f (ch' a))) _ t (hdet ▸ mul_ne_zero (Units.ne_zero _) hdl) (by`. Rewrite using `[Matrix.mul_assoc, ← Matrix.map_mul, ← h₁]`.

Use extensionality with `a i`. Rewrite using `[Matrix.diagonal_mul]`. Use `((Units.eq_inv_mul_iff_mul_eq _).2 ?_)` and prove the remaining obligations. Conclude with `(_root_.mul_comm _ _).trans ((congrArg _ (Units.val_pow_eq_pow_val _ _)).trans (hval a _ (b 0 i) (b' 0 i) (hb' 0 i)))) h₂ h₃`. Establish `e₁ : (∏ a, u a) ^ (-2 * (k : ℤ)) = ((∏ a, u a) ^ (-(k : ℤ))) ^ 2` using `by group`.

Rewrite `H` using `[hdet, mul_pow, ← _root_.mul_assoc]`. Rewrite using `[e₁]`. Conclude with `H`. Express the relevant statement in the definitionally equal form `f _ = f e * f Pm.det ^ 2`. Rewrite using `[← h₄, map_mul, map_pow, _root_.mul_comm]`.

Take `⟨c, lam, t, e, dl, hc, hct, hJ⟩` from `key l (Or.inl rfl) hadm.2.1`. Take `⟨c₂, lam₂, t₂, e₂, dl₂, hc₂, hct₂, hJ₂⟩` from `key l' (Or.inr rfl) (hadm.2.1.trans hadm.2.2.1)`. Establish `hdl : dl₂ ^ 2 = Units.map f.toMonoidHom (e₂⁻¹ * e) * dl ^ 2`. Rewrite using `[map_mul, map_inv, _root_.mul_assoc, ← hJ, hJ₂, inv_mul_cancel_left]`. Use `⟨kaForm x.P.g n l l' t (t₂ * (e₂⁻¹ * e)) lam lam₂ e, z', ch', c, c₂, _, _, Units.map f.toMonoidHom e * (∏ a, u a) ^ (-((x.P.g * n : ℕ) : ℤ)) * dl ^ 2, _, _, E, ?_, hc, hc₂, hct, hct₂, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_right_comm, ← hJ, zpow_neg, zpow_natCast, Units.val_mul, eq_comm, Units.eq_mul_inv_iff_mul_eq, Units.val_pow_eq_pow_val, Units.coe_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Conclude with `(Finset.prod_congr rfl fun a _ => hjac a).trans (map_prod f _ _).symm`. Establish `H` using `kaForm_homogeneous F x.P.g n l l' (Units.map f.toMonoidHom t) (Units.map f.toMonoidHom (t₂ * (e₂⁻¹ * e))) (Units.map f.toMonoidHom e) (∏ a, u a) 1 dl (fun j => Units.map f.toMonoidHom (lam j)) (fun j => Units.map f.toMonoidHom (lam₂ j)) (fun _ => 1) (fun _ => 1) hadm.2.1 hadm.2.2 …`. Simplify using `only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at H`. Use `(kaForm_map' _ _ _ _ _ _ _ _ _ _).trans (H.symm.trans ?_)` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[hdl, map_mul _ t₂]`. The two sides agree by associativity and commutativity.
-/
theorem exists_unit_kaVal (laws : Out.Laws) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {F : Type} [Field F] {f : O →+* F} {x : KeyIn O} {x' : KeyIn F}
    {φ w} {n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (hg : x'.P.g = x.P.g) {s : Fin x.P.g → RR x n}
    {s' : Fin x'.P.g → RR x' n} {d : ℕ} (hd : d = x'.P.g.factorial * n ^ x'.P.g) (z : Fin d → Pt x) {z' : Fin d → Pt x'}
    {ch'} (hO : ∀ m : ℕ, 1 ≤ m → IsUnit (m : O)) (hf : Function.Injective f) (hadm : admitted x.P.g n l l' al)
    (hx : KeyVia x' x f φ w) (hs : ∀ i, SecVia x' x φ w (s' i) (s (i.cast hg)))
    (hfin : {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite)
    (E : EtZ x' s' z' ch') (hz : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left)
    (hξ : ∀ k, k = l ∨ k = l' → ∀ j ≤ x.P.g, ∃ ξ : (Fin 4 → Fin ((k - j * n) ^ x.P.g)) → Fin 4 → Pt x,
      Function.Injective ξ ∧ ∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al (k - j * n) r c).prod = 1) :
    ∃ u : Oˣ, KaVal x' n l l' al s' (Units.map f.toMonoidHom u) := by
  subst hd
  obtain ⟨⟨A', ab, g', sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩ := x'
  obtain rfl : g' = x.P.g := hg
  let x' : KeyIn F := ⟨⟨A', ab, x.P.g, sm, L', hL', p₁, p₂, p₃, p₄⟩, q₁, q₂, q₃, q₄, q₅, q₆, q₇⟩
  have hp : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f) := hx.choose_spec.choose_spec.choose_spec.1.1
  choose ch hch using fun a => exists_chart_point (z a)
  choose u hval hjac using fun a => exists_unit_val_jac (x := x) (x' := x') rfl hx hs (hz a) (hch a) (E.1 a)
  replace hjac := fun a => hjac a (E.2.1 a)
  have hzero : ∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0 := fun a i =>
    hf ((hval a n _ _ (hs i)).symm.trans ((congrArg (· * _) (E.2.1 a i)).trans ((zero_mul _).trans (map_zero f).symm)))
  have hne : ∀ a, f (jac x s (z a) (ch a)) ≠ 0 := fun a =>
    hjac a ▸ ((E.2.2.1 a).mul ((u a).isUnit.pow _)).ne_zero
  have hinj : Function.Injective z := fun a a' e => by
    by_contra h
    have e₂ : (z' a).left = (z' a').left := hp.hom_ext (by rw [hz, hz, e]) ((Over.w _).trans (Over.w _).symm)
    exact E.2.2.2.1 a a' h (IsLocalRing.closedPoint F) (by rw [e₂])
  have hcov : ∀ y : x.P.A.left, x.P.A.hom y ≠ IsLocalRing.closedPoint O → (∀ i, y ∉ Out.nonzeroLocus (s i)) →
      ∃ a, ∃ p : Sp O, (z a).left p = y := fun y hy₀ hy => by
    have e : x.P.A.hom y = spMap f (IsLocalRing.closedPoint F) := by
      refine PrimeSpectrum.ext ?_
      have e₁ : PrimeSpectrum.asIdeal (x.P.A.hom y) = (⊥ : Ideal O) := by
        by_contra h
        exact hy₀ (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
          (Ring.DimensionLEOne.maximalOfPrime h (PrimeSpectrum.isPrime _))))
      refine e₁.trans (Eq.symm ?_)
      change Ideal.comap f (IsLocalRing.maximalIdeal F) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective f hf
    obtain ⟨y', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hp y (IsLocalRing.closedPoint F) e
    obtain ⟨a, p, rfl⟩ := E.2.2.2.2 y' fun i h => hy i (KaLift.mem_nonzeroLocus_of_via (hs i) y' h)
    exact ⟨a, spMap f p, (congrArg (fun q => q p) (hz a)).symm⟩
  have hex := ((KeyVia.main O F x x' f).2 φ w hx).1
  let J : Fˣ := Units.mk0 (f (∏ a, jac x s (z a) (ch a))) (by
    rw [map_prod]; exact Finset.prod_ne_zero_iff.2 fun a _ => hne a)
  have key : ∀ k, k = l ∨ k = l' → x.P.g * n < k →
      ∃ (b' : ∀ j, Fin ((k - j * n) ^ x.P.g) → RR x' (k - j * n)) (lam : ℕ → Oˣ) (t e : Oˣ) (dl : Fˣ),
        (∀ j ≤ x.P.g, IsBasis x' (b' j) ∧
          IsSquareDeterminantComparison x' (k - j * n) (al (k - j * n)) (b' j) (Units.map f.toMonoidHom (lam j))) ∧
        KosVal x' k s' z' ch' b' (Units.map f.toMonoidHom t * (∏ a, u a) ^ (-2 * (k : ℤ)) * dl ^ 2 : Fˣ) ∧
        J = Units.map f.toMonoidHom e * dl ^ 2 := by
    intro k hk hl
    have hpos : ∀ j ≤ x.P.g, 1 ≤ k - j * n := fun j hj => by
      have h₁ : j * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
      omega
    have hb : ∀ j, ∃ b : Fin ((k - j * n) ^ x.P.g) → RR x (k - j * n), ∃ lam : Oˣ, j ≤ x.P.g →
        IsBasis x b ∧ IsSquareDeterminantComparison x (k - j * n) (al (k - j * n)) b lam := fun j => by
      by_cases hj : j ≤ x.P.g
      · obtain ⟨b, hb⟩ := (T.basis_powerSections_local_baseChange laws O x (k - j * n) (hpos j hj)).1
        obtain ⟨ξ, h₁, h₂⟩ := hξ k hk j hj
        haveI := x.P.isAb.comm
        have h₃ : ∀ I r, ξ I r ^ (k - j * n) = 1 := fun I r =>
          pow_eq_one_of_ker (hpos j hj) (hadm.2.2.2 _) (ξ I) (fun c => (List.prod_ofFn).symm.trans (h₂ I c)) r
        obtain ⟨lam, hlam⟩ := T.exists_l2Val_field_or_dvr_split_kernel laws O x _ _ b ξ (hO _ (hpos j hj)) (hadm.2.2.2 _) hb (fun I I' hI p => by
          by_contra h
          refine hI (h₁ (funext fun r => ?_))
          exact eq_of_pow_eq_one laws x (hpos j hj) (hO _ (hpos j hj)) (h₃ I r) (h₃ I' r) p
            (not_not.1 fun h' => h ⟨r, h'⟩)) h₂
        exact ⟨b, lam, fun _ => ⟨hb, hlam⟩⟩
      · exact ⟨fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, 1, fun h => absurd h hj⟩
    choose b lam hb using hb
    obtain ⟨m, hm⟩ := (KoszulCx.koszul_isCx O x n k _ s b z ch hl fun j hj => (hb j hj).1).1
    obtain ⟨ev, Pm, t, h₁, h₂, h₃, e, h₄⟩ := T.discriminant_eq_jacobian_complete_intersection_dvr laws O x n k _ s b m z ch (by have := hadm.1; omega) hl
      (fun j hj => (hb j hj).1) hm hfin hch hzero (fun a h => hne a (by rw [h, map_zero])) hinj hcov
    obtain ⟨t, rfl⟩ := (TorsionUnique.torsSq_unique _ _ _ _ t t h₂ h₃ h₃).2
    have hdl : f Pm.det ≠ 0 := fun h => J.ne_zero (by
      change f _ = 0
      rw [← h₄, map_mul, map_pow, h]; simp)
    choose b' hb' using fun j i => (hex _ (b j i)).exists
    refine ⟨b', lam, t, e, Units.mk0 _ hdl, fun j hj => ⟨?_, ?_⟩, ⟨fun i j j' => (m i j j').map f, fun i j hj i' => ?_, ?_⟩,
      Units.ext ?_⟩
    · exact (T.basis_powerSections_local_baseChange laws O x _ (hpos j hj)).2 (b j) (hb j hj).1 F f x' φ w (b' j) hx (hb' j)
    · exact T.l2ComparisonNumber_baseChange_similitude_alt O F x x' f φ w _ _ rfl (b j) (b' j) (lam j) (hadm.2.2.2 _) hx (hb' j) (hb j hj).2
    · have h₅ : (j + 1) * n ≤ x.P.g * n := Nat.mul_le_mul_right n hj
      have h₆ : n + (k - (j + 1) * n) = k - j * n := by
        rw [Nat.add_mul, Nat.one_mul] at h₅ ⊢
        omega
      exact coords_mul' hx h₆ (hs i) (hb' (j + 1) i') (hb' j) (hm i j hj i')
    · have hdet : (Matrix.diagonal (fun a => (((u a ^ (k - 0 * n))⁻¹ : Fˣ) : F)) * Pm.map f).det =
          (((∏ a, u a) ^ (-(k : ℤ)) : Fˣ) : F) * f Pm.det := by
        rw [Matrix.det_mul, Matrix.det_diagonal, ← Units.coe_prod, Finset.prod_inv_distrib, Finset.prod_pow,
          RingHom.map_det, Nat.zero_mul, Nat.sub_zero, zpow_neg, zpow_natCast]
        rfl
      have H := torsSq_kosD_mul f m ev
        (fun j => Matrix.of fun a i => valT (T := F) (z' a).left (x'.P.L.U (ch' a)) ((b' j i).f (ch' a)))
        _ t (hdet ▸ mul_ne_zero (Units.ne_zero _) hdl) (by
          rw [Matrix.mul_assoc, ← Matrix.map_mul, ← h₁]
          ext a i
          rw [Matrix.diagonal_mul]
          refine ((Units.eq_inv_mul_iff_mul_eq _).2 ?_)
          exact (_root_.mul_comm _ _).trans ((congrArg _ (Units.val_pow_eq_pow_val _ _)).trans
            (hval a _ (b 0 i) (b' 0 i) (hb' 0 i)))) h₂ h₃
      have e₁ : (∏ a, u a) ^ (-2 * (k : ℤ)) = ((∏ a, u a) ^ (-(k : ℤ))) ^ 2 := by group
      rw [hdet, mul_pow, ← _root_.mul_assoc] at H
      rw [e₁]
      exact H
    · change f _ = f e * f Pm.det ^ 2
      rw [← h₄, map_mul, map_pow, _root_.mul_comm]
  obtain ⟨c, lam, t, e, dl, hc, hct, hJ⟩ := key l (Or.inl rfl) hadm.2.1
  obtain ⟨c₂, lam₂, t₂, e₂, dl₂, hc₂, hct₂, hJ₂⟩ := key l' (Or.inr rfl) (hadm.2.1.trans hadm.2.2.1)
  have hdl : dl₂ ^ 2 = Units.map f.toMonoidHom (e₂⁻¹ * e) * dl ^ 2 := by
    rw [map_mul, map_inv, _root_.mul_assoc, ← hJ, hJ₂, inv_mul_cancel_left]
  refine ⟨kaForm x.P.g n l l' t (t₂ * (e₂⁻¹ * e)) lam lam₂ e, z', ch', c, c₂, _, _,
    Units.map f.toMonoidHom e * (∏ a, u a) ^ (-((x.P.g * n : ℕ) : ℤ)) * dl ^ 2, _, _, E, ?_, hc, hc₂, hct, hct₂, ?_⟩
  · rw [mul_right_comm, ← hJ, zpow_neg, zpow_natCast, Units.val_mul, eq_comm, Units.eq_mul_inv_iff_mul_eq,
      Units.val_pow_eq_pow_val, Units.coe_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact (Finset.prod_congr rfl fun a _ => hjac a).trans (map_prod f _ _).symm
  · have H := kaForm_homogeneous F x.P.g n l l' (Units.map f.toMonoidHom t) (Units.map f.toMonoidHom (t₂ * (e₂⁻¹ * e)))
      (Units.map f.toMonoidHom e) (∏ a, u a) 1 dl (fun j => Units.map f.toMonoidHom (lam j))
      (fun j => Units.map f.toMonoidHom (lam₂ j)) (fun _ => 1) (fun _ => 1) hadm.2.1 hadm.2.2.1
    simp only [one_zpow, one_pow, _root_.mul_one, Finset.prod_const_one] at H
    refine (kaForm_map' _ _ _ _ _ _ _ _ _ _).trans (H.symm.trans ?_)
    congr 1
    rw [hdl, map_mul _ t₂]
    ac_rfl

/- English proof (translation)
Introduce `laws O _ _ _ _ F _ f x xF φ w n l l' al hg s sF κ a e hf hadm hx hs hfin hκ ha _`. Establish `hκ'` using `hκ`. Take `⟨z, ch, b, b₂, -, -, -, lam, lam₂, E, -, hb, hb₂, -⟩` from `hκ'`. Establish `h₀ : ∀ k j : ℕ, ∃ S : Set (Pt xF), S.Finite ∧ (k = l ∨ k = l' → j ≤ xF.P.g → ∃ ξ : (Fin 4 → Fin ((k - j * n) ^ xF.P.g)) → Fin 4 → Pt xF, (∀ I r, ξ I r ∈ S) ∧ Function.Injective ξ ∧ ∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al (k - j * n) r c).prod = 1)` using `fun k j => by`. Distinguish the cases in `h : (k = l ∨ k = l') ∧ j ≤ xF.P.g`.

Choose the witnesses or unpack the hypotheses as in `⟨c, la, ξ, -, -, -, -, h₁, h₂, -⟩ : ∃ c la, IsSquareDeterminantComparison xF (k - j * n) (al (k - j * n)) c la := by`. Break down `h.1 with rfl | rfl` into its components or cases. Use `exacts [⟨_, _, (hb j h.2).2⟩, ⟨_, _, (hb₂ j h.2).2⟩]`. Use `⟨Set.range fun p : _ × _ => ξ p.1 p.2, Set.finite_range _, fun _ _ => ⟨ξ, fun I r => ⟨(I, r), rfl⟩, fun I I' hI => ?_, h₂⟩⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Take `⟨r, hr⟩` from `h₁ I I' hne (IsLocalRing.closedPoint F)`. Conclude with `hr (by rw [hI])`. Conclude with `⟨∅, Set.finite_empty, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩`. Use `choose S hS hS' using h₀`. Set `A : Set (Pt xF)` to `Set.range z ∪ ⋃ j ∈ Set.Iic xF.P.g, (S l j ∪ S l' j)`.

Use `haveI : Finite A := ((Set.finite_range z).union ((Set.finite_Iic _).biUnion fun j _ => (hS l j).union (hS l' j))).to_subtype`. Use `haveI := x.P.isAb.proper`. Establish `hp : IsPullback φ xF.P.A.hom x.P.A.hom (spMap f)` using `hx.choose_spec.choose_spec.choose_spec.1.1`. Take `⟨O', _, _, _, _, j, Ω, _, i, g, hj, hgi, hsq, hq⟩` from `exists_points_extension f hf x.P.A.hom (fun p : A => p.1.left ≫ φ) (fun p => by`. Rewrite using `[Category.assoc, hp.w, ← Category.assoc, Over.w]`.

Conclude with `Category.id_comp _)`. Take `⟨x', hx'⟩` from `KeyPow.keyIn_baseChange laws.polBaseChange O O' x j`. Take `⟨φ', w', H'⟩` from `(KeyVia.main _ _ x x' j).1.1 hx'`. Establish `hg' : x'.P.g = x.P.g` using `H'.choose_spec.choose`. Establish `hp' : IsPullback φ' x'.P.A.hom x.P.A.hom (spMap j)` using `H'.choose_spec.choose_spec.choose_spec.1.1`.

Use `choose s' hs' using fun i : Fin x'.P.g => (((KeyVia.main _ _ x x' j).2 φ' w' H').1 n (s (i.cast hg'))).exists`. Take `⟨y, hy⟩` from `KeyPow.keyIn_baseChange laws.polBaseChange F Ω xF i`. Take `⟨ψ, v, H₁⟩` from `(KeyVia.main _ _ xF y i).1.1 hy`. Establish `hg₁ : y.P.g = xF.P.g` using `H₁.choose_spec.choose`. Use `choose s₁ hs₁ using fun a : Fin y.P.g => (((KeyVia.main _ _ xF y i).2 ψ v H₁).1 n (sF (a.cast hg₁))).exists`.

Take `⟨v₂, H₂, sec₂⟩` from `keyVia_trans hx H₁`. Take `⟨χ, v₃, H₃, hχ, sec₃⟩` from `KaLift.keyVia_cancel (f' := g) H' (hsq.symm ▸ H₂)`. Establish `hg₃ : y.P.g = x'.P.g` using `(hg₁.trans hg).trans hg'.symm`. Take `⟨u₁, hu₁, hu₁'⟩` from `exists_pull_hom H₁ i.injective`. Take `⟨u₃, hu₃, hu₃'⟩` from `exists_pull_hom H₃ hgi`.

Establish `hA : ∀ p ∈ A, ∃ q, u₃ q = u₁ p` using `fun p hpA => by`. Take `⟨q, e₁, e₂⟩` from `hq ⟨p, hpA⟩`. Establish `hw : q ≫ x.P.A.hom = 𝟙 _ ≫ spMap j` using `e₁.trans (Category.id_comp _).symm`. Set `q' : Pt x'` to `Over.homMk (hp'.lift q (𝟙 _) hw) (hp'.lift_snd _ _ _)`. Establish `e₃ : q'.left ≫ φ' = q` using `hp'.lift_fst _ _ _`.

Establish `e₄ : q'.left ≫ x'.P.A.hom = 𝟙 _` using `Over.w _`. Establish `e₅ : (u₁ p).left ≫ y.P.A.hom = 𝟙 _` using `Over.w _`. Establish `hp₃ : IsPullback χ y.P.A.hom x'.P.A.hom (spMap g)` using `H₃.choose_spec.choose_spec.choose_spec.1.1`. Use `⟨q', ((hu₃' q' _).2 (hp'.hom_ext ?_ ?_)).symm⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hχ, e₃, e₂, ← Category.assoc, (hu₁' p _).1 rfl, Category.assoc]`.

Rewrite using `[Category.assoc, Category.assoc, e₄, hp₃.w, ← Category.assoc, e₅]`. Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`. Use `choose z' hz' using fun a => hA (z a) (Or.inl ⟨a, rfl⟩)`. Take `⟨ch₁, E₁⟩` from `etZ_pull hg₁ H₁ hs₁ (z' := fun a => u₁ (z a)) (fun a => (hu₁' _ _).1 rfl) E`. Establish `hO : ∀ m : ℕ, 1 ≤ m → IsUnit (m : O')` using `fun m hm => by`.

Use `(isUnit_iff_ne_zero.2 (by exact_mod_cast (by omega : m ≠ 0) : (m : ℚ) ≠ 0)).map (j.comp (algebraMap ℚ O))` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Use `haveI : CharZero Ω := (RingHom.charZero_iff ((i.comp f).comp (algebraMap ℚ O)).injective).1 inferInstance`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : O'ˣ, KaVal y n l l' al s₁ (Units.map g.toMonoidHom u) := by`. Use `exists_unit_kaVal laws hg₃ (s := s') (s' := s₁) (by rw [hg₁]) z' hO hgi (hg'.symm ▸ hadm) H₃ (fun a => sec₃ n _ _ _ (hs' (a.cast hg₃)) (sec₂ n _ _ _ (hs (a.cast hg₁)) (hs₁ a))) ?_ E₁ (fun a => (hu₃' _ _).1 (hz' a).symm) ?_` and prove the remaining obligations.

Establish `hcl : IsClosed {t : x.P.A.left | x.P.A.hom t = IsLocalRing.closedPoint O ∧ ∀ a, t ∉ Out.nonzeroLocus (s a)}`. Use `IsClosed.inter ((IsLocalRing.isClosed_singleton_closedPoint O).preimage x.P.A.hom.continuous) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IsClosed {t : x.P.A.left | ∀ a, t ∉ Out.nonzeroLocus (s a)}`. Rewrite using `[Set.setOf_forall]`. Conclude with `isClosed_iInter fun a => (Out.nonzeroLocus (s a)).isOpen.isClosed_compl`.

Use `(finite_preimage_fibre hp' hcl hfin (IsLocalRing.closedPoint O')).subset fun t ht => ⟨ht.1, ?_, fun a h => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg (fun q => q t) hp'.w).trans ((congrArg (spMap j) ht.1).trans (IsLocalRing.comap_closedPoint j))`. Conclude with `ht.2 (a.cast hg'.symm) (EtBaseChange.mem_nonzeroLocus_via (hs' (a.cast hg'.symm)) t h)`. Introduce `k hk c hc`. Rewrite `hc`, the goal using `[hg'.trans hg.symm]`.

Take `⟨ξ, h₁, h₂, h₃⟩` from `hS' k c hk hc`. Use `choose ξ' hξ' using fun I r => hA (ξ I r) (Or.inr (Set.mem_biUnion hc (by`. Break down `hk with rfl | rfl` into its components or cases. Use `exacts [Or.inl (h₁ I r), Or.inr (h₁ I r)])))`. Use `⟨ξ', fun I I' h => h₂ (funext fun r => hu₁ ?_), fun I r => hu₃ ?_⟩` and prove the remaining obligations.

Rewrite using `[← hξ', ← hξ', h]`. Use `congrArg u₁ (h₃ I r)` as an intermediate fact. Simplify using `only [map_list_prod, List.map_ofFn, Function.comp_def, map_zpow, map_one, hξ'] at this ⊢`. Conclude with `this`. Establish `h₁` using `T.keyInvariant_baseChange laws F Ω xF y i ψ v n l l' al hg₁ sF s₁ κ (hg.symm ▸ hadm) H₁ hs₁ hκ`.

Establish `h₂ : i κ = g u` using `congrArg Units.val (T.keyInvariantFromIntersection_unique laws Ω y n l l' al s₁ _ _ ((hg₁.trans hg).symm ▸ hadm) h₁ hu)`. Establish `h₃ : g (j a) = g (u ^ e : O'ˣ)`. Use `(RingHom.congr_fun hsq a).trans ?_` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, ← ha, map_zpow₀, h₂]`. Conclude with `((congrArg Units.val (map_zpow (Units.map g.toMonoidHom) u e)).trans (Units.val_zpow_eq_zpow_val _ _)).symm`.

Conclude with `(isUnit_map_iff j a).1 (hgi h₃ ▸ Units.isUnit _)`.
-/
theorem isUnit_of_finite_zeros : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℚ O] (F : Type) [Field F] (f : O →+* F) (x : KeyIn O) (xF : KeyIn F) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (hg : xF.P.g = x.P.g) (s : Fin x.P.g → RR x n) (sF : Fin xF.P.g → RR xF n) (κ : Fˣ) (a : O) (e : ℤ), Function.Injective f → admitted x.P.g n l l' al → KeyVia xF x f φ w → (∀ i, SecVia xF x φ w (sF i) (s (i.cast hg))) → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → KaVal xF n l l' al sF κ → (κ : F) ^ e = f a → e ≠ 0 → IsUnit a := by
  intro laws O _ _ _ _ F _ f x xF φ w n l l' al hg s sF κ a e hf hadm hx hs hfin hκ ha _
  have hκ' := hκ
  obtain ⟨z, ch, b, b₂, -, -, -, lam, lam₂, E, -, hb, hb₂, -⟩ := hκ'
  have h₀ : ∀ k j : ℕ, ∃ S : Set (Pt xF), S.Finite ∧ (k = l ∨ k = l' → j ≤ xF.P.g →
      ∃ ξ : (Fin 4 → Fin ((k - j * n) ^ xF.P.g)) → Fin 4 → Pt xF, (∀ I r, ξ I r ∈ S) ∧
        Function.Injective ξ ∧ ∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al (k - j * n) r c).prod = 1) := fun k j => by
    by_cases h : (k = l ∨ k = l') ∧ j ≤ xF.P.g
    · obtain ⟨c, la, ξ, -, -, -, -, h₁, h₂, -⟩ : ∃ c la, IsSquareDeterminantComparison xF (k - j * n) (al (k - j * n)) c la := by
        rcases h.1 with rfl | rfl
        exacts [⟨_, _, (hb j h.2).2⟩, ⟨_, _, (hb₂ j h.2).2⟩]
      refine ⟨Set.range fun p : _ × _ => ξ p.1 p.2, Set.finite_range _, fun _ _ => ⟨ξ, fun I r => ⟨(I, r), rfl⟩,
        fun I I' hI => ?_, h₂⟩⟩
      by_contra hne
      obtain ⟨r, hr⟩ := h₁ I I' hne (IsLocalRing.closedPoint F)
      exact hr (by rw [hI])
    · exact ⟨∅, Set.finite_empty, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose S hS hS' using h₀
  let A : Set (Pt xF) := Set.range z ∪ ⋃ j ∈ Set.Iic xF.P.g, (S l j ∪ S l' j)
  haveI : Finite A := ((Set.finite_range z).union
    ((Set.finite_Iic _).biUnion fun j _ => (hS l j).union (hS l' j))).to_subtype
  haveI := x.P.isAb.proper
  have hp : IsPullback φ xF.P.A.hom x.P.A.hom (spMap f) := hx.choose_spec.choose_spec.choose_spec.1.1
  obtain ⟨O', _, _, _, _, j, Ω, _, i, g, hj, hgi, hsq, hq⟩ := exists_points_extension f hf x.P.A.hom
    (fun p : A => p.1.left ≫ φ) (fun p => by
      rw [Category.assoc, hp.w, ← Category.assoc, Over.w]
      exact Category.id_comp _)
  obtain ⟨x', hx'⟩ := KeyPow.keyIn_baseChange laws.polBaseChange O O' x j
  obtain ⟨φ', w', H'⟩ := (KeyVia.main _ _ x x' j).1.1 hx'
  have hg' : x'.P.g = x.P.g := H'.choose_spec.choose
  have hp' : IsPullback φ' x'.P.A.hom x.P.A.hom (spMap j) := H'.choose_spec.choose_spec.choose_spec.1.1
  choose s' hs' using fun i : Fin x'.P.g => (((KeyVia.main _ _ x x' j).2 φ' w' H').1 n (s (i.cast hg'))).exists
  obtain ⟨y, hy⟩ := KeyPow.keyIn_baseChange laws.polBaseChange F Ω xF i
  obtain ⟨ψ, v, H₁⟩ := (KeyVia.main _ _ xF y i).1.1 hy
  have hg₁ : y.P.g = xF.P.g := H₁.choose_spec.choose
  choose s₁ hs₁ using fun a : Fin y.P.g => (((KeyVia.main _ _ xF y i).2 ψ v H₁).1 n (sF (a.cast hg₁))).exists
  obtain ⟨v₂, H₂, sec₂⟩ := keyVia_trans hx H₁
  obtain ⟨χ, v₃, H₃, hχ, sec₃⟩ := KaLift.keyVia_cancel (f' := g) H' (hsq.symm ▸ H₂)
  have hg₃ : y.P.g = x'.P.g := (hg₁.trans hg).trans hg'.symm
  obtain ⟨u₁, hu₁, hu₁'⟩ := exists_pull_hom H₁ i.injective
  obtain ⟨u₃, hu₃, hu₃'⟩ := exists_pull_hom H₃ hgi
  have hA : ∀ p ∈ A, ∃ q, u₃ q = u₁ p := fun p hpA => by
    obtain ⟨q, e₁, e₂⟩ := hq ⟨p, hpA⟩
    have hw : q ≫ x.P.A.hom = 𝟙 _ ≫ spMap j := e₁.trans (Category.id_comp _).symm
    let q' : Pt x' := Over.homMk (hp'.lift q (𝟙 _) hw) (hp'.lift_snd _ _ _)
    have e₃ : q'.left ≫ φ' = q := hp'.lift_fst _ _ _
    have e₄ : q'.left ≫ x'.P.A.hom = 𝟙 _ := Over.w _
    have e₅ : (u₁ p).left ≫ y.P.A.hom = 𝟙 _ := Over.w _
    have hp₃ : IsPullback χ y.P.A.hom x'.P.A.hom (spMap g) := H₃.choose_spec.choose_spec.choose_spec.1.1
    refine ⟨q', ((hu₃' q' _).2 (hp'.hom_ext ?_ ?_)).symm⟩
    · rw [Category.assoc, Category.assoc, hχ, e₃, e₂, ← Category.assoc, (hu₁' p _).1 rfl, Category.assoc]
    · rw [Category.assoc, Category.assoc, e₄, hp₃.w, ← Category.assoc, e₅]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  choose z' hz' using fun a => hA (z a) (Or.inl ⟨a, rfl⟩)
  obtain ⟨ch₁, E₁⟩ := etZ_pull hg₁ H₁ hs₁ (z' := fun a => u₁ (z a)) (fun a => (hu₁' _ _).1 rfl) E
  have hO : ∀ m : ℕ, 1 ≤ m → IsUnit (m : O') := fun m hm => by
    have := (isUnit_iff_ne_zero.2 (by exact_mod_cast (by omega : m ≠ 0) : (m : ℚ) ≠ 0)).map (j.comp (algebraMap ℚ O))
    rwa [map_natCast] at this
  haveI : CharZero Ω := (RingHom.charZero_iff ((i.comp f).comp (algebraMap ℚ O)).injective).1 inferInstance
  obtain ⟨u, hu⟩ : ∃ u : O'ˣ, KaVal y n l l' al s₁ (Units.map g.toMonoidHom u) := by
    refine exists_unit_kaVal laws hg₃ (s := s') (s' := s₁) (by rw [hg₁]) z' hO hgi (hg'.symm ▸ hadm) H₃
      (fun a => sec₃ n _ _ _ (hs' (a.cast hg₃)) (sec₂ n _ _ _ (hs (a.cast hg₁)) (hs₁ a))) ?_ E₁
      (fun a => (hu₃' _ _).1 (hz' a).symm) ?_
    · have hcl : IsClosed {t : x.P.A.left | x.P.A.hom t = IsLocalRing.closedPoint O ∧ ∀ a, t ∉ Out.nonzeroLocus (s a)} := by
        refine IsClosed.inter ((IsLocalRing.isClosed_singleton_closedPoint O).preimage x.P.A.hom.continuous) ?_
        change IsClosed {t : x.P.A.left | ∀ a, t ∉ Out.nonzeroLocus (s a)}
        rw [Set.setOf_forall]
        exact isClosed_iInter fun a => (Out.nonzeroLocus (s a)).isOpen.isClosed_compl
      refine (finite_preimage_fibre hp' hcl hfin (IsLocalRing.closedPoint O')).subset fun t ht => ⟨ht.1, ?_, fun a h => ?_⟩
      · exact (congrArg (fun q => q t) hp'.w).trans ((congrArg (spMap j) ht.1).trans (IsLocalRing.comap_closedPoint j))
      · exact ht.2 (a.cast hg'.symm) (EtBaseChange.mem_nonzeroLocus_via (hs' (a.cast hg'.symm)) t h)
    · intro k hk c hc
      rw [hg'.trans hg.symm] at hc ⊢
      obtain ⟨ξ, h₁, h₂, h₃⟩ := hS' k c hk hc
      choose ξ' hξ' using fun I r => hA (ξ I r) (Or.inr (Set.mem_biUnion hc (by
        rcases hk with rfl | rfl
        exacts [Or.inl (h₁ I r), Or.inr (h₁ I r)])))
      refine ⟨ξ', fun I I' h => h₂ (funext fun r => hu₁ ?_), fun I r => hu₃ ?_⟩
      · rw [← hξ', ← hξ', h]
      · have := congrArg u₁ (h₃ I r)
        simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_zpow, map_one, hξ'] at this ⊢
        exact this
  have h₁ := T.keyInvariant_baseChange laws F Ω xF y i ψ v n l l' al hg₁ sF s₁ κ (hg.symm ▸ hadm) H₁ hs₁ hκ
  have h₂ : i κ = g u := congrArg Units.val
    (T.keyInvariantFromIntersection_unique laws Ω y n l l' al s₁ _ _ ((hg₁.trans hg).symm ▸ hadm) h₁ hu)
  have h₃ : g (j a) = g (u ^ e : O'ˣ) := by
    refine (RingHom.congr_fun hsq a).trans ?_
    rw [RingHom.comp_apply, ← ha, map_zpow₀, h₂]
    exact ((congrArg Units.val (map_zpow (Units.map g.toMonoidHom) u e)).trans (Units.val_zpow_eq_zpow_val _ _)).symm
  exact (isUnit_map_iff j a).1 (hgi h₃ ▸ Units.isUnit _)

end GlobalTheory.KaFiniteUnit
end
