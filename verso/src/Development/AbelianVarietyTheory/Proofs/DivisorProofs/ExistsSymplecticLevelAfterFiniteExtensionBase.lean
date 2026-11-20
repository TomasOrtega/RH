import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelAfterExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinExtIntegralClosure
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSymmetryHypothesisBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemGenusOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumLevel

/- English proof (translation)
Set `Ω` to `AlgebraicClosure K'`. Use `haveI : CharZero K' := (algebraMap K K').charZero_iff (algebraMap K K').injective |>.1 inferInstance`. Use `haveI : CharZero Ω := (algebraMap K' Ω).charZero_iff (algebraMap K' Ω).injective |>.1 inferInstance`. Use `haveI : NeZero m := ⟨by omega⟩`. Take `⟨ζ₀, hζ₀⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω m`.

Set `K'' : IntermediateField K' Ω` to `IntermediateField.adjoin K' {ζ₀}`. Use `haveI : FiniteDimensional K' K'' := IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K') ζ₀)`. Use `haveI : FiniteDimensional K K'' := Module.Finite.trans K' K''`. Use `haveI : IsScalarTower K K'' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `E` to `IntermediateField.normalClosure K K'' Ω`.

Use `haveI : IsGalois K E := inferInstance`. Use `haveI : FiniteDimensional K E := inferInstance`. Set `t : K'' →ₐ[K] E` to `(IsScalarTower.toAlgHom K K'' Ω).codRestrict _ fun y => AlgHom.fieldRange_le_normalClosure _ ⟨y, rfl⟩`. Establish `hz : ζ₀ ∈ K''` using `IntermediateField.mem_adjoin_simple_self K' ζ₀`. Use `⟨E, inferInstance, inferInstance, inferInstance, inferInstance, t.comp (IsScalarTower.toAlgHom K K' K''), t ⟨ζ₀, hz⟩, ?_⟩` and prove the remaining obligations.

Conclude with `IsPrimitiveRoot.of_map_of_injective (f := E.val) (by exact hζ₀) Subtype.val_injective`.
-/
theorem exists_galois_root (K K' : Type) [Field K] [CharZero K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E) (_ : IsGalois K E) (j : K' →ₐ[K] E) (ζ : E),
      IsPrimitiveRoot ζ m := by
  let Ω := AlgebraicClosure K'
  haveI : CharZero K' := (algebraMap K K').charZero_iff (algebraMap K K').injective |>.1 inferInstance
  haveI : CharZero Ω := (algebraMap K' Ω).charZero_iff (algebraMap K' Ω).injective |>.1 inferInstance
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  let K'' : IntermediateField K' Ω := IntermediateField.adjoin K' {ζ₀}
  haveI : FiniteDimensional K' K'' :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K') ζ₀)
  haveI : FiniteDimensional K K'' := Module.Finite.trans K' K''
  haveI : IsScalarTower K K'' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let E := IntermediateField.normalClosure K K'' Ω
  haveI : IsGalois K E := inferInstance
  haveI : FiniteDimensional K E := inferInstance
  let t : K'' →ₐ[K] E := (IsScalarTower.toAlgHom K K'' Ω).codRestrict _
    fun y => AlgHom.fieldRange_le_normalClosure _ ⟨y, rfl⟩
  have hz : ζ₀ ∈ K'' := IntermediateField.mem_adjoin_simple_self K' ζ₀
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, t.comp (IsScalarTower.toAlgHom K K' K''),
    t ⟨ζ₀, hz⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := E.val) (by exact hζ₀) Subtype.val_injective

end GlobalTheory.MumLevel

namespace GlobalTheory.MumLevel

def half (g : ℕ) (i : Fin (2 * g)) : Fin g ⊕ Fin g :=
  if h : (i : ℕ) < g then .inl ⟨i, h⟩ else .inr ⟨(i : ℕ) - g, by omega⟩

/- English proof (translation)
The claim follows from `| .inl p, .inr q => if p = q then 1 else 0 | .inr p, .inl q => if p = q then -1 else 0 | _, _ => 0 := by rcases a with p | p <;> rcases b with q | q <;> simp [omegaStd, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm] <;> split_ifs <;> simp`.
-/
theorem omegaStd_single (g : ℕ) (a b : Fin g ⊕ Fin g) :
    omegaStd (Pi.single a (1 : ℤ)) (Pi.single b 1) =
      match a, b with
      | .inl p, .inr q => if p = q then 1 else 0
      | .inr p, .inl q => if p = q then -1 else 0
      | _, _ => 0 := by
  rcases a with p | p <;> rcases b with q | q <;>
    simp [omegaStd, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm] <;> split_ifs <;> simp

/- English proof (translation)
Rewrite using `[omegaStd_single]`. Unfold `half stdSymp`. Apply the tactic sequence `by_cases hi : (i : ℕ) < g <;> by_cases hj : (j : ℕ) < g <;> simp only [hi, hj, dif_pos, dif_neg, not_false_eq_true, true_and, false_and, if_false]`. Apply the tactic sequence `all_goals (try simp only [Fin.ext_iff, Fin.val_mk])`. Apply the tactic sequence `all_goals (have := i.2; have := j.2; split_ifs <;> omega)`.
-/
theorem stdSymp_eq (g : ℕ) (i j : Fin (2 * g)) :
    stdSymp g i j = omegaStd (Pi.single (half g i) (1 : ℤ)) (Pi.single (half g j) 1) := by
  rw [omegaStd_single]
  unfold half stdSymp
  by_cases hi : (i : ℕ) < g <;> by_cases hj : (j : ℕ) < g <;> simp only [hi, hj, dif_pos, dif_neg, not_false_eq_true, true_and, false_and, if_false]
  all_goals (try simp only [Fin.ext_iff, Fin.val_mk])
  all_goals (have := i.2; have := j.2; split_ifs <;> omega)

end GlobalTheory.MumLevel

namespace GlobalTheory.MumLevel

/- English proof (translation)
Use `letI : Algebra R E := (GalClosure.baseMap R E).toAlgebra`. Use `haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl`. Take `⟨hloc, hfe⟩` from `GalClosure.finExt_integralClosure (E := E) hR`. Use `set R₁ := integralClosure R E`. Use `haveI : IsFractionRing R₁ E := integralClosure.isFractionRing_of_finite_extension (FractionRing R) E`.

Set `e : E ≃+* FractionRing R₁` to `(FractionRing.algEquiv R₁ E).symm.toRingEquiv`. Establish `he : ∀ x : R₁, e (algebraMap R₁ E x) = algebraMap R₁ _ x` using `fun x => (FractionRing.algEquiv R₁ E).symm.commutes x`. Establish `hint : IsIntegral R ζ`. Use `⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩` and prove the remaining obligations. Simplify using `[hζ.pow_eq_one]`.

Set `z : R₁` to `⟨ζ, hint⟩`. Establish `hz : z ^ m = 1` using `Subtype.ext (by simp [z, hζ.pow_eq_one])`. Set `ζ₁ : R₁ˣ` to `Units.ofPowEqOne z m hz (by omega)`. Establish `hζ₁ : (ζ₁ : R₁) = z` using `Units.val_ofPowEqOne _ _ _ _`. Use `⟨R₁, inferInstance, inferInstance, hloc, algebraMap R R₁, e, ζ₁, hfe, fun r => ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← he]`. Both sides reduce to the same expression. Rewrite using `[hζ₁, ← he]`. Both sides reduce to the same expression. Use `IsPrimitiveRoot.coe_units_iff.1 ?_` and prove the remaining obligations.

Rewrite using `[hζ₁]`. Conclude with `IsPrimitiveRoot.of_map_of_injective (f := algebraMap R₁ E) (by exact hζ) Subtype.val_injective`.
-/
theorem exists_ring (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (E : Type) [Field E]
    [Algebra (FractionRing R) E] [FiniteDimensional (FractionRing R) E] [IsGalois (FractionRing R) E] (ζ : E) (m : ℕ)
    (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ m) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (e : E ≃+* FractionRing R₁)
      (ζ₁ : R₁ˣ), FinExt ρ ∧ (∀ r, e (algebraMap (FractionRing R) E (algebraMap R _ r)) = algebraMap R₁ _ (ρ r)) ∧
      e ζ = algebraMap R₁ _ ζ₁ ∧ IsPrimitiveRoot ζ₁ m := by
  letI : Algebra R E := (GalClosure.baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hloc, hfe⟩ := GalClosure.finExt_integralClosure (E := E) hR
  set R₁ := integralClosure R E
  haveI : IsFractionRing R₁ E := integralClosure.isFractionRing_of_finite_extension (FractionRing R) E
  let e : E ≃+* FractionRing R₁ := (FractionRing.algEquiv R₁ E).symm.toRingEquiv
  have he : ∀ x : R₁, e (algebraMap R₁ E x) = algebraMap R₁ _ x := fun x => (FractionRing.algEquiv R₁ E).symm.commutes x
  have hint : IsIntegral R ζ := by
    refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
    simp [hζ.pow_eq_one]
  let z : R₁ := ⟨ζ, hint⟩
  have hz : z ^ m = 1 := Subtype.ext (by simp [z, hζ.pow_eq_one])
  let ζ₁ : R₁ˣ := Units.ofPowEqOne z m hz (by omega)
  have hζ₁ : (ζ₁ : R₁) = z := Units.val_ofPowEqOne _ _ _ _
  refine ⟨R₁, inferInstance, inferInstance, hloc, algebraMap R R₁, e, ζ₁, hfe, fun r => ?_, ?_, ?_⟩
  · rw [← he]; rfl
  · rw [hζ₁, ← he]; rfl
  · refine IsPrimitiveRoot.coe_units_iff.1 ?_
    rw [hζ₁]
    exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap R₁ E) (by exact hζ) Subtype.val_injective

end GlobalTheory.MumLevel

namespace GlobalTheory.MumLevel

/- English proof (translation)
Introduce `R _ _ _ hR A hS m hm _`. Use `haveI : CharZero R := hR.2`. Take `⟨K', _, _, hfin, H⟩` from `LevelAfterExt.exists_ext_level (FractionRing R) A m hm`. Use `haveI : FiniteDimensional (FractionRing R) K' := hfin`. Take `⟨E, _, _, _, _, j, ζ, hζ⟩` from `exists_galois_root (FractionRing R) K' m hm`.

Take `⟨R₁, _, _, _, ρ, e, ζ₁, hρ, he, -, hζ₁⟩` from `exists_ring R hR E ζ m hm hζ`. Set `f : FractionRing R →+* FractionRing R₁` to `ArcPull.fracMap hρ.2.1`. Set `i : K' →+* FractionRing R₁` to `e.toRingHom.comp j.toRingHom`. Establish `hf : i.comp (algebraMap (FractionRing R) K') = f`. Use `IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)` and prove the remaining obligations.

Simplify using `only [RingHom.comp_apply]`. Use `show e (j (algebraMap _ K' _)) = _`. Rewrite using `[j.commutes, he, ArcPull.fracMap_algebraMap]`. Use `haveI : CharZero (FractionRing R₁) := f.charZero_iff f.injective |>.1 inferInstance`. Take `⟨A₁, ψ, hA⟩` from `exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 f A`.

Set `ze : (FractionRing R₁)ˣ` to `Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ₁`. Establish `hze : IsPrimitiveRoot (ze : FractionRing R₁) m` using `IsPrimitiveRoot.coe_units_iff.2 (hζ₁.map_of_injective (Units.map_injective (IsFractionRing.injective R₁ _)))`. Take `⟨lev, -, h₂, h₃⟩` from `H (FractionRing R₁) i f hf A₁ ψ hA A₁.g rfl ze hze`. Establish `hL` using `GlobalTheory.lawsAndExpansions.1.1`. Use `A₁.isAb.comm` as an intermediate fact.

Establish `hM : (m : FractionRing R₁) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Set `ek` to `(Scheme.ΓSpecIso (CommRingCat.of (FractionRing R₁))).commRingCatIsoToRingEquiv.symm`. Take `⟨L, -⟩` from `exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ A₁ m (unitOn ze) (ZH.RealDimOne.isPrimitiveRoot_unitOn (IsPrimitiveRoot.coe_units_iff.1 hze)) (fun F _ s => by`. Establish `: Nontrivial Γ(Sp F, ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm.injective.nontrivial`. Use `⟨fun e₀ => hM ?_, (ZH.RealDimOne.isPrimitiveRoot_unitOn (IsPrimitiveRoot.coe_units_iff.1 hze)).map_of_injective (Units.map_injective fun a b hab => ek.symm.injective ((s.appTop.hom.comp ek.toRingHom).injective (by simpa using hab)))⟩` and prove the remaining obligations.

Use `(s.appTop.hom.comp ek.toRingHom).injective ?_` and prove the remaining obligations. Use `(Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective ?_` and prove the remaining obligations. Rewrite using `[map_natCast, map_natCast, map_zero, map_zero]`. Conclude with `e₀)`. Use the proof step `(fun k => lev (Pi.single (half A₁.g k) 1)) (fun k => h₂ _) (fun k l => by`.

Rewrite using `[stdSymp_eq, ← ZH.RealDimOne.unitOn_zpow]`. Conclude with `h₃ _ _)`. Use `⟨R₁, inferInstance, inferInstance, inferInstance, ρ, A₁, ψ, ζ₁, L, hρ, ⟨f, fun r => ArcPull.fracMap_algebraMap hρ.2.1 r, hA.2.1, hA.2.2.symm⟩, hA.1, ?_⟩` and prove the remaining obligations. Use `A.isAb.comm` as an intermediate fact. Conclude with `SymBaseChange.hypS_baseChange _ _ _ _ _ ψ _ _ A.isLB A₁.isLB hA.2.1 hA.2.2.symm hS`.
-/
theorem exists_level_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∀ m : ℕ, 1 ≤ m → IsUnit (m : R) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (ζ : R₁ˣ) (_ : ReciprocityTheory.ChartRestriction.G.Out.Level A₁ m (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ))), FinExt ρ ∧ IsFib ρ A A₁ a ∧ A₁.g = A.g ∧ (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) := by
  intro R _ _ _ hR A hS m hm _
  haveI : CharZero R := hR.2
  obtain ⟨K', _, _, hfin, H⟩ := LevelAfterExt.exists_ext_level (FractionRing R) A m hm
  haveI : FiniteDimensional (FractionRing R) K' := hfin
  obtain ⟨E, _, _, _, _, j, ζ, hζ⟩ := exists_galois_root (FractionRing R) K' m hm
  obtain ⟨R₁, _, _, _, ρ, e, ζ₁, hρ, he, -, hζ₁⟩ := exists_ring R hR E ζ m hm hζ
  let f : FractionRing R →+* FractionRing R₁ := ArcPull.fracMap hρ.2.1
  let i : K' →+* FractionRing R₁ := e.toRingHom.comp j.toRingHom
  have hf : i.comp (algebraMap (FractionRing R) K') = f := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply]
    show e (j (algebraMap _ K' _)) = _
    rw [j.commutes, he, ArcPull.fracMap_algebraMap]
  haveI : CharZero (FractionRing R₁) := f.charZero_iff f.injective |>.1 inferInstance
  obtain ⟨A₁, ψ, hA⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 f A
  let ze : (FractionRing R₁)ˣ := Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ₁
  have hze : IsPrimitiveRoot (ze : FractionRing R₁) m :=
    IsPrimitiveRoot.coe_units_iff.2 (hζ₁.map_of_injective (Units.map_injective (IsFractionRing.injective R₁ _)))
  obtain ⟨lev, -, h₂, h₃⟩ := H (FractionRing R₁) i f hf A₁ ψ hA A₁.g rfl ze hze
  have hL := GlobalTheory.lawsAndExpansions.1.1
  have := A₁.isAb.comm
  have hM : (m : FractionRing R₁) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let ek := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R₁))).commRingCatIsoToRingEquiv.symm
  obtain ⟨L, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ A₁ m (unitOn ze)
    (ZH.RealDimOne.isPrimitiveRoot_unitOn (IsPrimitiveRoot.coe_units_iff.1 hze)) (fun F _ s => by
      have : Nontrivial Γ(Sp F, ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
      refine ⟨fun e₀ => hM ?_, (ZH.RealDimOne.isPrimitiveRoot_unitOn (IsPrimitiveRoot.coe_units_iff.1 hze)).map_of_injective
        (Units.map_injective fun a b hab => ek.symm.injective ((s.appTop.hom.comp ek.toRingHom).injective (by simpa using hab)))⟩
      refine (s.appTop.hom.comp ek.toRingHom).injective ?_
      refine (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective ?_
      rw [map_natCast, map_natCast, map_zero, map_zero]
      exact e₀)
    (fun k => lev (Pi.single (half A₁.g k) 1)) (fun k => h₂ _) (fun k l => by
      rw [stdSymp_eq, ← ZH.RealDimOne.unitOn_zpow]
      exact h₃ _ _)
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ, A₁, ψ, ζ₁, L, hρ,
    ⟨f, fun r => ArcPull.fracMap_algebraMap hρ.2.1 r, hA.2.1, hA.2.2.symm⟩, hA.1, ?_⟩
  have := A.isAb.comm
  exact SymBaseChange.hypS_baseChange _ _ _ _ _ ψ _ _ A.isLB A₁.isLB hA.2.1 hA.2.2.symm hS

end GlobalTheory.MumLevel
