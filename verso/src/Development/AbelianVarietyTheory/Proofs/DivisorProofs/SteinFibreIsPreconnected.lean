import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfIsDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfProper
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option autoImplicit false

noncomputable section

open IsLocalRing CategoryTheory Limits

namespace GlobalTheory.SteinFibreConn

section Completion

variable {A : Type} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)

/- English proof (translation)
Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one, ← v.valuation_lt_one_iff_mem (K := FractionRing A)]`. Establish `e : Valued.v ((algebraMap A (v.adicCompletionIntegers (FractionRing A)) a : v.adicCompletionIntegers (FractionRing A)) : v.adicCompletion (FractionRing A)) = v.valuation (FractionRing A) (algebraMap A (FractionRing A) a)` using `by first`. Consider the case `exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _`. Consider the case `exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v _`. Consider the case `simp`.

Rewrite using `[e]`. Conclude with `⟨fun h => lt_of_le_of_ne (v.valuation_le_one a) h, ne_of_lt⟩`.
-/
theorem mem_maximalIdeal_iff (a : A) :
    algebraMap A (v.adicCompletionIntegers (FractionRing A)) a ∈
      maximalIdeal (v.adicCompletionIntegers (FractionRing A)) ↔ a ∈ v.asIdeal := by
  rw [mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    ← v.valuation_lt_one_iff_mem (K := FractionRing A)]
  have e : Valued.v ((algebraMap A (v.adicCompletionIntegers (FractionRing A)) a :
      v.adicCompletionIntegers (FractionRing A)) : v.adicCompletion (FractionRing A)) =
      v.valuation (FractionRing A) (algebraMap A (FractionRing A) a) := by
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v _
      | simp
  rw [e]
  exact ⟨fun h => lt_of_le_of_ne (v.valuation_le_one a) h, ne_of_lt⟩

/- English proof (translation)
Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce `x hx`. Take `⟨c, hc⟩` from `(Submodule.mem_torsion_iff x).1 hx`. Establish `hc' : algebraMap A (v.adicCompletionIntegers (FractionRing A)) (c : A) * x = 0`. Rewrite using `[← Algebra.smul_def]`.

Conclude with `hc`. Break down `mul_eq_zero.1 hc' with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h0 : (((algebraMap A (v.adicCompletionIntegers (FractionRing A)) (c : A)) : v.adicCompletionIntegers (FractionRing A)) : v.adicCompletion (FractionRing A)) = 0`. Rewrite using `[h]`.

Both sides reduce to the same expression. Establish `h1 : algebraMap (FractionRing A) (v.adicCompletion (FractionRing A)) (algebraMap A (FractionRing A) (c : A)) = 0` using `h0`. Rewrite `h1` using `[map_eq_zero, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `nonZeroDivisors.coe_ne_zero c h1`. Conclude with `(Submodule.mem_bot _).2 h`.
-/
theorem flat : Module.Flat A (v.adicCompletionIntegers (FractionRing A)) := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff x).1 hx
  have hc' : algebraMap A (v.adicCompletionIntegers (FractionRing A)) (c : A) * x = 0 := by
    rw [← Algebra.smul_def]; exact hc
  rcases mul_eq_zero.1 hc' with h | h
  · exfalso
    have h0 : (((algebraMap A (v.adicCompletionIntegers (FractionRing A)) (c : A)) :
        v.adicCompletionIntegers (FractionRing A)) : v.adicCompletion (FractionRing A)) = 0 := by
      rw [h]; rfl
    have h1 : algebraMap (FractionRing A) (v.adicCompletion (FractionRing A))
        (algebraMap A (FractionRing A) (c : A)) = 0 := h0
    rw [map_eq_zero, IsFractionRing.to_map_eq_zero_iff] at h1
    exact nonZeroDivisors.coe_ne_zero c h1
  · exact (Submodule.mem_bot _).2 h

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers (FractionRing A))`. Establish `: IsPrecomplete (maximalIdeal (v.adicCompletionIntegers (FractionRing A))) (v.adicCompletionIntegers (FractionRing A))` using `Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ`. Conclude with `{}`.
-/
theorem isAdicComplete :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers (FractionRing A)))
      (v.adicCompletionIntegers (FractionRing A)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers (FractionRing A))
  have : IsPrecomplete (maximalIdeal (v.adicCompletionIntegers (FractionRing A)))
      (v.adicCompletionIntegers (FractionRing A)) := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  exact {}

end Completion

/- English proof (translation)
Set `f : Spec (.of O) ⟶ Spec Γ(X, ⊤)` to `Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) O))`. Use `haveI : IsIso X.toSpecΓ.appTop := by rw [Scheme.toSpecΓ_appTop]; infer_instance`. Use `haveI : Flat f := by show Flat (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) O)))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 inferInstance`.

Establish `H` using `IsPullback.of_hasPullback X.toSpecΓ f`. Use `haveI : IsIso (pullback.snd X.toSpecΓ f).appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H`. Use `haveI : IsDomain Γ(pullback X.toSpecΓ f, ⊤) := (asIso (pullback.snd X.toSpecΓ f).appTop).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _`. Use `haveI hY := GlobalTheory.ConnDvr.connectedSpace_of_isDomain (pullback X.toSpecΓ f)`. Use `haveI hsp := GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms hM O _ (pullback.snd X.toSpecΓ f) inferInstance hY`.

Establish `hT : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f)) = (pullback.snd X.toSpecΓ f) ⁻¹' {IsLocalRing.closedPoint O}`. Establish `h` using `Scheme.Pullback.range_fst (pullback.snd X.toSpecΓ f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))`. Rewrite `h` using `[GlobalTheory.SpecialConn.range_residue]`. Conclude with `h`. Establish `hcl : (f (IsLocalRing.closedPoint O)).asIdeal = P`.

Use extensionality with `a`. Conclude with `hO a`. Establish `hw : ∀ y, X.toSpecΓ (pullback.fst X.toSpecΓ f y) = f (pullback.snd X.toSpecΓ f y)` using `fun y => by`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]`. Establish `hR : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) ≫ pullback.fst X.toSpecΓ f) = {z : X | GlobalTheory.SteinFibre.under z = P}`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`. Establish `hy : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) w ∈ Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f))` using `⟨w, rfl⟩`. Rewrite `hy` using `[hT]`.

Establish `hy' : pullback.snd X.toSpecΓ f (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) w) = IsLocalRing.closedPoint O` using `hy`. Use `show (X.toSpecΓ ((GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) ≫ pullback.fst X.toSpecΓ f) w)).asIdeal = P`. Rewrite using `[Scheme.Hom.comp_apply, hw, hy']`. Conclude with `hcl`. Introduce `hz`.

Establish `h1 : X.toSpecΓ z = f (IsLocalRing.closedPoint O)` using `PrimeSpectrum.ext (show (X.toSpecΓ z).asIdeal = _ from (hz : GlobalTheory.SteinFibre.under z = P).trans hcl.symm)`. Take `⟨y, hy1, hy2⟩` from `Scheme.Pullback.exists_preimage_pullback z _ h1`. Establish `hy : y ∈ Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f))`. Rewrite using `[hT]`. Conclude with `hy2`.

Take `⟨w, hw'⟩` from `hy`. Conclude with `⟨w, by rw [Scheme.Hom.comp_apply, hw', hy1]⟩`. Rewrite using `[← hR]`. Conclude with `isPreconnected_range (Scheme.Hom.continuous _)`.
-/
theorem isPreconnected_of_complete (hM : GlobalTheory.Published.FormalAlgebraisation.Morphisms) (X : Scheme.{0})
    [IsProper X.toSpecΓ] (P : Ideal Γ(X, ⊤)) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra Γ(X, ⊤) O] [Module.Flat Γ(X, ⊤) O]
    (hO : ∀ a, algebraMap Γ(X, ⊤) O a ∈ maximalIdeal O ↔ a ∈ P) :
    _root_.IsPreconnected {z : X | GlobalTheory.SteinFibre.under z = P} := by
  let f : Spec (.of O) ⟶ Spec Γ(X, ⊤) := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) O))
  haveI : IsIso X.toSpecΓ.appTop := by rw [Scheme.toSpecΓ_appTop]; infer_instance
  haveI : Flat f := by
    show Flat (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) O)))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have H := IsPullback.of_hasPullback X.toSpecΓ f
  haveI : IsIso (pullback.snd X.toSpecΓ f).appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  haveI : IsDomain Γ(pullback X.toSpecΓ f, ⊤) :=
    (asIso (pullback.snd X.toSpecΓ f).appTop).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  haveI hY := GlobalTheory.ConnDvr.connectedSpace_of_isDomain (pullback X.toSpecΓ f)
  haveI hsp := GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms hM O _ (pullback.snd X.toSpecΓ f)
    inferInstance hY
  have hT : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f)) =
      (pullback.snd X.toSpecΓ f) ⁻¹' {IsLocalRing.closedPoint O} := by
    have h := Scheme.Pullback.range_fst (pullback.snd X.toSpecΓ f)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    rw [GlobalTheory.SpecialConn.range_residue] at h
    exact h
  have hcl : (f (IsLocalRing.closedPoint O)).asIdeal = P := by
    ext a
    exact hO a
  have hw : ∀ y, X.toSpecΓ (pullback.fst X.toSpecΓ f y) = f (pullback.snd X.toSpecΓ f y) := fun y => by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hR : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) ≫ pullback.fst X.toSpecΓ f) =
      {z : X | GlobalTheory.SteinFibre.under z = P} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      have hy : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) w ∈
          Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f)) := ⟨w, rfl⟩
      rw [hT] at hy
      have hy' : pullback.snd X.toSpecΓ f (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) w) =
          IsLocalRing.closedPoint O := hy
      show (X.toSpecΓ ((GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) ≫ pullback.fst X.toSpecΓ f) w)).asIdeal = P
      rw [Scheme.Hom.comp_apply, hw, hy']
      exact hcl
    · intro hz
      have h1 : X.toSpecΓ z = f (IsLocalRing.closedPoint O) :=
        PrimeSpectrum.ext (show (X.toSpecΓ z).asIdeal = _ from (hz : GlobalTheory.SteinFibre.under z = P).trans hcl.symm)
      obtain ⟨y, hy1, hy2⟩ := Scheme.Pullback.exists_preimage_pullback z _ h1
      have hy : y ∈ Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f)) := by
        rw [hT]; exact hy2
      obtain ⟨w, hw'⟩ := hy
      exact ⟨w, by rw [Scheme.Hom.comp_apply, hw', hy1]⟩
  rw [← hR]
  exact isPreconnected_range (Scheme.Hom.continuous _)

/- English proof (translation)
Introduce `hP F _ _ X _ _ _ p e hX _ P`. Distinguish the cases in `hPp : P.IsPrime`. Use `swap`. Establish `h : {z : X | GlobalTheory.SteinFibre.under z = P} = ∅`. Use extensionality with `z`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`. Introduce `h`. Conclude with `hPp (h ▸ GlobalTheory.SteinFibre.under_isPrime z)`. Rewrite using `[h]`. Conclude with `isPreconnected_empty`.

Distinguish the cases in `hb : P = ⊥`. Substitute `hb` using the available equality. Establish `hη : GlobalTheory.SteinFibre.under (genericPoint X) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `a ha`.

Rewrite `ha` using `[GlobalTheory.SteinFibre.mem_under_iff]`. Rewrite using `[Ideal.mem_bot]`. Establish `hu : ∀ y : X.functionField, y ≠ 0 → IsUnit y` using `fun y hy => IsUnit.mk0 y hy`. Establish `h0 : X.presheaf.germ ⊤ (genericPoint X) trivial a = 0`. Assume the negation of the conclusion as `h`.

Conclude with `ha (hu _ h)`. Conclude with `germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial (h0.trans (map_zero _).symm)`. Use `(isPreconnected_singleton (x := genericPoint X)).subset_closure (fun z hz => ?_) (fun z _ => ?_)` and prove the remaining obligations. Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality.

Conclude with `hη`. Conclude with `specializes_iff_mem_closure.1 ((genericPoint_spec X).specializes (Set.mem_univ z))`. Set `v : HeightOneSpectrum Γ(X, ⊤)` to `⟨P, hPp, hb⟩`. Use `haveI hpr : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hX.isProjOver`. Establish `e1 : p = X.toSpecΓ ≫ (Spec.map p.appTop ≫ inv (Sp (𝓞 F)).toSpecΓ)`.

Rewrite using `[← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]`. Establish `h2` using `hpr`. Rewrite `h2` using `[e1]`. Use `haveI : IsProper X.toSpecΓ := IsProper.of_comp X.toSpecΓ (Spec.map p.appTop ≫ inv (Sp (𝓞 F)).toSpecΓ)`. Use `haveI := isAdicComplete v`.

Use `haveI := flat v`. Conclude with `isPreconnected_of_complete hP.q18.1 X P (v.adicCompletionIntegers (FractionRing Γ(X, ⊤))) (mem_maximalIdeal_iff v)`.
-/
theorem isPreconnected_setOf_under_eq : GlobalTheory.CovTop.Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsDedekindDomain Γ(X, ⊤)] (p : X ⟶ Sp (𝓞 F)) (e : ℕ), IsArithVar p e → IsArithVar (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) 0 →
    ∀ P : Ideal Γ(X, ⊤), _root_.IsPreconnected {z : X | GlobalTheory.SteinFibre.under z = P} := by
  intro hP F _ _ X _ _ _ p e hX _ P
  by_cases hPp : P.IsPrime
  swap
  · have h : {z : X | GlobalTheory.SteinFibre.under z = P} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hPp (h ▸ GlobalTheory.SteinFibre.under_isPrime z)
    rw [h]
    exact isPreconnected_empty
  by_cases hb : P = ⊥
  · subst hb
    have hη : GlobalTheory.SteinFibre.under (genericPoint X) = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [GlobalTheory.SteinFibre.mem_under_iff] at ha
      rw [Ideal.mem_bot]
      have hu : ∀ y : X.functionField, y ≠ 0 → IsUnit y := fun y hy => IsUnit.mk0 y hy
      have h0 : X.presheaf.germ ⊤ (genericPoint X) trivial a = 0 := by
        by_contra h
        exact ha (hu _ h)
      exact germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial (h0.trans (map_zero _).symm)
    refine (isPreconnected_singleton (x := genericPoint X)).subset_closure (fun z hz => ?_) (fun z _ => ?_)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hη
    · exact specializes_iff_mem_closure.1 ((genericPoint_spec X).specializes (Set.mem_univ z))
  let v : HeightOneSpectrum Γ(X, ⊤) := ⟨P, hPp, hb⟩
  haveI hpr : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hX.isProjOver
  have e1 : p = X.toSpecΓ ≫ (Spec.map p.appTop ≫ inv (Sp (𝓞 F)).toSpecΓ) := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have h2 := hpr
  rw [e1] at h2
  haveI : IsProper X.toSpecΓ := IsProper.of_comp X.toSpecΓ (Spec.map p.appTop ≫ inv (Sp (𝓞 F)).toSpecΓ)
  haveI := isAdicComplete v
  haveI := flat v
  exact isPreconnected_of_complete hP.q18.1 X P (v.adicCompletionIntegers (FractionRing Γ(X, ⊤)))
    (mem_maximalIdeal_iff v)

end GlobalTheory.SteinFibreConn
