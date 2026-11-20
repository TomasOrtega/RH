import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompleteUnramifiedResidueLift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EtaleCompletionResidue

open Polynomial

/- English proof (translation)
Use `letI : Algebra (ResidueField B) M := m.toAlgebra`. Use `haveI : FiniteDimensional (ResidueField B) M := hmf`. Use `haveI : Algebra.FormallyUnramified (ResidueField B) M := hmu`. Use `haveI : Algebra.IsSeparable (ResidueField B) M := (Algebra.FormallyUnramified.iff_isSeparable _ _).1 inferInstance`. Set `pb` to `Field.powerBasisOfFiniteOfSeparable (ResidueField B) M`.

Establish `hm` using `minpoly.monic pb.isIntegral_gen`. Establish `hirr` using `minpoly.irreducible pb.isIntegral_gen`. Take `⟨F, hF, hdeg, hFm⟩` from `Polynomial.lifts_and_degree_eq_and_monic (f := residue B) (Polynomial.mem_lifts_of_surjective residue_surjective _) hm`. Establish `hg : Irreducible (F.map (residue B))` using `hF ▸ hirr`. Use `haveI : Fact (Irreducible (F.map (residue B))) := ⟨hg⟩`.

Use `haveI hfin : Module.Finite B (AdjoinRoot F) := .of_basis (AdjoinRoot.powerBasis' hFm).basis`. Use `haveI : Module.Free B (AdjoinRoot F) := .of_basis (AdjoinRoot.powerBasis' hFm).basis`. Establish `hqf : IsField (AdjoinRoot F ⧸ (maximalIdeal B).map (AdjoinRoot.of F))`. Establish `hR : IsField (AdjoinRoot (F.map (residue B)))` using `Field.toIsField _`. Conclude with `MulEquiv.isField hR (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).toRingEquiv.toMulEquiv`.

Establish `hJ : ((maximalIdeal B).map (algebraMap B (AdjoinRoot F))).IsMaximal`. Rewrite using `[AdjoinRoot.algebraMap_eq]`. Conclude with `Ideal.Quotient.maximal_of_isField _ hqf`. Use `haveI : IsLocalRing (AdjoinRoot F) := by haveI : Algebra.IsIntegral B (AdjoinRoot F) := inferInstance`. Use `IsLocalRing.of_unique_max_ideal ⟨_, hJ, fun P hP => ?_⟩` and prove the remaining obligations.

Establish `hc : (P.comap (algebraMap B (AdjoinRoot F))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Establish `h1 : P.comap (algebraMap B (AdjoinRoot F)) = maximalIdeal B` using `IsLocalRing.eq_maximalIdeal hc`. Establish `hle : (maximalIdeal B).map (algebraMap B (AdjoinRoot F)) ≤ P` using `Ideal.map_le_iff_le_comap.2 h1.ge`. Conclude with `(hJ.eq_of_le hP.ne_top hle).symm`. Establish `hmax : maximalIdeal (AdjoinRoot F) = (maximalIdeal B).map (algebraMap B (AdjoinRoot F))` using `(IsLocalRing.eq_maximalIdeal hJ).symm`.

Use `haveI hloc : IsLocalHom (algebraMap B (AdjoinRoot F)) := by`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Assume the negation of the conclusion as `h`. Establish `h2 : algebraMap B (AdjoinRoot F) x ∈ maximalIdeal (AdjoinRoot F)`.

Rewrite using `[hmax]`. Conclude with `Ideal.mem_map_of_mem _ h`. Conclude with `h2 hx`. Establish `hinj : Function.Injective (algebraMap B (AdjoinRoot F))`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Assume the negation of the conclusion as `h0`. Express the relevant statement in the definitionally equal form `AdjoinRoot.mk F (C x) = 0 at hx`. Rewrite `hx` using `[AdjoinRoot.mk_eq_zero]`. Use `hFm.not_dvd_of_natDegree_lt (Polynomial.C_ne_zero.2 h0) ?_ hx` and prove the remaining obligations.

Rewrite using `[natDegree_C, natDegree_eq_of_degree_eq hdeg]`. Conclude with `minpoly.natDegree_pos pb.isIntegral_gen`. Use `haveI : IsNoetherianRing (AdjoinRoot F) := isNoetherian_of_tower B inferInstance`. Set `e₁ : ResidueField (AdjoinRoot F) ≃+* AdjoinRoot (F.map (residue B))` to `(Ideal.quotEquivOfEq hmax).trans (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).toRingEquiv`. Establish `he₁ : e₁.toRingHom.comp (ResidueField.map (algebraMap B (AdjoinRoot F))) = AdjoinRoot.of (F.map (residue B))`.

Apply `Ideal.Quotient.ringHom_ext` to reduce the goal to its premises. Use extensionality with `x`. Use `show e₁ (ResidueField.map _ (residue B x)) = _`. Rewrite using `[ResidueField.map_residue]`. Conclude with `(AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).commutes x`.

Set `pb'` to `AdjoinRoot.powerBasis (hFm.map (residue B)).ne_zero`. Establish `hmin : minpoly (ResidueField B) pb.gen = minpoly (ResidueField B) pb'.gen`. Rewrite using `[AdjoinRoot.minpoly_powerBasis_gen_of_monic (hFm.map (residue B)), hF]`. Set `e₂ : M ≃ₐ[ResidueField B] AdjoinRoot (F.map (residue B))` to `pb.equivOfMinpoly pb' hmin`. Set `Eq' : M ≃+* ResidueField (AdjoinRoot F)` to `e₂.toRingEquiv.trans e₁.symm`.

Establish `hE : Eq'.toRingHom.comp m = ResidueField.map (algebraMap B (AdjoinRoot F))`. Use extensionality with `x`. Establish `h1 : e₁ (ResidueField.map (algebraMap B (AdjoinRoot F)) x) = AdjoinRoot.of (F.map (residue B)) x` using `congrArg (fun q => q x) he₁`. Establish `h2 : e₂ (m x) = AdjoinRoot.of (F.map (residue B)) x`. Rewrite using `[← AdjoinRoot.algebraMap_eq]`.

Conclude with `e₂.commutes x`. Use `show e₁.symm (e₂ (m x)) = _`. Rewrite using `[h2, ← h1, RingEquiv.symm_apply_apply]`. Establish `hψfin : (algebraMap B (AdjoinRoot F)).Finite` using `RingHom.finite_algebraMap.mpr hfin`. Use `⟨AdjoinRoot F, inferInstance, inferInstance, algebraMap B (AdjoinRoot F), hloc, Eq', inferInstance, hinj, RingHom.flat_algebraMap_iff.mpr inferInstance, hmax.symm, RingHom.Finite.comp (RingHom.Finite.of_surjective _ residue_surjective) hψfin, ?_, hE⟩` and prove the remaining obligations.

Rewrite using `[← ResidueField.map_comp_residue, ← hE]`. Conclude with `RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective) (RingHom.FormallyUnramified.comp hmu (RingHom.FormallyUnramified.of_surjective Eq'.surjective))`.
-/
theorem exists_finite_free_local_residue_equiv (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (M : Type)
    [Field M] (m : ResidueField B →+* M) (hmf : m.Finite) (hmu : m.FormallyUnramified) :
    ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (ψ₀ : B →+* C) (_ : IsLocalHom ψ₀) (E : M ≃+* ResidueField C),
      IsNoetherianRing C ∧ Function.Injective ψ₀ ∧ ψ₀.Flat ∧ (maximalIdeal B).map ψ₀ = maximalIdeal C ∧
      ((residue C).comp ψ₀).Finite ∧ ((residue C).comp ψ₀).FormallyUnramified ∧ (E : M →+* ResidueField C).comp m = ResidueField.map ψ₀ := by
  letI : Algebra (ResidueField B) M := m.toAlgebra
  haveI : FiniteDimensional (ResidueField B) M := hmf
  haveI : Algebra.FormallyUnramified (ResidueField B) M := hmu
  haveI : Algebra.IsSeparable (ResidueField B) M := (Algebra.FormallyUnramified.iff_isSeparable _ _).1 inferInstance
  let pb := Field.powerBasisOfFiniteOfSeparable (ResidueField B) M
  have hm := minpoly.monic pb.isIntegral_gen
  have hirr := minpoly.irreducible pb.isIntegral_gen
  obtain ⟨F, hF, hdeg, hFm⟩ := Polynomial.lifts_and_degree_eq_and_monic (f := residue B)
    (Polynomial.mem_lifts_of_surjective residue_surjective _) hm
  have hg : Irreducible (F.map (residue B)) := hF ▸ hirr
  haveI : Fact (Irreducible (F.map (residue B))) := ⟨hg⟩
  haveI hfin : Module.Finite B (AdjoinRoot F) := .of_basis (AdjoinRoot.powerBasis' hFm).basis
  haveI : Module.Free B (AdjoinRoot F) := .of_basis (AdjoinRoot.powerBasis' hFm).basis
  have hqf : IsField (AdjoinRoot F ⧸ (maximalIdeal B).map (AdjoinRoot.of F)) := by
    have hR : IsField (AdjoinRoot (F.map (residue B))) := Field.toIsField _
    exact MulEquiv.isField hR (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).toRingEquiv.toMulEquiv
  have hJ : ((maximalIdeal B).map (algebraMap B (AdjoinRoot F))).IsMaximal := by
    rw [AdjoinRoot.algebraMap_eq]
    exact Ideal.Quotient.maximal_of_isField _ hqf
  haveI : IsLocalRing (AdjoinRoot F) := by
    haveI : Algebra.IsIntegral B (AdjoinRoot F) := inferInstance
    refine IsLocalRing.of_unique_max_ideal ⟨_, hJ, fun P hP => ?_⟩
    have hc : (P.comap (algebraMap B (AdjoinRoot F))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    have h1 : P.comap (algebraMap B (AdjoinRoot F)) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hc
    have hle : (maximalIdeal B).map (algebraMap B (AdjoinRoot F)) ≤ P := Ideal.map_le_iff_le_comap.2 h1.ge
    exact (hJ.eq_of_le hP.ne_top hle).symm
  have hmax : maximalIdeal (AdjoinRoot F) = (maximalIdeal B).map (algebraMap B (AdjoinRoot F)) :=
    (IsLocalRing.eq_maximalIdeal hJ).symm
  haveI hloc : IsLocalHom (algebraMap B (AdjoinRoot F)) := by
    constructor
    intro x hx
    by_contra h
    have h2 : algebraMap B (AdjoinRoot F) x ∈ maximalIdeal (AdjoinRoot F) := by
      rw [hmax]; exact Ideal.mem_map_of_mem _ h
    exact h2 hx
  have hinj : Function.Injective (algebraMap B (AdjoinRoot F)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    change AdjoinRoot.mk F (C x) = 0 at hx
    rw [AdjoinRoot.mk_eq_zero] at hx
    refine hFm.not_dvd_of_natDegree_lt (Polynomial.C_ne_zero.2 h0) ?_ hx
    rw [natDegree_C, natDegree_eq_of_degree_eq hdeg]
    exact minpoly.natDegree_pos pb.isIntegral_gen
  haveI : IsNoetherianRing (AdjoinRoot F) := isNoetherian_of_tower B inferInstance
  let e₁ : ResidueField (AdjoinRoot F) ≃+* AdjoinRoot (F.map (residue B)) :=
    (Ideal.quotEquivOfEq hmax).trans (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).toRingEquiv
  have he₁ : e₁.toRingHom.comp (ResidueField.map (algebraMap B (AdjoinRoot F))) = AdjoinRoot.of (F.map (residue B)) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    show e₁ (ResidueField.map _ (residue B x)) = _
    rw [ResidueField.map_residue]
    exact (AdjoinRoot.quotEquivQuotMap F (maximalIdeal B)).commutes x
  let pb' := AdjoinRoot.powerBasis (hFm.map (residue B)).ne_zero
  have hmin : minpoly (ResidueField B) pb.gen = minpoly (ResidueField B) pb'.gen := by
    rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic (hFm.map (residue B)), hF]
  let e₂ : M ≃ₐ[ResidueField B] AdjoinRoot (F.map (residue B)) := pb.equivOfMinpoly pb' hmin
  let Eq' : M ≃+* ResidueField (AdjoinRoot F) := e₂.toRingEquiv.trans e₁.symm
  have hE : Eq'.toRingHom.comp m = ResidueField.map (algebraMap B (AdjoinRoot F)) := by
    ext x
    have h1 : e₁ (ResidueField.map (algebraMap B (AdjoinRoot F)) x) = AdjoinRoot.of (F.map (residue B)) x :=
      congrArg (fun q => q x) he₁
    have h2 : e₂ (m x) = AdjoinRoot.of (F.map (residue B)) x := by
      rw [← AdjoinRoot.algebraMap_eq]
      exact e₂.commutes x
    show e₁.symm (e₂ (m x)) = _
    rw [h2, ← h1, RingEquiv.symm_apply_apply]
  have hψfin : (algebraMap B (AdjoinRoot F)).Finite := RingHom.finite_algebraMap.mpr hfin
  refine ⟨AdjoinRoot F, inferInstance, inferInstance, algebraMap B (AdjoinRoot F), hloc, Eq', inferInstance,
    hinj, RingHom.flat_algebraMap_iff.mpr inferInstance, hmax.symm,
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ residue_surjective) hψfin, ?_, hE⟩
  rw [← ResidueField.map_comp_residue, ← hE]
  exact RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective)
    (RingHom.FormallyUnramified.comp hmu (RingHom.FormallyUnramified.of_surjective Eq'.surjective))

/- English proof (translation)
Introduce `O _ _ _ _ _ _ M _ m hmf hmu`. Establish `hOn : IsNoetherianRing O` using `Algebra.EssFiniteType.isNoetherianRing ℤ O`. Take `⟨C, _, _, ψ₀, hψl, E₀, hCn, hψi, hψf, hψm, hψfin, hψfu, hE⟩` from `exists_finite_free_local_residue_equiv O M m hmf hmu`. Use `haveI := hCn`. Use `haveI := hψl`.

Set `A` to `AdicCompletion (maximalIdeal C) C`. Set `j : C →+* A` to `algebraMap C A`. Use `haveI : Module.Flat C A := AdicCompletion.flat_of_isNoetherian _`. Establish `hbij : Function.Bijective (ResidueField.map j)` using `AdicCompletion.residueField_map_bijective C`. Establish `hcomp : (residue A).comp (j.comp ψ₀) = (ResidueField.map j).comp ((residue C).comp ψ₀)`.

Use extensionality with `b`. Simplify using `[ResidueField.map_residue]`. Establish `hAn : IsNoetherianRing A` using `GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _`. Establish `hAc : IsAdicComplete (maximalIdeal A) A` using `inferInstance`. Establish `hjl : IsLocalHom j` using `inferInstance`.

Establish `hji : Function.Injective j` using `AdicCompletion.of_injective (maximalIdeal C) C`. Set `ψ : O →+* A` to `j.comp ψ₀`. Establish `hloc : IsLocalHom ψ` using `inferInstance`. Establish `het : IsEtaleCompletion ψ`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `RingHom.Flat.comp hψf (RingHom.flat_algebraMap_iff.2 inferInstance)`. Use `show (maximalIdeal O).map (j.comp ψ₀) = _`. Rewrite using `[← Ideal.map_map, hψm, AdicCompletion.maximalIdeal_eq_map]`. Use `show ((residue A).comp (j.comp ψ₀)).Finite`. Rewrite using `[hcomp]`.

Conclude with `RingHom.Finite.comp (RingHom.Finite.of_surjective _ hbij.2) hψfin`. Establish `hur : ((residue A).comp ψ).FormallyUnramified` using `by show ((residue A).comp (j.comp ψ₀)).FormallyUnramified`. Rewrite using `[hcomp]`. Conclude with `RingHom.FormallyUnramified.comp hψfu (RingHom.FormallyUnramified.of_surjective hbij.2)`. Take `⟨hd, hic⟩` from `GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed O`.

Take `⟨hAd, hAi⟩` from `GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed O A ψ hOn hd hic hAn hAc hloc het hur`. Use `haveI := hAd`. Establish `hψinj : Function.Injective ψ` using `hji.comp hψi`. Use `haveI : CharZero A := charZero_of_injective_ringHom hψinj`. Set `E : M ≃+* ResidueField A` to `E₀.trans (RingEquiv.ofBijective _ hbij)`.

Use `⟨A, inferInstance, hAd, inferInstance, ψ, hloc, E, ⟨hAn, hAi, hAc, inferInstance⟩, het, hur, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Take `⟨b, rfl⟩` from `residue_surjective x`. Establish `h2` using `congrArg (fun t => t (residue O b)) hE`. Simplify using `only [RingHom.comp_apply, ResidueField.map_residue] at h2`.

Use `show ResidueField.map j (E₀ (m (residue O b))) = _`. Establish `h3 : E₀ (m (residue O b)) = residue C (ψ₀ b)` using `h2`. Rewrite using `[h3]`. Simplify using `only [ψ, ResidueField.map_residue, RingHom.comp_apply]`.
-/
theorem exists_etaleCompletion_residue_equiv : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] (M : Type) [Field M] (m : ResidueField O →+* M), m.Finite → m.FormallyUnramified → ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (ψ : O →+* A) (_ : IsLocalHom ψ) (E : M ≃+* ResidueField A), IsCN A ∧ IsEtaleCompletion ψ ∧ ((residue A).comp ψ).FormallyUnramified ∧ (E : M →+* ResidueField A).comp m = ResidueField.map ψ := by
  intro O _ _ _ _ _ _ M _ m hmf hmu
  have hOn : IsNoetherianRing O := Algebra.EssFiniteType.isNoetherianRing ℤ O
  obtain ⟨C, _, _, ψ₀, hψl, E₀, hCn, hψi, hψf, hψm, hψfin, hψfu, hE⟩ :=
    exists_finite_free_local_residue_equiv O M m hmf hmu
  haveI := hCn
  haveI := hψl
  let A := AdicCompletion (maximalIdeal C) C
  let j : C →+* A := algebraMap C A
  haveI : Module.Flat C A := AdicCompletion.flat_of_isNoetherian _
  have hbij : Function.Bijective (ResidueField.map j) := AdicCompletion.residueField_map_bijective C
  have hcomp : (residue A).comp (j.comp ψ₀) = (ResidueField.map j).comp ((residue C).comp ψ₀) := by
    ext b
    simp [ResidueField.map_residue]
  have hAn : IsNoetherianRing A := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _
  have hAc : IsAdicComplete (maximalIdeal A) A := inferInstance
  have hjl : IsLocalHom j := inferInstance
  have hji : Function.Injective j := AdicCompletion.of_injective (maximalIdeal C) C
  let ψ : O →+* A := j.comp ψ₀
  have hloc : IsLocalHom ψ := inferInstance
  have het : IsEtaleCompletion ψ := by
    refine ⟨?_, ?_, ?_⟩
    · exact RingHom.Flat.comp hψf (RingHom.flat_algebraMap_iff.2 inferInstance)
    · show (maximalIdeal O).map (j.comp ψ₀) = _
      rw [← Ideal.map_map, hψm, AdicCompletion.maximalIdeal_eq_map]
    · show ((residue A).comp (j.comp ψ₀)).Finite
      rw [hcomp]
      exact RingHom.Finite.comp (RingHom.Finite.of_surjective _ hbij.2) hψfin
  have hur : ((residue A).comp ψ).FormallyUnramified := by
    show ((residue A).comp (j.comp ψ₀)).FormallyUnramified
    rw [hcomp]
    exact RingHom.FormallyUnramified.comp hψfu (RingHom.FormallyUnramified.of_surjective hbij.2)
  obtain ⟨hd, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed O
  obtain ⟨hAd, hAi⟩ := GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed O A ψ hOn hd hic hAn hAc hloc het hur
  haveI := hAd
  have hψinj : Function.Injective ψ := hji.comp hψi
  haveI : CharZero A := charZero_of_injective_ringHom hψinj
  let E : M ≃+* ResidueField A := E₀.trans (RingEquiv.ofBijective _ hbij)
  refine ⟨A, inferInstance, hAd, inferInstance, ψ, hloc, E, ⟨hAn, hAi, hAc, inferInstance⟩, het, hur, ?_⟩
  ext x
  obtain ⟨b, rfl⟩ := residue_surjective x
  have h2 := congrArg (fun t => t (residue O b)) hE
  simp only [RingHom.comp_apply, ResidueField.map_residue] at h2
  show ResidueField.map j (E₀ (m (residue O b))) = _
  have h3 : E₀ (m (residue O b)) = residue C (ψ₀ b) := h2
  rw [h3]
  simp only [ψ, ResidueField.map_residue, RingHom.comp_apply]

end GlobalTheory.EtaleCompletionResidue
