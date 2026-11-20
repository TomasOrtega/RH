import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveElementUnramified
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHenselRootResidue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniqueness
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EtaleCompletionLift

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

Conclude with `e₂.commutes x`. Use `show e₁.symm (e₂ (m x)) = _`. Rewrite using `[h2, ← h1, RingEquiv.symm_apply_apply]`. Establish `hψfin : (algebraMap B (AdjoinRoot F)).Finite` using `RingHom.finite_algebraMap.mpr hfin`. Use `⟨AdjoinRoot F, inferInstance, inferInstance, algebraMap B (AdjoinRoot F), hloc, Eq'.toRingHom, inferInstance, hinj, RingHom.flat_algebraMap_iff.mpr inferInstance, hmax.symm, RingHom.Finite.comp (RingHom.Finite.of_surjective _ residue_surjective) hψfin, ?_, hE⟩` and prove the remaining obligations.

Rewrite using `[← ResidueField.map_comp_residue, ← hE]`. Conclude with `RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective) (RingHom.FormallyUnramified.comp hmu (RingHom.FormallyUnramified.of_surjective Eq'.surjective))`.
-/
theorem exists_finite_free_local_of_residue (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (M : Type)
    [Field M] (m : ResidueField B →+* M) (hmf : m.Finite) (hmu : m.FormallyUnramified) :
    ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (ψ₀ : B →+* C) (_ : IsLocalHom ψ₀) (E : M →+* ResidueField C),
      IsNoetherianRing C ∧ Function.Injective ψ₀ ∧ ψ₀.Flat ∧ (maximalIdeal B).map ψ₀ = maximalIdeal C ∧
      ((residue C).comp ψ₀).Finite ∧ ((residue C).comp ψ₀).FormallyUnramified ∧ E.comp m = ResidueField.map ψ₀ := by
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
  refine ⟨AdjoinRoot F, inferInstance, inferInstance, algebraMap B (AdjoinRoot F), hloc, Eq'.toRingHom, inferInstance,
    hinj, RingHom.flat_algebraMap_iff.mpr inferInstance, hmax.symm,
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ residue_surjective) hψfin, ?_, hE⟩
  rw [← ResidueField.map_comp_residue, ← hE]
  exact RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective residue_surjective)
    (RingHom.FormallyUnramified.comp hmu (RingHom.FormallyUnramified.of_surjective Eq'.surjective))

/- English proof (translation)
Introduce `S₀ B R₀ k' _ _ _ _ _ _ _ _ _ _ _ f g v hR₀ hf hg het hur hvf hvu`. Use `haveI := hR₀`. Establish `hBn : IsNoetherianRing B` using `Algebra.EssFiniteType.isNoetherianRing ℤ B`. Take `⟨hflat, hmax, hfin⟩` from `het`. Establish `hfin' : (ResidueField.map g).Finite`.

Rewrite `hfin` using `[← ResidueField.map_comp_residue]`. Conclude with `RingHom.Finite.of_comp_finite hfin`. Establish `hur' : (ResidueField.map g).FormallyUnramified`. Rewrite `hur` using `[← ResidueField.map_comp_residue]`. Conclude with `RingHom.FormallyUnramified.of_comp hur`.

Take `⟨θ, q, hqm, hqθ, hqd, hgen, hind⟩` from `GlobalTheory.exists_hensel_generator_of_residue_finite_unramified g hfin hur`. Take `⟨M, _, u, w, huw, hwf, hwu⟩` from `GlobalTheory.compositum_finite_formallyUnramified (ResidueField.map g) (v.comp (ResidueField.map f)) hfin' hur'`. Take `⟨C, _, _, ψ₀, hψl, E, hCn, hψi, hψf, hψm, hψfin, hψfu, hE⟩` from `exists_finite_free_local_of_residue B M (w.comp v) (RingHom.Finite.comp hwf hvf) (RingHom.FormallyUnramified.comp hvu hwu)`. Take `⟨A, _, _, ι, hAn, hAc, hιl, hιi, hιe, hιu⟩` from `GlobalTheory.CompletionEtale.exists_completion B C ψ₀ hCn hψl hψf hψm hψfin hψfu`. Take `⟨hd, hic⟩` from `GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed B`.

Use `haveI := hιl`. Use `haveI := hψl`. Set `ψ : B →+* A` to `ι.comp ψ₀`. Establish `hloc : IsLocalHom ψ` using `inferInstance`. Take `⟨hAd, hAi⟩` from `GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed B A ψ hBn hd hic hAn hAc hloc hιe hιu`.

Use `haveI := hAd`. Use `haveI := hAc`. Establish `hψinj : Function.Injective ψ` using `hιi.comp hψi`. Use `haveI : CharZero A := charZero_of_injective_ringHom hψinj`. Set `σ : ResidueField R₀ →+* ResidueField A` to `((ResidueField.map ι).comp E).comp u`.

Establish `hσ : ∀ a, σ (residue R₀ (g a)) = residue A ((ψ.comp f) a)`. Introduce `a`. Establish `h1` using `congrArg (fun t => t (residue S₀ a)) huw`. Simplify using `only [RingHom.comp_apply, ResidueField.map_residue] at h1`. Establish `h2` using `congrArg (fun t => t (residue B (f a))) hE`.

Simplify using `only [RingHom.comp_apply, ResidueField.map_residue] at h2`. Simplify using `only [σ, ψ, RingHom.comp_apply, h1, h2, ResidueField.map_residue]`. Take `⟨η, hη, -⟩` from `GlobalTheory.exists_root_lift_of_residue_map g (ψ.comp f) σ hσ θ q hqm hqθ hqd`. Establish `hgp` using `GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow g hmax θ hgen`. Establish `hip` using `GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max g hflat hmax θ q hqm hqθ hgp hind`.

Take `⟨φ, hφ, hφl⟩` from `GlobalTheory.lift_of_compatible_approx g (ψ.comp f) inferInstance θ η q hqm hqθ hη hgp hip`. Use `⟨A, inferInstance, hAd, inferInstance, ψ, φ, ((ResidueField.map ι).comp E).comp w, ⟨hAn, hAi, hAc, inferInstance⟩, hloc, hιe, hιu, hφl, hφ.symm, ?_⟩` and prove the remaining obligations. Use extensionality with `b`. Establish `h2` using `congrArg (fun t => t (residue B b)) hE`. Simplify using `only [RingHom.comp_apply, ResidueField.map_residue] at h2`.

Simplify using `only [ψ, RingHom.comp_apply, h2, ResidueField.map_residue]`.
-/
theorem exists_etaleCompletion_over : ∀ (S₀ B R₀ k' : Type) [CommRing S₀] [IsLocalRing S₀] [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [CharZero B] [Algebra.EssFiniteType ℤ B] [CommRing R₀] [IsLocalRing R₀] [Field k'] (f : S₀ →+* B) (g : S₀ →+* R₀) (v : ResidueField B →+* k'), IsAdicComplete (maximalIdeal R₀) R₀ → IsLocalHom f → IsLocalHom g → IsEtaleCompletion g → ((residue R₀).comp g).FormallyUnramified → v.Finite → v.FormallyUnramified → ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (ψ : B →+* A) (φ : R₀ →+* A) (τ : k' →+* ResidueField A), IsCN A ∧ IsLocalHom ψ ∧ IsEtaleCompletion ψ ∧ ((residue A).comp ψ).FormallyUnramified ∧ IsLocalHom φ ∧ ψ.comp f = φ.comp g ∧ τ.comp (v.comp (residue B)) = (residue A).comp ψ := by
  intro S₀ B R₀ k' _ _ _ _ _ _ _ _ _ _ _ f g v hR₀ hf hg het hur hvf hvu
  haveI := hR₀
  have hBn : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing ℤ B
  obtain ⟨hflat, hmax, hfin⟩ := het
  have hfin' : (ResidueField.map g).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hur' : (ResidueField.map g).FormallyUnramified := by
    rw [← ResidueField.map_comp_residue] at hur
    exact RingHom.FormallyUnramified.of_comp hur
  obtain ⟨θ, q, hqm, hqθ, hqd, hgen, hind⟩ := GlobalTheory.exists_hensel_generator_of_residue_finite_unramified g hfin hur
  obtain ⟨M, _, u, w, huw, hwf, hwu⟩ := GlobalTheory.compositum_finite_formallyUnramified (ResidueField.map g) (v.comp (ResidueField.map f)) hfin' hur'
  obtain ⟨C, _, _, ψ₀, hψl, E, hCn, hψi, hψf, hψm, hψfin, hψfu, hE⟩ :=
    exists_finite_free_local_of_residue B M (w.comp v) (RingHom.Finite.comp hwf hvf)
      (RingHom.FormallyUnramified.comp hvu hwu)
  obtain ⟨A, _, _, ι, hAn, hAc, hιl, hιi, hιe, hιu⟩ := GlobalTheory.CompletionEtale.exists_completion B C ψ₀ hCn hψl hψf hψm hψfin hψfu
  obtain ⟨hd, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed B
  haveI := hιl
  haveI := hψl
  let ψ : B →+* A := ι.comp ψ₀
  have hloc : IsLocalHom ψ := inferInstance
  obtain ⟨hAd, hAi⟩ := GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed B A ψ hBn hd hic hAn hAc hloc hιe hιu
  haveI := hAd
  haveI := hAc
  have hψinj : Function.Injective ψ := hιi.comp hψi
  haveI : CharZero A := charZero_of_injective_ringHom hψinj
  let σ : ResidueField R₀ →+* ResidueField A := ((ResidueField.map ι).comp E).comp u
  have hσ : ∀ a, σ (residue R₀ (g a)) = residue A ((ψ.comp f) a) := by
    intro a
    have h1 := congrArg (fun t => t (residue S₀ a)) huw
    simp only [RingHom.comp_apply, ResidueField.map_residue] at h1
    have h2 := congrArg (fun t => t (residue B (f a))) hE
    simp only [RingHom.comp_apply, ResidueField.map_residue] at h2
    simp only [σ, ψ, RingHom.comp_apply, h1, h2, ResidueField.map_residue]
  obtain ⟨η, hη, -⟩ := GlobalTheory.exists_root_lift_of_residue_map g (ψ.comp f) σ hσ θ q hqm hqθ hqd
  have hgp := GlobalTheory.exists_poly_sub_mem_maximalIdeal_pow g hmax θ hgen
  have hip := GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max g hflat hmax θ q hqm hqθ hgp hind
  obtain ⟨φ, hφ, hφl⟩ := GlobalTheory.lift_of_compatible_approx g (ψ.comp f) inferInstance θ η q hqm hqθ hη hgp hip
  refine ⟨A, inferInstance, hAd, inferInstance, ψ, φ, ((ResidueField.map ι).comp E).comp w,
    ⟨hAn, hAi, hAc, inferInstance⟩, hloc, hιe, hιu, hφl, hφ.symm, ?_⟩
  ext b
  have h2 := congrArg (fun t => t (residue B b)) hE
  simp only [RingHom.comp_apply, ResidueField.map_residue] at h2
  simp only [ψ, RingHom.comp_apply, h2, ResidueField.map_residue]

end GlobalTheory.EtaleCompletionLift
