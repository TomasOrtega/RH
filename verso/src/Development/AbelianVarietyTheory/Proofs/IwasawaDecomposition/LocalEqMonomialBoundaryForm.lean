import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalDomainPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TorRef

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Z g φs 𝒩 φ EX N R _ _ _ ξ t mt P m γ hg hfan href hN hphi hCN hEt hun hTor hcone hin`. Establish `hCN'` using `hCN`. Take `⟨hNoeth, hIC, -, hChar⟩` from `hCN'`. Use `haveI := hNoeth`. Use `haveI := hChar`.

Use `haveI := c.fin`. Use `haveI : NumberField c.F := {}`. Take `⟨y, hy⟩` from `DomFine.exists_generic_point (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense ξ hEt.1`. Take `⟨W, _, _, _, f, hW, hfi, hfm⟩` from `PrimeUnif.exists_cdvr R (maximalIdeal R)`. Establish `hloc : IsLocalHom f` using `⟨fun a ha => by`.

Assume the negation of the conclusion as `h`. Establish `h' : a ∈ (maximalIdeal W).comap f` using `hfm.symm ▸ (mem_maximalIdeal a).2 h`. Conclude with `(mem_maximalIdeal _).1 h' ha⟩`. Establish `hW'` using `hW`. Take `⟨hdvr, hcpl, hch⟩` from `hW'`.

Use `haveI := hdvr`. Use `haveI := hcpl`. Use `haveI := hch`. Establish `hCNW : IsCN W` using `⟨inferInstance, inferInstance, hcpl, hch⟩`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible W`.

Take `⟨t', mt', P', e, -, hcoord⟩` from `pullSt E H R W f t P hCN hCNW hfi hloc hTor`. Take `⟨be', hbe', hmon, -⟩` from `exists_periodForm P' hϖ`. Take `⟨mt''⟩` from `TraitOrder.comp rfl mt mt'`. Establish `j : Function.Injective ((algebraMap W (FractionRing W)).comp f)` using `(IsFractionRing.injective W _).comp hfi`. Set `gK : FractionRing R →+* FractionRing W` to `IsFractionRing.lift j`.

Establish `eK : jK W ≫ spMap f = spMap gK ≫ jK R` using `(GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm`. Establish `hr : Set.range (jK W ≫ spMap f ≫ ξ) ⊆ Set.range Z.j`. Establish `hmor : spMap gK ≫ y ≫ Z.j = jK W ≫ spMap f ≫ ξ`. Rewrite using `[← Category.assoc (jK W), eK, Category.assoc, ← hy]`. Both sides reduce to the same expression.

Introduce and unpack `_ ⟨p, rfl⟩`. Use `⟨(spMap gK ≫ y) p, ?_⟩` and prove the remaining obligations. Use `show (spMap gK ≫ y ≫ Z.j) p = _`. Rewrite using `[hmor]`. Take `⟨n, hn, hid⟩` from `hphi W hW ϖ hϖ (spMap f ≫ ξ) t' mt'' P' hr be' hbe' hmon`.

Set `es : P.D.toPre.X →ₗ[ℤ] P'.D.toPre.X` to `e.symm.toLinearMap.toAddMonoidHom.toIntLinearMap`. Set `be : LinearMap.BilinForm ℤ P.D.toPre.X` to `be'.compl₁₂ es es`. Establish `hbe : ∀ a b, be a b = be' (e.symm a) (e.symm b)` using `fun _ _ => rfl`. Use `⟨W, inferInstance, inferInstance, inferInstance, hW, ϖ, hϖ, f, hloc, be, fun a b => ?_, fun a => ?_, n, ?_, hid⟩` and prove the remaining obligations. Rewrite using `[hbe, hbe, hbe'.1]`.

Take `⟨u, k, hk, hc⟩` from `hmon (e.symm a)`. Take `⟨⟨r, hr0, -⟩, -⟩` from `GlobalTheory.PsiCoordLocal.main R P.D hIC a`. Take `⟨u', hc'⟩` from `hcoord (e.symm a) r (by rw [LinearEquiv.apply_symm_apply]; exact hr0)`. Take `⟨v, hv⟩` from `GlobalTheory.PsiCoordLocal.exists_unit_of_coord hc hc'`. Use `⟨r, k 0, hr0, by rw [hbe]; exact hk 0, ?_⟩` and prove the remaining obligations.

Establish `e1 : f r = ((u'⁻¹ * v * u : Wˣ) : W) * ϖ ^ k 0`. Establish `: (u' : W) * f r = v * (u * ϖ ^ k 0)` using `by simpa using hv`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1]`. Conclude with `(associated_unit_mul_left _ _ (Units.isUnit _))`.

Rewrite using `[hn]`. Establish `e2 : φ.evalZ be = φ.evalZ be'` using `InvFun.eval_equiv φ e.symm (fun a b => ((be' a b : ℤ) : ℝ))`. Rewrite using `[e2]`. Simplify using `only [InvFun.evalZ, InvFun.eval, comb]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_trait_phiDiv_order : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (EX : EffCartierData Z.X) (N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)), SABMap t Z.t ξ → ∀ (P : PELUnif (maximalIdeal R) t) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → 0 < N → IsPhiDiv (comb 0 φ N φ) Z EX → IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ConeZ E φs P.D.toPre.X m γ → InCone P.D.toPre γ → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W), CDvr W ∧ ∃ ϖ : W, Irreducible ϖ ∧ ∃ f : R →+* W, IsLocalHom f ∧ ∃ be : LinearMap.BilinForm ℤ P.D.toPre.X, (∀ y z, be y z = be z y) ∧ FormAt P.D.toPre f ϖ be ∧ ∃ n : ℕ, (n : ℝ) = N * φ.evalZ be ∧ idlAlong EX.idealSheaf (spMap f ≫ ξ) = Ideal.span {ϖ ^ n} := by
  intro E _ _ _ H D l Xo c Z g φs 𝒩 φ EX N R _ _ _ ξ t mt P m γ hg hfan href hN hphi hCN hEt hun hTor hcone hin
  have hCN' := hCN
  obtain ⟨hNoeth, hIC, -, hChar⟩ := hCN'
  haveI := hNoeth
  haveI := hChar
  haveI := c.fin
  haveI : NumberField c.F := {}

  obtain ⟨y, hy⟩ := DomFine.exists_generic_point (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open
    Z.jQ_dense ξ hEt.1

  obtain ⟨W, _, _, _, f, hW, hfi, hfm⟩ := PrimeUnif.exists_cdvr R (maximalIdeal R)
  have hloc : IsLocalHom f := ⟨fun a ha => by
    by_contra h
    have h' : a ∈ (maximalIdeal W).comap f := hfm.symm ▸ (mem_maximalIdeal a).2 h
    exact (mem_maximalIdeal _).1 h' ha⟩
  have hW' := hW
  obtain ⟨hdvr, hcpl, hch⟩ := hW'
  haveI := hdvr
  haveI := hcpl
  haveI := hch
  have hCNW : IsCN W := ⟨inferInstance, inferInstance, hcpl, hch⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨t', mt', P', e, -, hcoord⟩ := pullSt E H R W f t P hCN hCNW hfi hloc hTor
  obtain ⟨be', hbe', hmon, -⟩ := exists_periodForm P' hϖ
  obtain ⟨mt''⟩ := TraitOrder.comp rfl mt mt'

  have j : Function.Injective ((algebraMap W (FractionRing W)).comp f) :=
    (IsFractionRing.injective W _).comp hfi
  let gK : FractionRing R →+* FractionRing W := IsFractionRing.lift j
  have eK : jK W ≫ spMap f = spMap gK ≫ jK R :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hr : Set.range (jK W ≫ spMap f ≫ ξ) ⊆ Set.range Z.j := by
    have hmor : spMap gK ≫ y ≫ Z.j = jK W ≫ spMap f ≫ ξ := by
      rw [← Category.assoc (jK W), eK, Category.assoc, ← hy]
      rfl
    rintro _ ⟨p, rfl⟩
    refine ⟨(spMap gK ≫ y) p, ?_⟩
    show (spMap gK ≫ y ≫ Z.j) p = _
    rw [hmor]
  obtain ⟨n, hn, hid⟩ := hphi W hW ϖ hϖ (spMap f ≫ ξ) t' mt'' P' hr be' hbe' hmon

  let es : P.D.toPre.X →ₗ[ℤ] P'.D.toPre.X := e.symm.toLinearMap.toAddMonoidHom.toIntLinearMap
  let be : LinearMap.BilinForm ℤ P.D.toPre.X := be'.compl₁₂ es es
  have hbe : ∀ a b, be a b = be' (e.symm a) (e.symm b) := fun _ _ => rfl
  refine ⟨W, inferInstance, inferInstance, inferInstance, hW, ϖ, hϖ, f, hloc, be, fun a b => ?_, fun a => ?_, n, ?_, hid⟩
  · rw [hbe, hbe, hbe'.1]
  · obtain ⟨u, k, hk, hc⟩ := hmon (e.symm a)
    obtain ⟨⟨r, hr0, -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main R P.D hIC a
    obtain ⟨u', hc'⟩ := hcoord (e.symm a) r (by rw [LinearEquiv.apply_symm_apply]; exact hr0)
    obtain ⟨v, hv⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hc hc'
    refine ⟨r, k 0, hr0, by rw [hbe]; exact hk 0, ?_⟩
    have e1 : f r = ((u'⁻¹ * v * u : Wˣ) : W) * ϖ ^ k 0 := by
      have : (u' : W) * f r = v * (u * ϖ ^ k 0) := by simpa using hv
      calc f r = (u'⁻¹ : Wˣ) * ((u' : W) * f r) := by simp
        _ = _ := by rw [this]; push_cast; ring
    rw [e1]
    exact (associated_unit_mul_left _ _ (Units.isUnit _))
  · rw [hn]
    have e2 : φ.evalZ be = φ.evalZ be' :=
      InvFun.eval_equiv φ e.symm (fun a b => ((be' a b : ℤ) : ℝ))
    rw [e2]
    simp only [InvFun.evalZ, InvFun.eval, comb]
    push_cast
    ring

end GlobalTheory.TorRef
