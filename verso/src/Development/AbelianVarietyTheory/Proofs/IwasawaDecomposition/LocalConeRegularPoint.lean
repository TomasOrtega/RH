import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrExtensionEtale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryEtaleStalkUnif
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryEtaleStalkFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightOnePrimeEtaleStalkComapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPointInOpenOfEtale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemAssociatedOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMonomialLevelFormDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsProduct
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegVert
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightComapFlatHeightOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalkStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkSpecializesCompatRingMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvrMapOfCodimOnePrimeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.PeriodUniform

/- English proof (translation)
Establish `h : (Ideal.span {gz ϖz} : Ideal W') = Ideal.span {ι ϖ}`. Establish `e1 : (Ideal.span {gz ϖz} : Ideal W') = (maximalIdeal Rz).map gz`. Rewrite using `[h2, Ideal.map_span, Set.image_singleton]`. Establish `e2 : (Ideal.span {ι ϖ} : Ideal W') = (maximalIdeal W).map ι`. Rewrite using `[h4, Ideal.map_span, Set.image_singleton]`.

Rewrite using `[e1, e2, ← h1, ← h3, Ideal.map_map, Ideal.map_map, hc]`. Conclude with `Ideal.span_singleton_eq_span_singleton.1 h`.
-/
theorem associated_of_map_maximalIdeal {A Rz W W' : Type} [CommRing A] [IsLocalRing A] [CommRing Rz]
    [IsLocalRing Rz] [CommRing W] [IsLocalRing W] [CommRing W'] [IsDomain W'] (φz : A →+* Rz) (ψ : A →+* W)
    (ι : W →+* W') (gz : Rz →+* W') (ϖz : Rz) (ϖ : W) (h1 : (maximalIdeal A).map φz = maximalIdeal Rz)
    (h2 : maximalIdeal Rz = Ideal.span {ϖz}) (h3 : (maximalIdeal A).map ψ = maximalIdeal W)
    (h4 : maximalIdeal W = Ideal.span {ϖ}) (hc : gz.comp φz = ι.comp ψ) : Associated (gz ϖz) (ι ϖ) := by
  have h : (Ideal.span {gz ϖz} : Ideal W') = Ideal.span {ι ϖ} := by
    have e1 : (Ideal.span {gz ϖz} : Ideal W') = (maximalIdeal Rz).map gz := by
      rw [h2, Ideal.map_span, Set.image_singleton]
    have e2 : (Ideal.span {ι ϖ} : Ideal W') = (maximalIdeal W).map ι := by
      rw [h4, Ideal.map_span, Set.image_singleton]
    rw [e1, e2, ← h1, ← h3, Ideal.map_map, Ideal.map_map, hc]
  exact Ideal.span_singleton_eq_span_singleton.1 h

/- English proof (translation)
Establish `hdiag : ∀ y, b y y = b' y y`. Introduce `y`. Take `⟨r, n, hr, hn, ha⟩` from `h y`. Take `⟨r', n', hr', hn', ha'⟩` from `h' y`. Establish `ha'' : Associated (ι (f r')) (ϖ' ^ n')` using `by simpa using ha'`.

Establish `hrr` using `GlobalTheory.TorRef.psiCoord_associated hr hr'`. Establish `h1 : Associated (ϖ' ^ n) (ϖ' ^ n')`. Establish `e1 : Associated (ι (f r)) (ϖ' ^ n)`. Use `(ha.map ι).trans ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Conclude with `hass.pow_pow`. Establish `e2 : Associated (ι (f r)) (ι (f r'))` using `(hrr.map f).map ι`. Conclude with `e1.symm.trans (e2.trans ha'')`. Establish `hne : ϖ' ≠ 0` using `hϖ'.ne_zero`. Establish `hnu : ¬ IsUnit ϖ'` using `hϖ'.not_isUnit`.

Establish `hle1` using `(pow_dvd_pow_iff hne hnu).1 h1.dvd`. Establish `hle2` using `(pow_dvd_pow_iff hne hnu).1 h1.symm.dvd`. Establish `hnn : n = n'` using `le_antisymm hle1 hle2`. Rewrite using `[hn, hn', hnn]`. Use extensionality with `y z`.

Establish `e` using `hdiag (y + z)`. Simplify using `only [map_add, LinearMap.add_apply] at e`. Rewrite `e` using `[hdiag y, hdiag z, hb z y, hb' z y]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_of_formAt {R : Type} [CommRing R] [IsDomain R] (Dg : DegPre R) {W W' : Type} [CommRing W] [CommRing W']
    [IsDomain W'] (f : R →+* W) (ι : W →+* W') (ϖ : W) (ϖ' : W') (hϖ' : Irreducible ϖ') (hass : Associated (ι ϖ) ϖ')
    (b b' : LinearMap.BilinForm ℤ Dg.X) (hb : ∀ y z, b y z = b z y) (hb' : ∀ y z, b' y z = b' z y)
    (h : FormAt Dg f ϖ b) (h' : FormAt Dg (ι.comp f) ϖ' b') : b = b' := by
  have hdiag : ∀ y, b y y = b' y y := by
    intro y
    obtain ⟨r, n, hr, hn, ha⟩ := h y
    obtain ⟨r', n', hr', hn', ha'⟩ := h' y
    have ha'' : Associated (ι (f r')) (ϖ' ^ n') := by simpa using ha'
    have hrr := GlobalTheory.TorRef.psiCoord_associated hr hr'
    have h1 : Associated (ϖ' ^ n) (ϖ' ^ n') := by
      have e1 : Associated (ι (f r)) (ϖ' ^ n) := by
        refine (ha.map ι).trans ?_
        rw [map_pow]
        exact hass.pow_pow
      have e2 : Associated (ι (f r)) (ι (f r')) := (hrr.map f).map ι
      exact e1.symm.trans (e2.trans ha'')
    have hne : ϖ' ≠ 0 := hϖ'.ne_zero
    have hnu : ¬ IsUnit ϖ' := hϖ'.not_isUnit
    have hle1 := (pow_dvd_pow_iff hne hnu).1 h1.dvd
    have hle2 := (pow_dvd_pow_iff hne hnu).1 h1.symm.dvd
    have hnn : n = n' := le_antisymm hle1 hle2
    rw [hn, hn', hnn]
  ext y z
  have e := hdiag (y + z)
  simp only [map_add, LinearMap.add_apply] at e
  rw [hdiag y, hdiag z, hb z y, hb' z y] at e
  linarith

/- English proof (translation)
The claim follows from `φ.eval_comp he (fun a b => (B a b : ℝ))`.
-/
theorem evalZ_compl {E : Type} [Field E] [NumberField E] (φ : InvFun (𝓞 E)) {X X₁ : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup X₁] [Module (𝓞 E) X₁] [Module.Finite (𝓞 E) X₁]
    (e : X →ₗ[𝓞 E] X₁) (he : Function.Surjective e) (B : LinearMap.BilinForm ℤ X₁) :
    φ.evalZ (B.compl₁₂ e.toAddMonoidHom.toIntLinearMap e.toAddMonoidHom.toIntLinearMap) = φ.evalZ B :=
  φ.eval_comp he (fun a b => (B a b : ℝ))

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Z Cn φ hC R _ _ _ ξ t mξ P hCN hEt hFU hTI q hq`. Distinguish the cases in `hex : ∃ (Q : Ideal R) (_ : Q.IsPrime), Q.height = 1 ∧ Q.comap (Scheme.stalkClosedPointTo ξ).hom = q`. Use `swap`. Conclude with `⟨0, fun Q _ hQ1 hQq => (hex ⟨Q, inferInstance, hQ1, hQq⟩).elim⟩`. Take `⟨Q₀, _, hQ₀1, hQ₀q⟩` from `hex`.

Use `haveI : IsDomain (Z.X.presheaf.stalk (ξ (closedPoint R))) := (Z.normal _).1`. Use `haveI : q.IsPrime := by rw [← hQ₀q]; infer_instance`. Establish `hq1 : q.height = 1`. Rewrite using `[← hQ₀q]`. Conclude with `GlobalTheory.T.height_comap_flat_height_one _ hEt.1 Q₀ hQ₀1 (by rw [hQ₀q]; exact hq)`.

Take `⟨z, hs, hdim, hmax, hpt⟩` from `GlobalTheory.T.codim_one_generization_stalk Z.X ξ q hq1`. Take `⟨Rz, _, _, _, ξz, tz, mz, Pz, m, γ, hCNz, hz, hEtz, hFUz, hTIz, -, -⟩` from `hC z`. Substitute `hz` using the available equality. Use `haveI : IsDomain (Z.X.presheaf.stalk (ξz (closedPoint Rz))) := (Z.normal _).1`. Use `haveI : IsIntegrallyClosed (Z.X.presheaf.stalk (ξz (closedPoint Rz))) := (Z.normal _).2`.

Use `haveI := GlobalTheory.DivDescent.isNoetherianRing_stalk Z (ξz (closedPoint Rz))`. Establish `hWz : CDvr Rz` using `GlobalTheory.CdvrExt.cdvr_of_isEtaleCompletion _ hdim hEtz hCNz`. Use `haveI : IsDiscreteValuationRing Rz := hWz.1`. Take `⟨ϖz, hϖz⟩` from `IsDiscreteValuationRing.exists_irreducible Rz`. Establish `hrange` using `GlobalTheory.GenFibre.range_jK_subset_range_j Z ξz hEtz`.

Take `⟨Bz, hBz, hmon⟩` from `GlobalTheory.MonPeriods.exists_isMonomial_levelOne hWz ϖz hϖz tz Pz`. Use `⟨φ.evalZ Bz, fun Q _ hQ1 hQq W _ _ _ hW ϖ hϖ g hinj hunit hπ be hbe hfa => ?_⟩` and prove the remaining obligations. Use `haveI : IsDiscreteValuationRing W := hW.1`. Establish `hCN'` using `hCN`. Take `⟨hNo, hIC, -, -⟩` from `hCN'`.

Establish `hQ0 : Q ≠ ⊥` using `fun e => by rw [e, Ideal.height_bot] at hQ1; exact zero_ne_one hQ1`. Establish `hdvr : IsDiscreteValuationRing (Localization.AtPrime Q)` using `((IsDiscreteValuationRing.TFAE (Localization.AtPrime Q) (IsLocalization.AtPrime.not_isField R hQ0 _)).out 0 1).2 (ReciprocityTheory.ChartRestriction.G.T0.regVert_valuationRing Q hQ1)`. Establish `hU` using `GlobalTheory.T.height_one_prime_etale_stalk_comap Z ξ hCN hEt hFU Q hQ1 (by rw [hQq]; exact hq)`. Take `⟨hWm, hWc⟩` from `GlobalTheory.T.dvr_map_of_codim_one_prime _ Q hdvr hU ϖ hϖ ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ) g hunit hπ`. Rewrite `hWm` using `[hQq]`.

Establish `hχ : (spMap g ≫ ξ) (closedPoint W) = ξz (closedPoint Rz)` using `hpt W g (by rw [← Ideal.comap_comap, hWc, hQq])`. Establish `hzz : (spMap g ≫ ξ) (closedPoint W) ⤳ ξz (closedPoint Rz)` using `by rw [hχ]`. Set `ψ : Z.X.presheaf.stalk (ξz (closedPoint Rz)) →+* W` to `(Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom.comp (Z.X.presheaf.stalkSpecializes hzz).hom`. Establish `hψs : ∀ a, ψ ((Z.X.presheaf.stalkSpecializes hs).hom a) = g ((Scheme.stalkClosedPointTo ξ).hom a)`. Introduce `a`.

Express the relevant statement in the definitionally equal form `(Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom ((Z.X.presheaf.stalkSpecializes hzz).hom ((Z.X.presheaf.stalkSpecializes hs).hom a)) = _`. Rewrite using `[← CommRingCat.comp_apply (Z.X.presheaf.stalkSpecializes hs) (Z.X.presheaf.stalkSpecializes hzz) a, TopCat.Presheaf.stalkSpecializes_comp]`. Conclude with `GlobalTheory.T.stalk_specializes_compat_ring_map Z.X ξ g _ a`. Establish `hψm : (maximalIdeal _).map ψ = maximalIdeal W`. Rewrite using `[← hmax, Ideal.map_map, ← hWm]`.

Use `congr 1`. Use extensionality with `a`. Conclude with `hψs a`. Use `haveI : IsLocalHom ψ := ⟨fun a ha => by`. Assume the negation of the conclusion as `hna`.

Establish `: ψ a ∈ maximalIdeal W` using `hψm ▸ Ideal.mem_map_of_mem ψ ((mem_maximalIdeal a).2 hna)`. Conclude with `(mem_maximalIdeal _).1 this ha⟩`. Take `⟨W', _, _, _, ι, gz, hW', hι, hc⟩` from `GlobalTheory.TraitLift.exists_ringHom_lift_of_isEtaleCompletion (Scheme.stalkClosedPointTo ξz).hom ψ hCNz hEtz hFUz hW inferInstance`. Establish `hass : Associated (gz ϖz) (ι ϖ)` using `associated_of_map_maximalIdeal _ ψ ι gz ϖz ϖ hEtz.2.1 ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖz).1 hϖz) hψm ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ) hc`. Establish `hirr : Irreducible (gz ϖz)` using `hass.symm.irreducible (hι ϖ hϖ)`.

Establish `hcomp : ∀ a, (ι.comp g) ((Scheme.stalkClosedPointTo ξ).hom a) = gz ((Scheme.stalkClosedPointTo ξz).hom ((Z.X.presheaf.stalkSpecializes hs).hom a))`. Introduce `a`. Rewrite using `[← RingHom.comp_apply gz, hc, RingHom.comp_apply ι ψ, hψs]`. Both sides reduce to the same expression. Choose the witnesses or unpack the hypotheses as in `⟨e, he, hfe⟩ : ∃ (e : P.D.toPre.X →ₗ[𝓞 E] Pz.D.toPre.X), Function.Surjective e ∧ FormAt P.D.toPre (ι.comp g) (gz ϖz) (Bz.compl₁₂ e.toAddMonoidHom.toIntLinearMap e.toAddMonoidHom.toIntLinearMap) := by`.

Distinguish the cases in `hxz : ξz (closedPoint Rz) = ξ (closedPoint R)`. Conclude with `GlobalTheory.ChartCentre.exists_surjective_formAt Z ξ t mξ P hCN hEt hFU hTI Rz hWz ϖz hϖz ξz tz mz Pz hrange Bz hBz hmon hs hxz W' gz (ι.comp g) hW' hirr hcomp`. Conclude with `GlobalTheory.T.boundary_etale_stalk_forms Z ξ t mξ P hCN hEt hFU hTI Rz hWz ϖz hϖz ξz tz mz Pz hrange Bz hBz hmon hs hxz hdim W' gz (ι.comp g) hW' hirr hcomp`. Establish `hsymz : ∀ y z, Bz y z = Bz z y` using `((mem_levelForms).1 hBz).1`. Establish `heq` using `eq_of_formAt P.D.toPre g ι ϖ (gz ϖz) hirr hass.symm be _ hbe (fun y z => hsymz _ _) hfa hfe`.

Rewrite using `[heq]`. Conclude with `evalZ_compl φ e he Bz`.
-/
theorem evalZ_const : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)), HasCones Cn Z → ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ∀ q : Ideal (Z.X.presheaf.stalk (ξ (closedPoint R))), q ≠ ⊥ → ∃ cq : ℝ, ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → Q.comap (Scheme.stalkClosedPointTo ξ).hom = q → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ g : R →+* W, Function.Injective g → (∀ r, r ∉ Q → IsUnit (g r)) → (∃ π ∈ Q, Associated (g π) ϖ) → ∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, (∀ y z, be y z = be z y) → FormAt P.D.toPre g ϖ be → φ.evalZ be = cq := by
  intro E _ _ _ H D l Xo c Z Cn φ hC R _ _ _ ξ t mξ P hCN hEt hFU hTI q hq
  classical
  by_cases hex : ∃ (Q : Ideal R) (_ : Q.IsPrime), Q.height = 1 ∧ Q.comap (Scheme.stalkClosedPointTo ξ).hom = q
  swap
  · exact ⟨0, fun Q _ hQ1 hQq => (hex ⟨Q, inferInstance, hQ1, hQq⟩).elim⟩
  obtain ⟨Q₀, _, hQ₀1, hQ₀q⟩ := hex
  haveI : IsDomain (Z.X.presheaf.stalk (ξ (closedPoint R))) := (Z.normal _).1
  haveI : q.IsPrime := by rw [← hQ₀q]; infer_instance
  have hq1 : q.height = 1 := by
    rw [← hQ₀q]
    exact GlobalTheory.T.height_comap_flat_height_one _ hEt.1 Q₀ hQ₀1 (by rw [hQ₀q]; exact hq)
  obtain ⟨z, hs, hdim, hmax, hpt⟩ := GlobalTheory.T.codim_one_generization_stalk Z.X ξ q hq1
  obtain ⟨Rz, _, _, _, ξz, tz, mz, Pz, m, γ, hCNz, hz, hEtz, hFUz, hTIz, -, -⟩ := hC z
  subst hz
  haveI : IsDomain (Z.X.presheaf.stalk (ξz (closedPoint Rz))) := (Z.normal _).1
  haveI : IsIntegrallyClosed (Z.X.presheaf.stalk (ξz (closedPoint Rz))) := (Z.normal _).2
  haveI := GlobalTheory.DivDescent.isNoetherianRing_stalk Z (ξz (closedPoint Rz))
  have hWz : CDvr Rz := GlobalTheory.CdvrExt.cdvr_of_isEtaleCompletion _ hdim hEtz hCNz
  haveI : IsDiscreteValuationRing Rz := hWz.1
  obtain ⟨ϖz, hϖz⟩ := IsDiscreteValuationRing.exists_irreducible Rz
  have hrange := GlobalTheory.GenFibre.range_jK_subset_range_j Z ξz hEtz
  obtain ⟨Bz, hBz, hmon⟩ := GlobalTheory.MonPeriods.exists_isMonomial_levelOne hWz ϖz hϖz tz Pz
  refine ⟨φ.evalZ Bz, fun Q _ hQ1 hQq W _ _ _ hW ϖ hϖ g hinj hunit hπ be hbe hfa => ?_⟩
  haveI : IsDiscreteValuationRing W := hW.1
  have hCN' := hCN
  obtain ⟨hNo, hIC, -, -⟩ := hCN'
  have hQ0 : Q ≠ ⊥ := fun e => by rw [e, Ideal.height_bot] at hQ1; exact zero_ne_one hQ1
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    ((IsDiscreteValuationRing.TFAE (Localization.AtPrime Q)
      (IsLocalization.AtPrime.not_isField R hQ0 _)).out 0 1).2 (ReciprocityTheory.ChartRestriction.G.T0.regVert_valuationRing Q hQ1)
  have hU := GlobalTheory.T.height_one_prime_etale_stalk_comap Z ξ hCN hEt hFU Q hQ1 (by rw [hQq]; exact hq)
  obtain ⟨hWm, hWc⟩ := GlobalTheory.T.dvr_map_of_codim_one_prime _ Q hdvr hU ϖ hϖ
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ) g hunit hπ
  rw [hQq] at hWm
  have hχ : (spMap g ≫ ξ) (closedPoint W) = ξz (closedPoint Rz) :=
    hpt W g (by rw [← Ideal.comap_comap, hWc, hQq])
  have hzz : (spMap g ≫ ξ) (closedPoint W) ⤳ ξz (closedPoint Rz) := by rw [hχ]
  let ψ : Z.X.presheaf.stalk (ξz (closedPoint Rz)) →+* W :=
    (Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom.comp (Z.X.presheaf.stalkSpecializes hzz).hom
  have hψs : ∀ a, ψ ((Z.X.presheaf.stalkSpecializes hs).hom a) = g ((Scheme.stalkClosedPointTo ξ).hom a) := by
    intro a
    change (Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom ((Z.X.presheaf.stalkSpecializes hzz).hom
      ((Z.X.presheaf.stalkSpecializes hs).hom a)) = _
    rw [← CommRingCat.comp_apply (Z.X.presheaf.stalkSpecializes hs) (Z.X.presheaf.stalkSpecializes hzz) a,
      TopCat.Presheaf.stalkSpecializes_comp]
    exact GlobalTheory.T.stalk_specializes_compat_ring_map Z.X ξ g _ a
  have hψm : (maximalIdeal _).map ψ = maximalIdeal W := by
    rw [← hmax, Ideal.map_map, ← hWm]
    congr 1
    ext a
    exact hψs a
  haveI : IsLocalHom ψ := ⟨fun a ha => by
    by_contra hna
    have : ψ a ∈ maximalIdeal W := hψm ▸ Ideal.mem_map_of_mem ψ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 this ha⟩
  obtain ⟨W', _, _, _, ι, gz, hW', hι, hc⟩ := GlobalTheory.TraitLift.exists_ringHom_lift_of_isEtaleCompletion
    (Scheme.stalkClosedPointTo ξz).hom ψ hCNz hEtz hFUz hW inferInstance
  have hass : Associated (gz ϖz) (ι ϖ) := associated_of_map_maximalIdeal _ ψ ι gz ϖz ϖ hEtz.2.1
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖz).1 hϖz) hψm
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ) hc
  have hirr : Irreducible (gz ϖz) := hass.symm.irreducible (hι ϖ hϖ)
  have hcomp : ∀ a, (ι.comp g) ((Scheme.stalkClosedPointTo ξ).hom a) =
      gz ((Scheme.stalkClosedPointTo ξz).hom ((Z.X.presheaf.stalkSpecializes hs).hom a)) := by
    intro a
    rw [← RingHom.comp_apply gz, hc, RingHom.comp_apply ι ψ, hψs]
    rfl
  obtain ⟨e, he, hfe⟩ : ∃ (e : P.D.toPre.X →ₗ[𝓞 E] Pz.D.toPre.X), Function.Surjective e ∧
      FormAt P.D.toPre (ι.comp g) (gz ϖz)
        (Bz.compl₁₂ e.toAddMonoidHom.toIntLinearMap e.toAddMonoidHom.toIntLinearMap) := by
    by_cases hxz : ξz (closedPoint Rz) = ξ (closedPoint R)
    · exact GlobalTheory.ChartCentre.exists_surjective_formAt Z ξ t mξ P hCN hEt hFU hTI Rz hWz ϖz hϖz ξz tz mz Pz hrange
        Bz hBz hmon hs hxz W' gz (ι.comp g) hW' hirr hcomp
    · exact GlobalTheory.T.boundary_etale_stalk_forms Z ξ t mξ P hCN hEt hFU hTI Rz hWz ϖz hϖz ξz tz mz Pz hrange Bz hBz hmon hs hxz hdim W' gz
        (ι.comp g) hW' hirr hcomp
  have hsymz : ∀ y z, Bz y z = Bz z y := ((mem_levelForms).1 hBz).1
  have heq := eq_of_formAt P.D.toPre g ι ϖ (gz ϖz) hirr hass.symm be _ hbe (fun y z => hsymz _ _) hfa hfe
  rw [heq]
  exact evalZ_compl φ e he Bz

end GlobalTheory.PeriodUniform
