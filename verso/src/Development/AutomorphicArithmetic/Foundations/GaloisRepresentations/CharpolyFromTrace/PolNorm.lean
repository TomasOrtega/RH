import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.NumberField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PolarizedPairSatakeParameterConjugatePlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PolOfSatOfThetaSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharNormDescentStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnderStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EventuallyCofiniteUnderOfEventuallyCofinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormVEqNormVUnderPowStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

/- English proof (translation)
Take `⟨χ', hs, hN⟩` from `GlobalTheory.T.hecke_char_norm_descent K M a χ hpol.sign`. Use `⟨χ', ⟨hs, ?_⟩, hN⟩` and prove the remaining obligations. Apply `UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hjs hgk M a ha π' (compNorm M χ')` to reduce the goal to its premises. Establish `hT` using `GlobalTheory.PolarizedSat.hasSat_conjPlace GlobalTheory.automorphicFormsFiniteGL K a π χ hpol`. Establish `hU : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (compNorm K χ).UnrAt v` using `Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified _)`.

Establish `hT'` using `GlobalTheory.T.eventually_cofinite_under_of_eventually_cofinite_places K M _ (hT.and hU)`. Establish `hbc'` using `(conjSrc_injective (IsCMField.complexConj M).toRingEquiv).tendsto_cofinite.eventually hbc`. Use `filter_upwards [hT', hbc, hbc'] with w ⟨hTw, hUw⟩ hw hcw`. Take `⟨f, hf⟩` from `GlobalTheory.T.exists_normV_eq_normV_under_pow K M w`. Take `⟨hu', hval⟩` from `GlobalTheory.T.unramifiedAt_value_heckeChar_comp_ideleNorm K M (compNorm K χ) (compNorm M χ') hN w f hf hUw`.

Use `⟨hu', ?_⟩` and prove the remaining obligations. Take `⟨B, hB1, hB2⟩` from `hw f hf`. Establish `hcu` using `GlobalTheory.T.under_conjugatePlace_eq_conjugatePlace_under K M w`. Establish `hnc : normV (UpperTheory.V.Af.Bc.cPl w) = normV ((UpperTheory.V.Af.Bc.cPl w).under (𝓞 K)) ^ f`. Rewrite using `[hcu]`.

Establish `e1 : normV (UpperTheory.V.Af.Bc.cPl w) = normV w` using `GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc _ w`. Establish `e2 : normV (UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K))) = normV (w.under (𝓞 K))` using `GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc _ _`. Rewrite using `[e1, e2, hf]`. Take `⟨C, hC1, hC2⟩` from `hcw f hnc`. Rewrite `hC1` using `[hcu]`.

Establish `e` using `GlobalTheory.T.cuspRep_satakeParameters_unique K a (CG.mk π) _ _ _ hC1 (hTw B hB1)`. Use `⟨_, _, hB2, hC2, ?_⟩` and prove the remaining obligations. Rewrite using `[e, hval]`. Simplify using `only [Multiset.map_map]`. Use `Multiset.map_congr rfl fun α _ => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, mul_pow, inv_pow, mul_inv, inv_inv]`.
-/
private theorem pol_norm (hjs : GlobalTheory.Published.JacquetShalikaRigidity) (hgk : GlobalTheory.Published.GelfandKazhdanDual)
    (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M]
    [IsCMField M] [Algebra K M] (a : ℕ) (ha : 1 ≤ a) (π : CuspSub K a) (π' : CuspSub M a) (χ : HChar (maximalRealSubfield K))
    (hpol : GlobalTheory.ContraPair.PolarizedPair π χ) (hbc : UpperTheory.V.Published.WeakBC (CG.mk π).HasSat (CG.mk π').HasSat) :
    ∃ χ' : HChar (maximalRealSubfield M), GlobalTheory.ContraPair.PolarizedPair π' χ' ∧
      ∀ x : Ideles M, (compNorm M χ').1 x = (compNorm K χ).1 (GroundTheory.Global.ideleNorm K M x) := by
  obtain ⟨χ', hs, hN⟩ := GlobalTheory.T.hecke_char_norm_descent K M a χ hpol.sign
  refine ⟨χ', ⟨hs, ?_⟩, hN⟩
  apply UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse hjs hgk M a ha π' (compNorm M χ')
  have hT := GlobalTheory.PolarizedSat.hasSat_conjPlace GlobalTheory.automorphicFormsFiniteGL K a π χ hpol
  have hU : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (compNorm K χ).UnrAt v :=
    Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified _)
  have hT' := GlobalTheory.T.eventually_cofinite_under_of_eventually_cofinite_places K M _ (hT.and hU)
  have hbc' := (conjSrc_injective (IsCMField.complexConj M).toRingEquiv).tendsto_cofinite.eventually hbc
  filter_upwards [hT', hbc, hbc'] with w ⟨hTw, hUw⟩ hw hcw
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_normV_eq_normV_under_pow K M w
  obtain ⟨hu', hval⟩ := GlobalTheory.T.unramifiedAt_value_heckeChar_comp_ideleNorm K M (compNorm K χ) (compNorm M χ') hN w f hf hUw
  refine ⟨hu', ?_⟩
  obtain ⟨B, hB1, hB2⟩ := hw f hf
  have hcu := GlobalTheory.T.under_conjugatePlace_eq_conjugatePlace_under K M w
  have hnc : normV (UpperTheory.V.Af.Bc.cPl w) = normV ((UpperTheory.V.Af.Bc.cPl w).under (𝓞 K)) ^ f := by
    rw [hcu]
    have e1 : normV (UpperTheory.V.Af.Bc.cPl w) = normV w := GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc _ w
    have e2 : normV (UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K))) = normV (w.under (𝓞 K)) :=
      GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc _ _
    rw [e1, e2, hf]
  obtain ⟨C, hC1, hC2⟩ := hcw f hnc
  rw [hcu] at hC1
  have e := GlobalTheory.T.cuspRep_satakeParameters_unique K a (CG.mk π) _ _ _ hC1 (hTw B hB1)
  refine ⟨_, _, hB2, hC2, ?_⟩
  rw [e, hval]
  simp only [Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, mul_pow, inv_pow, mul_inv, inv_inv]

/- English proof (translation)
Introduce `hjs hgk K M _ _ _ _ _ _ _ a ha π P χ hpol hbc`. Take `⟨χ', hχ', hN⟩` from `pol_norm hjs hgk K M a ha π P χ hpol hbc`. Use `⟨⟨χ', hχ'⟩, fun hq => ?_⟩` and prove the remaining obligations. Establish `h1 : compNorm M χ' = 1`. Use `Subtype.ext (MonoidHom.ext fun x => ?_)` and prove the remaining obligations.

Rewrite using `[hN x, hq, map_pow, compNorm_quadChar, one_pow]`. Both sides reduce to the same expression. Use `⟨fun v => ?_, ?_⟩` and prove the remaining obligations. Establish `e : (quadChar M ^ a).locInf v (-1) = (quadChar M).locInf v (-1) ^ a` using `rfl`. Rewrite using `[e, quadChar_locInf]`.

Rewrite using `[map_pow, compNorm_quadChar, one_pow]`. Establish `h` using `hχ'.dual`. Rewrite `h` using `[h1]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Gal.NearKilling.polBC :
    GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual → PolBC := by
  intro hjs hgk K M _ _ _ _ _ _ _ a ha π P χ hpol hbc
  obtain ⟨χ', hχ', hN⟩ := pol_norm hjs hgk K M a ha π P χ hpol hbc
  refine ⟨⟨χ', hχ'⟩, fun hq => ?_⟩
  have h1 : compNorm M χ' = 1 := by
    refine Subtype.ext (MonoidHom.ext fun x => ?_)
    rw [hN x, hq, map_pow, compNorm_quadChar, one_pow]
    rfl
  refine ⟨fun v => ?_, ?_⟩
  · have e : (quadChar M ^ a).locInf v (-1) = (quadChar M).locInf v (-1) ^ a := rfl
    rw [e, quadChar_locInf]
  · rw [map_pow, compNorm_quadChar, one_pow]
    have h := hχ'.dual
    rwa [h1] at h
