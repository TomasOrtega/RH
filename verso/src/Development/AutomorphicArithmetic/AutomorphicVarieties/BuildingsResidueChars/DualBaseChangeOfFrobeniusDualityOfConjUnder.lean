import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

/- English proof (translation)
Introduce `hF hU K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r π sat' huniq hbc hatt μ χ c P hL hc hpair`. Take `⟨j, hj⟩` from `hc`. Set `c' : G (maximalRealSubfield M) Ω` to `AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by`. Apply `j.injective` to reduce the goal to its premises. Use `(hj _).trans ?_` and prove the remaining obligations.

Conclude with `(mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap M Ω))`. Establish `hpair' : IsPairing c' (r.comp (resG K M Ω)) (cycBar M Ω l ^ (1 - (n : ℤ)) * (μ.comp (resG (maximalRealSubfield K) K Ω)).comp (resG K M Ω)) P` using `fun s s' hs => hpair (resG K M Ω s) (resG K M Ω s') (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)`. Establish `h0 : Ideal.span {((l : ℕ) : 𝓞 M)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `(Fact.out : l.Prime).ne_zero` after adjusting the coercions.

Establish `hl : ∀ᶠ v : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ((l : ℕ) : 𝓞 M) ∉ v.asIdeal` using `(Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)`. Establish `ht` using `(conjSrc_injective (IsCMField.complexConj M).toRingEquiv).tendsto_cofinite`. Use `filter_upwards [hbc, ht.eventually hbc, hatt.2, ht.eventually hatt.2, hl, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually (Bc.normGal K Ω l ι χ μ hL)] with w h1 h2 ⟨C, hC, hE⟩ ⟨C', hC', hE'⟩ hw ⟨hu, he⟩ f hf`. Take `⟨e1, e2, -⟩` from `hU K M w`. Take `⟨-, e3, -⟩` from `hU K K (w.under (𝓞 K))`.

Take `⟨B, hB, hs⟩` from `h1 f hf`. Take `⟨B', hB', hs'⟩` from `h2 f (by`. Express the relevant statement in the definitionally equal form `normV (cPl w) = normV ((cPl w).under (𝓞 K)) ^ f`. Rewrite using `[e2, e1, e3, hf])`. Take `rfl` from `huniq _ _ _ hs hC`.

Take `rfl` from `huniq _ _ _ hs' hC'`. Establish `he'` using `(UpperTheory.frobenius_power_compatibility K M Ω l ι w f hf).2 _ _ he`. Rewrite `he'` using `[← Units.val_pow_eq_pow_val]`. Establish `key` using `hF M Ω l ι n _ _ c' P ⟨j, hj⟩ hpair' w hw _ _ _ hE hE' he'`. Establish `hB'' : (CG.mk π).HasSat (cPl (w.under (𝓞 K))) B'` using `e1 ▸ hB'`.

Establish `hT` using `UpperTheory.theta_satake_parameters_inverse K n π _ _ hB''`. Rewrite `hT` using `[CG.hasSat_mk]`. Use `⟨_, (CG.hasSat_mk ..).2 (GlobalTheory.SphGal.hasSatGL_twist K n _ (compNorm K χ) _ _ hu hT), ?_⟩` and prove the remaining obligations. Use `hs using 1` and compare the differences between its conclusion and the goal. Establish `k2` using `congrArg (Multiset.map (· * (compNorm K χ).val (w.under (𝓞 K)) ^ f)) key`.

Simplify using `only [Multiset.map_map, Function.comp_def, inv_mul_cancel_right] at k2 ⊢`. Rewrite using `[← k2]`. Simplify using `only [mul_pow, inv_pow]`.
-/
theorem UpperTheory.dualBaseChange_of_frobeniusDuality_of_conjUnder :
    UpperTheory.V.Af.Sol.FrobDualC → UpperTheory.V.Af.Sol.ConjUnder → UpperTheory.V.Af.Sol.DualBcC := by
  intro hF hU K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r π sat' huniq hbc hatt μ χ c P hL hc hpair
  obtain ⟨j, hj⟩ := hc
  let c' : G (maximalRealSubfield M) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap M Ω))
  have hpair' : IsPairing c' (r.comp (resG K M Ω)) (cycBar M Ω l ^ (1 - (n : ℤ)) *
      (μ.comp (resG (maximalRealSubfield K) K Ω)).comp (resG K M Ω)) P := fun s s' hs =>
    hpair (resG K M Ω s) (resG K M Ω s') (AlgEquiv.ext fun x => DFunLike.congr_fun hs x)
  have h0 : Ideal.span {((l : ℕ) : 𝓞 M)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ((l : ℕ) : 𝓞 M) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have ht := (conjSrc_injective (IsCMField.complexConj M).toRingEquiv).tendsto_cofinite
  filter_upwards [hbc, ht.eventually hbc, hatt.2, ht.eventually hatt.2, hl,
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually (Bc.normGal K Ω l ι χ μ hL)]
    with w h1 h2 ⟨C, hC, hE⟩ ⟨C', hC', hE'⟩ hw ⟨hu, he⟩ f hf
  obtain ⟨e1, e2, -⟩ := hU K M w
  obtain ⟨-, e3, -⟩ := hU K K (w.under (𝓞 K))
  obtain ⟨B, hB, hs⟩ := h1 f hf
  obtain ⟨B', hB', hs'⟩ := h2 f (by
    change normV (cPl w) = normV ((cPl w).under (𝓞 K)) ^ f
    rw [e2, e1, e3, hf])
  obtain rfl := huniq _ _ _ hs hC
  obtain rfl := huniq _ _ _ hs' hC'
  have he' := (UpperTheory.frobenius_power_compatibility K M Ω l ι w f hf).2 _ _ he
  rw [← Units.val_pow_eq_pow_val] at he'
  have key := hF M Ω l ι n _ _ c' P ⟨j, hj⟩ hpair' w hw _ _ _ hE hE' he'
  have hB'' : (CG.mk π).HasSat (cPl (w.under (𝓞 K))) B' := e1 ▸ hB'
  have hT := UpperTheory.theta_satake_parameters_inverse K n π _ _ hB''
  rw [CG.hasSat_mk] at hT
  refine ⟨_, (CG.hasSat_mk ..).2 (GlobalTheory.SphGal.hasSatGL_twist K n _ (compNorm K χ) _ _ hu hT), ?_⟩
  convert hs using 1
  have k2 := congrArg (Multiset.map (· * (compNorm K χ).val (w.under (𝓞 K)) ^ f)) key
  simp only [Multiset.map_map, Function.comp_def, inv_mul_cancel_right] at k2 ⊢
  rw [← k2]
  simp only [mul_pow, inv_pow]
