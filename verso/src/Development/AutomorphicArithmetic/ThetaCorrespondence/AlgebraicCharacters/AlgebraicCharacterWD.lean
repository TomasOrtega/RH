import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.EmbOrbit
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.ContinuousRankOneRep
import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.ChIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
open UpperTheory.Lit.CharWD GlobalTheory.Published
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands UpperTheory.V.W

/- English proof (translation)
Introduce `hG hD hP E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ _ hμ hL w A h O _ _ _ Bw hj ξ hξ a ha`. Establish `hc : Continuous (μ.comp (Dec (F` using `E) A).subtype) := hμ.comp continuous_subtype_val`. Take `⟨η, hη, eη⟩` from `locWD hG hD hP ι h Bw hj a ha _ hc _ (UpperTheory.V.Loc.laHecke h art hart ι χ n μ hL ⟨a, ha⟩)`. Take `⟨-, hs, e⟩` from `chIndep P AI hT ι h Bw hj _ η hc hη`. Take `⟨ξ₀, -, hu, -⟩` from `GlobalTheory.HeckeComp.main E χ w`.

Establish `hx : ξ = χ.loc w` using `(hu ξ hξ).trans (hu _ ⟨GlobalTheory.HeckeComp.smooth_loc χ w, fun _ => rfl⟩).symm`. Use `haveI : Finite (Emb l w) := finite_contEmb w`. Establish `key : (Units.map ι.toRingHom.toMonoidHom).comp η = ξ.comp a`. Use `MonoidHom.ext fun σ => Units.ext ?_` and prove the remaining obligations. Establish `h1` using `hL.loc (a σ) _ (ha.glob art hart σ)`.

Establish `h2 : locPow ι n w (a σ) * ∏ᶠ τ : Emb l w, τ.1 (a σ : w.adicCompletion E) ^ (-n ((ι.toRingHom.comp τ.1).comp (algebraMap E (w.adicCompletion E)))) = 1`. Unfold `locPow`. Rewrite using `[← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]`. Use `finprod_eq_one_of_forall_eq_one fun τ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ ((map_ne_zero τ.1).2 (Units.ne_zero _))]`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `ι (η σ : Qbar l) = (ξ (a σ) : ℂ)`. Rewrite using `[eη]`. Express the relevant statement in the definitionally equal form `ι ((μ (σ : G E Ω) : Qbar l) * _) = _`. Rewrite using `[h1, mul_assoc, h2, mul_one, RingEquiv.apply_symm_apply, hx]`.

Use `(e : _ = _).trans ?_` and prove the remaining obligations. Use `congr 1`.
-/
theorem UpperTheory.Lit.CharWD.algebraicCharacterWD :
    GlobalArtinReciprocity → HeckeLAdicCharacterDeRham → DeRhamPotSemistable → AlgebraicCharacterWD := by
  intro hG hD hP E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ _ hμ hL w A h O _ _ _ Bw hj ξ hξ a ha
  have hc : Continuous (μ.comp (Dec (F := E) A).subtype) := hμ.comp continuous_subtype_val
  obtain ⟨η, hη, eη⟩ := locWD hG hD hP ι h Bw hj a ha _ hc _ (UpperTheory.V.Loc.laHecke h art hart ι χ n μ hL ⟨a, ha⟩)
  obtain ⟨-, hs, e⟩ := chIndep P AI hT ι h Bw hj _ η hc hη
  obtain ⟨ξ₀, -, hu, -⟩ := GlobalTheory.HeckeComp.main E χ w
  have hx : ξ = χ.loc w := (hu ξ hξ).trans (hu _ ⟨GlobalTheory.HeckeComp.smooth_loc χ w, fun _ => rfl⟩).symm
  haveI : Finite (Emb l w) := finite_contEmb w
  have key : (Units.map ι.toRingHom.toMonoidHom).comp η = ξ.comp a := by
    refine MonoidHom.ext fun σ => Units.ext ?_
    have h1 := hL.loc (a σ) _ (ha.glob art hart σ)
    have h2 : locPow ι n w (a σ) * ∏ᶠ τ : Emb l w, τ.1 (a σ : w.adicCompletion E) ^
        (-n ((ι.toRingHom.comp τ.1).comp (algebraMap E (w.adicCompletion E)))) = 1 := by
      unfold locPow
      rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
      refine finprod_eq_one_of_forall_eq_one fun τ => ?_
      rw [← zpow_add₀ ((map_ne_zero τ.1).2 (Units.ne_zero _))]
      simp
    change ι (η σ : Qbar l) = (ξ (a σ) : ℂ)
    rw [eη]
    change ι ((μ (σ : G E Ω) : Qbar l) * _) = _
    rw [h1, mul_assoc, h2, mul_one, RingEquiv.apply_symm_apply, hx]
  refine (e : _ = _).trans ?_
  congr 1
