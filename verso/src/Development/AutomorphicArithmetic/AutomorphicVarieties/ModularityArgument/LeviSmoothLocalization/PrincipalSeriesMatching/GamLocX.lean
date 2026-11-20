import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxLevi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.CoefInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralLaurentExpansion
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralShellMean
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralTateComparison
import GroundTheory.AutomorphicForms.GL2.GJStandardLDual
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace

open NumberField IsDedekindDomain MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet GroundTheory.Automorphic.GJStandardL UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

/- English proof (translation)
Establish `hML : leviModulus β (blockUnif F a) = leviAbsDet β (blockUnif F a)`. Rewrite using `[← leviEquivPi_symm_mulSingle (F := F) a]`. Use `set x : (b : Set.range β) → GL (Fin (blockSize β b)) F := Pi.mulSingle a (centralUnif F (blockSize β a)) with hx`. Establish `hC : ((leviAbsDet β ((leviEquivPi F β).symm x) : ℝ≥0) : ℂ) = ∏ b, detPow (x b) 1`. Rewrite using `[← detPow_leviEquivPi_symm, detPow_eq_cpow, Complex.cpow_one]`.

Both sides reduce to the same expression. Rewrite using `[Finset.prod_eq_single a (fun b _ hb => by`. Rewrite using `[hx, Pi.mulSingle_eq_of_ne hb]`. Conclude with `detPow_of_mem_integralGL (one_mem _) 1) (by simp), detPow_eq_cpow, Complex.cpow_one] at hC`. Rewrite using `[leviModulus_leviEquivPi_symm, Finset.prod_eq_single a]`.

Rewrite using `[detModulusPow] conv_lhs => arg 2`. Rewrite using `[ha]`. Rewrite using `[pow_one]`. Conclude with `hC.symm` after adjusting the coercions. Introduce `b _ hb`.

Rewrite using `[hx, Pi.mulSingle_eq_of_ne hb, detModulusPow]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use `set m := blockUnif F a`. Establish `key` using `leviRatio_sq_mul_modular_mul_det m`.

Rewrite `key` using `[hML]`. Establish `hD : 0 < leviAbsDet β m` using `modulus_det_pos _`. Establish `hsq : inducedChar β m ^ 2 = 1`. Establish `e : inducedChar β m = leviRatio β m * NNReal.sqrt (MeasureTheory.Measure.modularCharacter (leviIncl m)) * leviAbsDet β m ^ (((n : ℝ) - 1) / 2)` using `rfl`. Rewrite using `[e, mul_pow, mul_pow, NNReal.sq_sqrt, ← NNReal.rpow_natCast (leviAbsDet β m ^ (((n : ℝ) - 1) / 2)), ← NNReal.rpow_mul]`.

Establish `h2 : ((n : ℝ) - 1) / 2 * ((2 : ℕ) : ℝ) = (n : ℝ) - 1` using `by push_cast; ring`. Rewrite using `[h2]`. Apply `mul_right_cancel₀ hD.ne'` to reduce the goal to its premises. Rewrite using `[one_mul]`. Use `conv_rhs => rw [← key]`.

Rewrite using `[mul_assoc, ← NNReal.rpow_add_one hD.ne', sub_add_cancel, NNReal.rpow_natCast]`. Conclude with `(pow_left_inj₀ (by positivity) zero_le_one two_ne_zero).1 (by rw [hsq, one_pow])`.
-/
private theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.kappa_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] {n : ℕ} {β : Fin n → ℕ} (a : Set.range β) (ha : blockSize β a = 1) :
    inducedChar β (blockUnif F a) = 1 := by
  have hML : leviModulus β (blockUnif F a) = leviAbsDet β (blockUnif F a) := by
    rw [← leviEquivPi_symm_mulSingle (F := F) a]
    set x : (b : Set.range β) → GL (Fin (blockSize β b)) F := Pi.mulSingle a (centralUnif F (blockSize β a)) with hx
    have hC : ((leviAbsDet β ((leviEquivPi F β).symm x) : ℝ≥0) : ℂ) = ∏ b, detPow (x b) 1 := by
      rw [← detPow_leviEquivPi_symm, detPow_eq_cpow, Complex.cpow_one]
      rfl
    rw [Finset.prod_eq_single a (fun b _ hb => by
        rw [hx, Pi.mulSingle_eq_of_ne hb]
        exact detPow_of_mem_integralGL (one_mem _) 1) (by simp), detPow_eq_cpow, Complex.cpow_one] at hC
    rw [leviModulus_leviEquivPi_symm, Finset.prod_eq_single a]
    · rw [detModulusPow]
      conv_lhs => arg 2; rw [ha]
      rw [pow_one]
      exact_mod_cast hC.symm
    · intro b _ hb
      rw [hx, Pi.mulSingle_eq_of_ne hb, detModulusPow]
      simp
    · simp
  set m := blockUnif F a
  have key := leviRatio_sq_mul_modular_mul_det m
  rw [hML] at key
  have hD : 0 < leviAbsDet β m := modulus_det_pos _
  have hsq : inducedChar β m ^ 2 = 1 := by
    have e : inducedChar β m = leviRatio β m * NNReal.sqrt (MeasureTheory.Measure.modularCharacter (leviIncl m)) *
        leviAbsDet β m ^ (((n : ℝ) - 1) / 2) := rfl
    rw [e, mul_pow, mul_pow, NNReal.sq_sqrt, ← NNReal.rpow_natCast (leviAbsDet β m ^ (((n : ℝ) - 1) / 2)),
      ← NNReal.rpow_mul]
    have h2 : ((n : ℝ) - 1) / 2 * ((2 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast; ring
    rw [h2]
    apply mul_right_cancel₀ hD.ne'
    rw [one_mul]
    conv_rhs => rw [← key]
    rw [mul_assoc, ← NNReal.rpow_add_one hD.ne', sub_add_cancel, NNReal.rpow_natCast]
  exact (pow_left_inj₀ (by positivity) zero_le_one two_ne_zero).1 (by rw [hsq, one_pow])

/- English proof (translation)
Introduce `K _ _ n hn v V _ _ π s hs`. Use `haveI := hs.isIrreducible`. Take `⟨β, W, _, _, σ, hirr, hsm, hcusp, hadm, Φ, hinj⟩` from `exists_embedding_parabolicInd hs.isSmooth`. Use `letI : MeasurableSpace (levi (HeightOneSpectrum.adicCompletion K v) n β) := borel _`. Use `haveI : BorelSpace (levi (HeightOneSpectrum.adicCompletion K v) n β) := ⟨rfl⟩`.

Use `haveI := hirr`. Take `⟨ω, hω⟩` from `exists_blockChar (σ := σ) hsm`. Establish `hB` using `gxBlock_of UpperTheory.local_zeta_integral_laurent_expansion UpperTheory.local_zeta_integral_shell_mean UpperTheory.local_zeta_integral_tate_comparison`. Establish `hψc` using `GroundTheory.Global.continuous_localAdelicChar (K := K) v`. Establish `hψ1` using `GroundTheory.Global.localAdelicChar_ne_one (K := K) v`.

Take `⟨γ, hshape, hFE⟩` from `gxLevi hB hadm hcusp (inducedChar β) continuous_inducedChar (leviMeasure β (GroundTheory.Global.localAdelicChar K v)) hψc hψ1 hω`. Establish `hInd` using `inducedFE_of_leviFE (localHaar n v) hψc hψ1 hFE`. Establish `hG` using `coefInd _ n V π hs.isSmooth β W σ hsm Φ hinj (localHaar n v) _ hψc hψ1 γ hInd`. Establish `hpolF : polF σ (fun a => ((inducedChar β (blockUnif (HeightOneSpectrum.adicCompletion K v) a) : ℝ≥0) : ℂ) * ω a) = polF σ ω`. Unfold `polF`.

Use `Finset.prod_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Use `split_ifs with h`. Use `beta_reduce`. Rewrite using `[kappa_one a h.1]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Establish `hpol` using `gxSupp hs hirr hcusp Φ hinj hω`. Rewrite `hshape` using `[hpolF, GroundTheory.Global.residueCard_adicCompletion]`. Take `⟨c, j, hc, hγ⟩` from `hshape`. Use `⟨c, j, hc, ?_⟩` and prove the remaining obligations.

Rewrite using `[hpol, ← hγ]`. Conclude with `hG`.
-/
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.gamLocX :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.GamLocX := by
  intro K _ _ n hn v V _ _ π s hs
  haveI := hs.isIrreducible
  obtain ⟨β, W, _, _, σ, hirr, hsm, hcusp, hadm, Φ, hinj⟩ := exists_embedding_parabolicInd hs.isSmooth
  letI : MeasurableSpace (levi (HeightOneSpectrum.adicCompletion K v) n β) := borel _
  haveI : BorelSpace (levi (HeightOneSpectrum.adicCompletion K v) n β) := ⟨rfl⟩
  haveI := hirr
  obtain ⟨ω, hω⟩ := exists_blockChar (σ := σ) hsm
  have hB := gxBlock_of UpperTheory.local_zeta_integral_laurent_expansion UpperTheory.local_zeta_integral_shell_mean UpperTheory.local_zeta_integral_tate_comparison
  have hψc := GroundTheory.Global.continuous_localAdelicChar (K := K) v
  have hψ1 := GroundTheory.Global.localAdelicChar_ne_one (K := K) v
  obtain ⟨γ, hshape, hFE⟩ := gxLevi hB hadm hcusp (inducedChar β) continuous_inducedChar
    (leviMeasure β (GroundTheory.Global.localAdelicChar K v)) hψc hψ1 hω
  have hInd := inducedFE_of_leviFE (localHaar n v) hψc hψ1 hFE
  have hG := coefInd _ n V π hs.isSmooth β W σ hsm Φ hinj (localHaar n v) _ hψc hψ1 γ hInd
  have hpolF : polF σ (fun a => ((inducedChar β (blockUnif (HeightOneSpectrum.adicCompletion K v) a) : ℝ≥0) : ℂ) * ω a)
      = polF σ ω := by
    unfold polF
    refine Finset.prod_congr rfl (fun a _ => ?_)
    split_ifs with h
    · beta_reduce
      rw [kappa_one a h.1]
      simp
    · rfl
  have hpol := gxSupp hs hirr hcusp Φ hinj hω
  rw [hpolF, GroundTheory.Global.residueCard_adicCompletion] at hshape
  obtain ⟨c, j, hc, hγ⟩ := hshape
  refine ⟨c, j, hc, ?_⟩
  rw [hpol, ← hγ]
  exact hG
