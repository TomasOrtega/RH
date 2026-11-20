import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.HodgeTateFromSandwich
import GroundTheory.AutomorphicForms.GL2.GJStandardLDual
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace

open NumberField IsDedekindDomain MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet GroundTheory.Automorphic.GJStandardL
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

/- English proof (translation)
Introduce `hL hC hS K _ _ n _ v V _ _ π s hs`. Establish `hirr : π.IsIrreducible` using `hs.isIrreducible`. Establish `hsm : IsSmooth π` using `hs.isSmooth`. Establish `hψ` using `GroundTheory.Global.continuous_localAdelicChar (K := K) v`. Establish `hψ1` using `GroundTheory.Global.localAdelicChar_ne_one (K := K) v`.

Take `⟨β, W, _, _, σ, hσirr, hσs, hσc, hσa, ι, hι⟩` from `exists_embedding_parabolicInd (π := π) hsm`. Take `⟨γ, hγ⟩` from `exists_leviFE hσa hσc (inducedChar β) continuous_inducedChar (leviMeasure β (GroundTheory.Global.localAdelicChar K v)) hψ hψ1`. Take `⟨P, c, j, h0, hd, hc, hγ'⟩` from `hL _ n β W σ hσa hσirr hσc _ continuous_inducedChar _ _ hψ hψ1 γ hγ`. Use `⟨P, c, j, h0, ?_, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[hd]`.

Conclude with `(hS _ n V π s hs β W σ hσa hσirr hσc ι hι).symm`. Rewrite using `[← GroundTheory.Global.residueCard_adicCompletion, ← hγ']`. Conclude with `hC _ n V π hsm β W σ hσs ι hι _ _ hψ hψ1 γ (inducedFE_of_leviFE _ hψ hψ1 hγ)`.
-/
theorem UpperTheory.V.Z.Gam.gamLocOf :
    UpperTheory.V.Z.Gam.GamLocOf := by
  intro hL hC hS K _ _ n _ v V _ _ π s hs
  have hirr : π.IsIrreducible := hs.isIrreducible
  have hsm : IsSmooth π := hs.isSmooth
  have hψ := GroundTheory.Global.continuous_localAdelicChar (K := K) v
  have hψ1 := GroundTheory.Global.localAdelicChar_ne_one (K := K) v
  obtain ⟨β, W, _, _, σ, hσirr, hσs, hσc, hσa, ι, hι⟩ := exists_embedding_parabolicInd (π := π) hsm
  obtain ⟨γ, hγ⟩ := exists_leviFE hσa hσc (inducedChar β) continuous_inducedChar
    (leviMeasure β (GroundTheory.Global.localAdelicChar K v)) hψ hψ1
  obtain ⟨P, c, j, h0, hd, hc, hγ'⟩ := hL _ n β W σ hσa hσirr hσc _ continuous_inducedChar _ _ hψ hψ1 γ hγ
  refine ⟨P, c, j, h0, ?_, hc, ?_⟩
  · rw [hd]
    exact (hS _ n V π s hs β W σ hσa hσirr hσc ι hι).symm
  · rw [← GroundTheory.Global.residueCard_adicCompletion, ← hγ']
    exact hC _ n V π hsm β W σ hσs ι hι _ _ hψ hψ1 γ (inducedFE_of_leviFE _ hψ hψ1 hγ)
