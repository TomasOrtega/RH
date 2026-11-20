import Mathlib
import GroundTheory.ArithmeticGeometry.EtaleCompletion.ArtinHenselCompletionNoetherian
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAffineCompletionNormal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAdicCompletionRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

/- English proof (translation)
Introduce `R _ hR M hM hreg`. Set `B` to `AdicCompletion M R`. Establish `hfg : M.FG` using `Ideal.fg_of_isNoetherianRing M`. Establish `: IsLocalRing B` using `adicCompletion_isLocalRing_of_isMaximal M hfg`. Establish `: IsNoetherianRing B` using `GroundTheory.Arith.Etale.isNoetherianRing_adicCompletion R M`.

Establish `hmax : (M.map (algebraMap R B)).IsMaximal` using `AdicCompletion.isMaximal_map_of_le M M le_rfl hfg`. Establish `hmB : M.map (algebraMap R B) = maximalIdeal B` using `IsLocalRing.eq_maximalIdeal hmax`. Establish `hc : (M.map (algebraMap R B)).comap (algebraMap R B) = M` using `(hM.eq_of_le (Ideal.comap_ne_top _ hmax.ne_top) Ideal.le_comap_map).symm`. Establish `hunit : ∀ s : M.primeCompl, IsUnit (algebraMap R B s)`. Introduce `s`.

Assume the negation of the conclusion as `h`. Establish `hs : algebraMap R B s ∈ maximalIdeal B` using `h`. Rewrite `hs` using `[← hmB]`. Establish `hs'` using `Ideal.mem_comap.mpr hs`. Rewrite `hs'` using `[hc]`.

Conclude with `s.2 hs'`. Set `_ : Algebra (Localization.AtPrime M) B` to `(IsLocalization.lift (M := M.primeCompl) (S := Localization.AtPrime M) hunit).toAlgebra`. Establish `: IsScalarTower R (Localization.AtPrime M) B` using `IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq hunit r).symm`. Establish `: Module.Flat (Localization.AtPrime M) B` using `(Module.flat_iff_of_isLocalization (Localization.AtPrime M) M.primeCompl B).mpr inferInstance`. Establish `hmap : (maximalIdeal (Localization.AtPrime M)).map (algebraMap (Localization.AtPrime M) B) = maximalIdeal B`.

Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq, hmB]`. Establish `: IsLocalHom (algebraMap (Localization.AtPrime M) B)`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `h1 : algebraMap (Localization.AtPrime M) B a ∈ maximalIdeal B` using `hmap ▸ Ideal.mem_map_of_mem _ (show a ∈ maximalIdeal (Localization.AtPrime M) from h)`.

Conclude with `h1 ha`. Conclude with `GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap`.
-/
theorem AdicCompletionRegular.proof : AdicCompletionRegular.Statement := by
  intro R _ hR M hM hreg
  let B := AdicCompletion M R
  have hfg : M.FG := Ideal.fg_of_isNoetherianRing M
  have : IsLocalRing B := adicCompletion_isLocalRing_of_isMaximal M hfg
  have : IsNoetherianRing B := GroundTheory.Arith.Etale.isNoetherianRing_adicCompletion R M
  have hmax : (M.map (algebraMap R B)).IsMaximal := AdicCompletion.isMaximal_map_of_le M M le_rfl hfg
  have hmB : M.map (algebraMap R B) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hmax
  have hc : (M.map (algebraMap R B)).comap (algebraMap R B) = M :=
    (hM.eq_of_le (Ideal.comap_ne_top _ hmax.ne_top) Ideal.le_comap_map).symm
  have hunit : ∀ s : M.primeCompl, IsUnit (algebraMap R B s) := by
    intro s
    by_contra h
    have hs : algebraMap R B s ∈ maximalIdeal B := h
    rw [← hmB] at hs
    have hs' := Ideal.mem_comap.mpr hs
    rw [hc] at hs'
    exact s.2 hs'
  let _ : Algebra (Localization.AtPrime M) B :=
    (IsLocalization.lift (M := M.primeCompl) (S := Localization.AtPrime M) hunit).toAlgebra
  have : IsScalarTower R (Localization.AtPrime M) B :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq hunit r).symm
  have : Module.Flat (Localization.AtPrime M) B :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime M) M.primeCompl B).mpr inferInstance
  have hmap : (maximalIdeal (Localization.AtPrime M)).map (algebraMap (Localization.AtPrime M) B) =
      maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq, hmB]
  have : IsLocalHom (algebraMap (Localization.AtPrime M) B) := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have h1 : algebraMap (Localization.AtPrime M) B a ∈ maximalIdeal B :=
      hmap ▸ Ideal.mem_map_of_mem _ (show a ∈ maximalIdeal (Localization.AtPrime M) from h)
    exact h1 ha
  exact GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
