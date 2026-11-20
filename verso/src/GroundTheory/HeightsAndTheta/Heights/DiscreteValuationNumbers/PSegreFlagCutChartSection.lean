import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChartSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChartSectionChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GenericProjClosureDivisor SegreFlagCutChartSection

noncomputable section

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ _ _ _ _ e t ht k hk c hc`. Establish `hsame₀ : ∀ i j : Fin N, i < j → w.repr (w i) j = 0` using `fun i j h => by`. Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply, if_neg (ne_of_lt h)]`. Prove the components needed by the constructor for the conclusion. Take `⟨β, δ, lam, Y, c'', hβ0, hlam, hlamv, hYh, hYs, hYv, hc''⟩` from `chart_data (O := O) y B w w e x hfl.flag hsame₀ a₀ φ hφ φ φ' t k hk c hc (some none) (fun l => X ⟨some none, l⟩) (fun l => isWeightedHomogeneous_X O _ _) (fun l => by rw [aeval_X]; rfl)`.

Take `⟨t', ht'⟩` from `exists_flagCoord_eq w e k c'' hc''`. Use `⟨Pi.single (some none) 1 + vdeg (fun j => (β j + (x ⟨k, hk⟩ j - a₀ j)).toNat), vdeg β, lam, chartMonoZ O M M' c β, β, rfl, hlam, chartMonoZ_homog c β, ?_, hlamv, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `o`. Break down `o with _ | _ | j` into its components or cases. Simplify using `[vdeg, zetaFirst, liftPairDeg]`.

Simplify using `[vdeg, zetaFirst, liftPairDeg]`. Use `hβ0 j` as an intermediate fact. Simplify using `[vdeg, zetaFirst, liftPairDeg]`. Use linear arithmetic over natural numbers and integers. Set `gg : (Σ o : Option K, bundleIdx (bundleIdx ι M) M' (Function.Embedding.some o)) → MRing (bundleIdx (bundleIdx ι M) M') O` to `fun p => match p with`.

Consider the case `⟨none, l⟩ => Y l`. Consider the case `⟨some kk, i⟩ => X ⟨some (some kk), i⟩`. Use `saturate Function.Embedding.some none (flagClosurePt y w e φ φ' t (k + 1)) lam (chartMonoZ O M M' c δ) _ _ (chartMonoZ_dvd c δ) (Pi.single (some none) 1 + vdeg δ) gg ?_ ?_ _ (isMultiHomogIdeal_pointIdeal _) ?_` and prove the remaining obligations. Introduce and unpack `⟨_ | kk, i⟩ h`. Conclude with `absurd rfl h`.

Both sides reduce to the same expression. Introduce and unpack `⟨_ | kk, l⟩ h`. Conclude with `⟨hYh l, hYs l⟩`. Conclude with `absurd h (Option.some_ne_none kk)`. Introduce `q hq`.

Establish `hpt : (fun p => aeval (flagClosurePt y w e φ φ' t (k + 1)) (gg p)) = flagProjPt Function.Embedding.some y w e φ φ' t' k`. Use function extensionality and compare the values at `p`. Break down `p with ⟨_ | kk, i⟩` into its components or cases. Use `show aeval _ (Y i) = _`. Rewrite using `[hYv i]`.

Use `show genVal w c'' (φ i) = projCoord y w φ (flagCoord w e t' k) ⟨none, i⟩`. Rewrite using `[ht']`. Both sides reduce to the same expression. Use `show aeval _ (X _) = _`. Rewrite using `[aeval_X]`.

Both sides reduce to the same expression. Rewrite using `[hpt]`. Conclude with `aeval_flagProjPt_eq_zero _ y w e φ φ' ht k hq t'`. Take `⟨β, δ, lam, Y, c'', hβ0, hlam, hlamv, hYh, hYs, hYv, hc''⟩` from `chart_data (O := O) y B' w w' e x' hfl.flag' hfl.sameFlag a₀' φ' hφ' φ φ' t k hk c hc none (fun l => X ⟨none, l⟩) (fun l => isWeightedHomogeneous_X O _ _) (fun l => by rw [aeval_X]; rfl)`. Take `⟨t', ht'⟩` from `exists_flagCoord_eq w e k c'' hc''`.

Use `⟨Pi.single none 1 + vdeg (fun j => (β j + (x' ⟨k, hk⟩ j - a₀' j)).toNat), vdeg β, lam, chartMonoZ O M M' c β, β, rfl, hlam, chartMonoZ_homog c β, ?_, hlamv, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `o`. Break down `o with _ | _ | j` into its components or cases. Simplify using `[vdeg, zetaSecond, liftPairDeg]`. Simplify using `[vdeg, zetaSecond, liftPairDeg]`.

Use `hβ0 j` as an intermediate fact. Simplify using `[vdeg, zetaSecond, liftPairDeg]`. Use linear arithmetic over natural numbers and integers. Set `gg : (Σ o : Option K, bundleIdx (bundleIdx ι M) M' (secondFactorBlocks o)) → MRing (bundleIdx (bundleIdx ι M) M') O` to `fun p => match p with`. Consider the case `⟨none, l⟩ => Y l`.

Consider the case `⟨some kk, i⟩ => X ⟨some (some kk), i⟩`. Use `saturate secondFactorBlocks none (flagClosurePt y w e φ φ' t (k + 1)) lam (chartMonoZ O M M' c δ) _ _ (chartMonoZ_dvd c δ) (Pi.single none 1 + vdeg δ) gg ?_ ?_ _ (isMultiHomogIdeal_pointIdeal _) ?_` and prove the remaining obligations. Introduce and unpack `⟨_ | kk, i⟩ h`. Conclude with `absurd rfl h`. Both sides reduce to the same expression.

Introduce and unpack `⟨_ | kk, l⟩ h`. Conclude with `⟨hYh l, hYs l⟩`. Conclude with `absurd h (Option.some_ne_none kk)`. Introduce `q hq`. Establish `hpt : (fun p => aeval (flagClosurePt y w e φ φ' t (k + 1)) (gg p)) = flagProjPt secondFactorBlocks y w e φ φ' t' k`.

Use function extensionality and compare the values at `p`. Break down `p with ⟨_ | kk, i⟩` into its components or cases. Use `show aeval _ (Y i) = _`. Rewrite using `[hYv i]`. Use `show genVal w c'' (φ' i) = ∑ j, flagCoord w e t' k j * algebraMap Ω Φ (φ' i (w j))`.

Rewrite using `[ht']`. Both sides reduce to the same expression. Use `show aeval _ (X _) = _`. Rewrite using `[aeval_X]`. Both sides reduce to the same expression.

Rewrite using `[hpt]`. Conclude with `aeval_flagProjPt_eq_zero _ y w e φ φ' ht k hq t'`.
-/
theorem SegreFlagCutChartSection.proof : SegreFlagCutChartSection.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hk c hc
  classical
  have hsame₀ : ∀ i j : Fin N, i < j → w.repr (w i) j = 0 := fun i j h => by
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg (ne_of_lt h)]
  constructor
  · obtain ⟨β, δ, lam, Y, c'', hβ0, hlam, hlamv, hYh, hYs, hYv, hc''⟩ :=
      chart_data (O := O) y B w w e x hfl.flag hsame₀ a₀ φ hφ φ φ' t k hk c hc (some none)
        (fun l => X ⟨some none, l⟩) (fun l => isWeightedHomogeneous_X O _ _)
        (fun l => by rw [aeval_X]; rfl)
    obtain ⟨t', ht'⟩ := exists_flagCoord_eq w e k c'' hc''
    refine ⟨Pi.single (some none) 1 + vdeg (fun j => (β j + (x ⟨k, hk⟩ j - a₀ j)).toNat), vdeg β, lam,
      chartMonoZ O M M' c β, β, rfl, hlam, chartMonoZ_homog c β, ?_, hlamv, ?_⟩
    · funext o
      rcases o with _ | _ | j
      · simp [vdeg, zetaFirst, liftPairDeg]
      · simp [vdeg, zetaFirst, liftPairDeg]
      · have := hβ0 j
        simp [vdeg, zetaFirst, liftPairDeg]
        omega
    · let gg : (Σ o : Option K, bundleIdx (bundleIdx ι M) M' (Function.Embedding.some o)) →
          MRing (bundleIdx (bundleIdx ι M) M') O := fun p =>
        match p with
        | ⟨none, l⟩ => Y l
        | ⟨some kk, i⟩ => X ⟨some (some kk), i⟩
      refine saturate Function.Embedding.some none (flagClosurePt y w e φ φ' t (k + 1)) lam
        (chartMonoZ O M M' c δ) _ _ (chartMonoZ_dvd c δ) (Pi.single (some none) 1 + vdeg δ) gg ?_ ?_ _
        (isMultiHomogIdeal_pointIdeal _) ?_
      · rintro ⟨_ | kk, i⟩ h
        · exact absurd rfl h
        · rfl
      · rintro ⟨_ | kk, l⟩ h
        · exact ⟨hYh l, hYs l⟩
        · exact absurd h (Option.some_ne_none kk)
      · intro q hq
        have hpt : (fun p => aeval (flagClosurePt y w e φ φ' t (k + 1)) (gg p)) =
            flagProjPt Function.Embedding.some y w e φ φ' t' k := by
          funext p
          rcases p with ⟨_ | kk, i⟩
          · show aeval _ (Y i) = _
            rw [hYv i]
            show genVal w c'' (φ i) = projCoord y w φ (flagCoord w e t' k) ⟨none, i⟩
            rw [ht']
            rfl
          · show aeval _ (X _) = _
            rw [aeval_X]
            rfl
        rw [hpt]
        exact aeval_flagProjPt_eq_zero _ y w e φ φ' ht k hq t'
  · obtain ⟨β, δ, lam, Y, c'', hβ0, hlam, hlamv, hYh, hYs, hYv, hc''⟩ :=
      chart_data (O := O) y B' w w' e x' hfl.flag' hfl.sameFlag a₀' φ' hφ' φ φ' t k hk c hc none
        (fun l => X ⟨none, l⟩) (fun l => isWeightedHomogeneous_X O _ _)
        (fun l => by rw [aeval_X]; rfl)
    obtain ⟨t', ht'⟩ := exists_flagCoord_eq w e k c'' hc''
    refine ⟨Pi.single none 1 + vdeg (fun j => (β j + (x' ⟨k, hk⟩ j - a₀' j)).toNat), vdeg β, lam,
      chartMonoZ O M M' c β, β, rfl, hlam, chartMonoZ_homog c β, ?_, hlamv, ?_⟩
    · funext o
      rcases o with _ | _ | j
      · simp [vdeg, zetaSecond, liftPairDeg]
      · simp [vdeg, zetaSecond, liftPairDeg]
      · have := hβ0 j
        simp [vdeg, zetaSecond, liftPairDeg]
        omega
    · let gg : (Σ o : Option K, bundleIdx (bundleIdx ι M) M' (secondFactorBlocks o)) →
          MRing (bundleIdx (bundleIdx ι M) M') O := fun p =>
        match p with
        | ⟨none, l⟩ => Y l
        | ⟨some kk, i⟩ => X ⟨some (some kk), i⟩
      refine saturate secondFactorBlocks none (flagClosurePt y w e φ φ' t (k + 1)) lam
        (chartMonoZ O M M' c δ) _ _ (chartMonoZ_dvd c δ) (Pi.single none 1 + vdeg δ) gg ?_ ?_ _
        (isMultiHomogIdeal_pointIdeal _) ?_
      · rintro ⟨_ | kk, i⟩ h
        · exact absurd rfl h
        · rfl
      · rintro ⟨_ | kk, l⟩ h
        · exact ⟨hYh l, hYs l⟩
        · exact absurd h (Option.some_ne_none kk)
      · intro q hq
        have hpt : (fun p => aeval (flagClosurePt y w e φ φ' t (k + 1)) (gg p)) =
            flagProjPt secondFactorBlocks y w e φ φ' t' k := by
          funext p
          rcases p with ⟨_ | kk, i⟩
          · show aeval _ (Y i) = _
            rw [hYv i]
            show genVal w c'' (φ' i) = ∑ j, flagCoord w e t' k j * algebraMap Ω Φ (φ' i (w j))
            rw [ht']
            rfl
          · show aeval _ (X _) = _
            rw [aeval_X]
            rfl
        rw [hpt]
        exact aeval_flagProjPt_eq_zero _ y w e φ φ' ht k hq t'

end

end GroundTheory.Heights₂.Heights.NumbersDVR
