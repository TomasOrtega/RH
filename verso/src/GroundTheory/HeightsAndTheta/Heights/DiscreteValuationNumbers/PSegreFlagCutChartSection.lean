import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCutChartSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagCutChartSectionChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GenericProjClosureDivisor SegreFlagCutChartSection

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Introduce a local definition for the expression.

Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Both sides reduce to the same expression.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Introduce a local definition for the expression. Treat this case separately. Treat this case separately.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Both sides reduce to the same expression. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
