import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdDefs

noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

/- English proof (translation)
Introduce `F _ _ _ _ m _ _ _ μ _ α c hc hzero Φ hΦ`. Take `⟨A, hA⟩` from `hΦ.exists_ordDet_ge`. Take `⟨K, hK, hKc⟩` from `hc.exists_compact_tile`. Take `⟨B, hB⟩` from `exists_valBall_of_isCompact (hK.image Units.continuous_val)`. Take `⟨J, hJ⟩` from `hΦ.exists_eq_zero_of_small B`.

Establish `hm : (0 : ℤ) < m`. Use `NeZero.pos m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Set `sh : ℤ → Set (GL (Fin m) F)` to `fun k => {g | ordDet g = k}`. Use `⟨Finset.Icc (-((m : ℤ) * A)) (J * m), fun k => ∫ g in sh k, Φ g * c g ∂μ, ?_⟩` and prove the remaining obligations.

Introduce `s hs`. Establish `hint` using `hc.integrable_zeta μ hΦ hs`. Establish `hmeas : ∀ k, MeasurableSet (sh k)` using `fun k => (isClopen_shell F m k).isClosed.measurableSet`. Establish `hdisj : Pairwise (fun i j => Disjoint (sh i) (sh j))`. Introduce `i j hij`.

Conclude with `Set.disjoint_left.2 fun g hi hj => hij (hi.symm.trans hj)`. Establish `huniv : (⋃ k, sh k) = Set.univ` using `Set.iUnion_eq_univ_iff.2 fun g => ⟨ordDet g, rfl⟩`. Establish `hsplit` using `integral_iUnion hmeas hdisj hint.integrableOn`. Rewrite `hsplit` using `[huniv, setIntegral_univ]`. Rewrite using `[hsplit]`.

Establish `hshell : ∀ k, ∫ g in sh k, Φ g * detPow g s * c g ∂μ = (∫ g in sh k, Φ g * c g ∂μ) * qs F s ^ k`. Introduce `k`. Rewrite using `[← integral_mul_const]`. Use `setIntegral_congr_fun (hmeas k) fun g hg => ?_` and prove the remaining obligations. Establish `hg' : ordDet g = k` using `hg`.

Rewrite using `[detPow_eq_qs_zpow, hg']`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[hshell]`. Apply `tsum_eq_sum` to reduce the goal to its premises. Introduce `k hk`.

Rewrite `hk` using `[Finset.mem_Icc, not_and_or, not_le, not_le]`. Establish `hk0 : ∫ g in sh k, Φ g * c g ∂μ = 0`. Break down `hk with hk | hk` into its components or cases. Apply `setIntegral_eq_zero_of_forall_eq_zero` to reduce the goal to its premises. Introduce `g hg`.

Establish `hg' : ordDet g = k` using `hg`. Establish `hΦ0 : Φ g = 0`. Assume the negation of the conclusion as `hne`. Use `hA g hne` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[hΦ0, zero_mul]`. Establish `hcongr : ∫ g in sh k, Φ g * c g ∂μ = ∫ g in sh k, Φ 0 * c g ∂μ`. Use `setIntegral_congr_fun (hmeas k) fun g hg => ?_` and prove the remaining obligations. Establish `hg' : ordDet g = k` using `hg`. Distinguish the cases in `hcg : c g = 0`.

Simplify using `[hcg]`. Use `congr 1`. Establish `hgh : centralUnif F m ^ (k / (m : ℤ)) * (centralUnif F m ^ (-(k / (m : ℤ))) * g) = g`. Rewrite using `[← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]`. Establish `hordh : ordDet (centralUnif F m ^ (-(k / (m : ℤ))) * g) = k % m`.

Rewrite using `[ordDet_centralUnif_zpow_mul, hg', Int.emod_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `htile : centralUnif F m ^ (-(k / (m : ℤ))) * g ∈ tile F m 0`. Simplify using `only [tile, Set.mem_setOf_eq, zero_mul, zero_add]`. Rewrite using `[hordh]`.

Conclude with `⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩`. Establish `hch : c (centralUnif F m ^ (-(k / (m : ℤ))) * g) ≠ 0`. Rewrite `hcg` using `[← hgh, hc.zpow_mul]`. Conclude with `right_ne_zero_of_mul hcg`. Establish `hhK` using `hKc _ htile hch`.

Establish `hball` using `hB _ ⟨_, hhK, rfl⟩`. Establish `hjJ : J ≤ k / (m : ℤ)` using `Int.le_ediv_of_mul_le hm hk.le`. Rewrite using `[← hgh]`. Conclude with `hJ _ hjJ _ hball`. Rewrite using `[hcongr, integral_const_mul, hzero k, mul_zero]`.

Rewrite using `[hk0, zero_mul]`.
-/
theorem UpperTheory.local_zeta_integral_laurent_expansion :
    UpperTheory.V.Z.Gam.LdLaurent := by
  intro F _ _ _ _ m _ _ _ μ _ α c hc hzero Φ hΦ
  obtain ⟨A, hA⟩ := hΦ.exists_ordDet_ge
  obtain ⟨K, hK, hKc⟩ := hc.exists_compact_tile
  obtain ⟨B, hB⟩ := exists_valBall_of_isCompact (hK.image Units.continuous_val)
  obtain ⟨J, hJ⟩ := hΦ.exists_eq_zero_of_small B
  have hm : (0 : ℤ) < m := by
    have := NeZero.pos m
    omega
  let sh : ℤ → Set (GL (Fin m) F) := fun k => {g | ordDet g = k}
  refine ⟨Finset.Icc (-((m : ℤ) * A)) (J * m), fun k => ∫ g in sh k, Φ g * c g ∂μ, ?_⟩
  intro s hs
  have hint := hc.integrable_zeta μ hΦ hs
  have hmeas : ∀ k, MeasurableSet (sh k) := fun k => (isClopen_shell F m k).isClosed.measurableSet
  have hdisj : Pairwise (fun i j => Disjoint (sh i) (sh j)) := by
    intro i j hij
    exact Set.disjoint_left.2 fun g hi hj => hij (hi.symm.trans hj)
  have huniv : (⋃ k, sh k) = Set.univ := Set.iUnion_eq_univ_iff.2 fun g => ⟨ordDet g, rfl⟩
  have hsplit := integral_iUnion hmeas hdisj hint.integrableOn
  rw [huniv, setIntegral_univ] at hsplit
  rw [hsplit]
  have hshell : ∀ k, ∫ g in sh k, Φ g * detPow g s * c g ∂μ = (∫ g in sh k, Φ g * c g ∂μ) * qs F s ^ k := by
    intro k
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (hmeas k) fun g hg => ?_
    have hg' : ordDet g = k := hg
    rw [detPow_eq_qs_zpow, hg']
    ring
  simp_rw [hshell]
  apply tsum_eq_sum
  intro k hk
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  have hk0 : ∫ g in sh k, Φ g * c g ∂μ = 0 := by
    rcases hk with hk | hk
    · apply setIntegral_eq_zero_of_forall_eq_zero
      intro g hg
      have hg' : ordDet g = k := hg
      have hΦ0 : Φ g = 0 := by
        by_contra hne
        have := hA g hne
        linarith
      rw [hΦ0, zero_mul]
    · have hcongr : ∫ g in sh k, Φ g * c g ∂μ = ∫ g in sh k, Φ 0 * c g ∂μ := by
        refine setIntegral_congr_fun (hmeas k) fun g hg => ?_
        have hg' : ordDet g = k := hg
        by_cases hcg : c g = 0
        · simp [hcg]
        · congr 1
          have hgh : centralUnif F m ^ (k / (m : ℤ)) * (centralUnif F m ^ (-(k / (m : ℤ))) * g) = g := by
            rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
          have hordh : ordDet (centralUnif F m ^ (-(k / (m : ℤ))) * g) = k % m := by
            rw [ordDet_centralUnif_zpow_mul, hg', Int.emod_def]
            ring
          have htile : centralUnif F m ^ (-(k / (m : ℤ))) * g ∈ tile F m 0 := by
            simp only [tile, Set.mem_setOf_eq, zero_mul, zero_add]
            rw [hordh]
            exact ⟨Int.emod_nonneg _ hm.ne', Int.emod_lt_of_pos _ hm⟩
          have hch : c (centralUnif F m ^ (-(k / (m : ℤ))) * g) ≠ 0 := by
            rw [← hgh, hc.zpow_mul] at hcg
            exact right_ne_zero_of_mul hcg
          have hhK := hKc _ htile hch
          have hball := hB _ ⟨_, hhK, rfl⟩
          have hjJ : J ≤ k / (m : ℤ) := Int.le_ediv_of_mul_le hm hk.le
          rw [← hgh]
          exact hJ _ hjJ _ hball
      rw [hcongr, integral_const_mul, hzero k, mul_zero]
  rw [hk0, zero_mul]
