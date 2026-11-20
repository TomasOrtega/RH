import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.IsDSSigLam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RigidUniversal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HcParamGapGeIndex
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

/- English proof (translation)
Apply `Submodule.le_topologicalClosure` to reduce the goal to its premises. Use `⟨v, ?_, rfl⟩` and prove the remaining obligations. Conclude with `(le_sInf fun _ hT => hT.1 : W' ≤ genSub (smE ε (rreg ε)) W') hv`.
-/
theorem mem_closure_generated_of_mem {ε : Fin n → Bool} (W' : Submodule ℂ (smD ε (rreg ε))) {v : smD ε (rreg ε)}
    (hv : v ∈ W') : (v : L2 ε) ∈ closGen (smE ε (rreg ε)) W' := by
  apply Submodule.le_topologicalClosure
  refine ⟨v, ?_, rfl⟩
  exact (le_sInf fun _ hT => hT.1 : W' ≤ genSub (smE ε (rreg ε)) W') hv

/- English proof (translation)
The claim follows from `Submodule.isClosed_topologicalClosure _`.
-/
theorem closure_generated_isClosed {ε : Fin n → Bool} (W' : Submodule ℂ (smD ε (rreg ε))) :
    IsClosed (closGen (smE ε (rreg ε)) W' : Set (L2 ε)) :=
  Submodule.isClosed_topologicalClosure _

/- English proof (translation)
Use `choose m hm using hlam.2`. Use `⟨fun a => m a + (n : ℤ) - 1 - ((a : ℕ) : ℤ), fun a => ?_⟩` and prove the remaining obligations. Use `hm a` as an intermediate fact. Simplify using `only [rho]`. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_integral_parameter (lam : Fin n → ℝ) (hlam : S7.IsHCParam lam) : ∃ μ : Fin n → ℤ, S7.IsMu lam μ := by
  choose m hm using hlam.2
  refine ⟨fun a => m a + (n : ℤ) - 1 - ((a : ℕ) : ℤ), fun a => ?_⟩
  have := hm a
  simp only [rho]
  push_cast
  linarith

/- English proof (translation)
Take `⟨T'⟩` from `HW.kType_exists_of_dom ε (lowK ε lam') (HW.lowK_int_dom ε lam' hlam).1 (HW.lowK_int_dom ε lam' hlam).2`. Take `⟨μ', hμ⟩` from `exists_integral_parameter lam' hlam`. Establish `hP` using `(S7.isPsiFor_psiM ε lam' h T' μ' hlam hμ hgl hq0 h8).1`. Establish `hv₀` using `HW.KType.w_ne_zero T'`. Establish `hσ` using `rreg_isURepOn ε`.

Establish `hD` using `isDerivedOn_smE hσ`. Establish `hV2` using `datumV_isKIrrHW hP hv₀`. Establish `hc2` using `datumV_casimir hP T'.w`. Establish `hVK2` using `datumV_kStable hP T'.w`. Establish `hV20` using `datumV_ne_bot hP hv₀`.

Establish `hW0 : W' ≠ ⊥`. Take `⟨w, hw, hw0, -⟩` from `hirr.2.2.2`. Introduce `hb`. Rewrite `hw` using `[hb]`. Conclude with `hw0 ((Submodule.mem_bot ℂ).1 hw)`.

Take `⟨φ, hφK, hφI⟩` from `KTypeIsomorphism.exists_phi hσ hD hirr hσ hD hV2`. Establish `huniv` using `rigid_universal hσ hD hirr hcas hK hσ hD hV2 hc2 hVK2 hstd φ hφK hφI`. Establish `hjw` using `datumEmbedding_highest_ne_zero hstd hP hv₀`. Establish `hstab` using `closGen_stable hstd hσ hD hirr hcas hK`. Take `⟨U0, hU0⟩` from `data_unitary_equiv hstd hσ hD hirr hcas hK hW0 hσ hD hV2 hc2 hVK2 hV20`.

Set `U : closGen (smE ε (rreg ε)) W' ≃ₗᵢ[ℂ] Hlam ε (S7.PsiM T' μ') T'.w` to `U0`. Establish `hU : ∀ g ∈ UJset ε, ∀ x y : closGen (smE ε (rreg ε)) W', (x : L2 ε) = rreg ε g (y : L2 ε) → ((U x : Hlam ε (S7.PsiM T' μ') T'.w) : L2 ε) = rreg ε g ((U y : Hlam ε (S7.PsiM T' μ') T'.w) : L2 ε)` using `hU0`. Take `⟨d, hd0, hd⟩` from `Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam' (sigLam ε (S7.PsiM T' μ') T'.w) (isDS_sigLam hstd hP hv₀)`. Use `⟨T', μ', hμ, ‖uniformisationL2 ε (S7.PsiM T' μ') T'.w T'.w‖ ^ 2, by positivity, d, hd0, ?_, hstab, ?_⟩` and prove the remaining obligations. Introduce `v hv`.

Establish `hmem : ((φ ⟨v, hv⟩ : datumV ε (S7.PsiM T' μ') T'.w) : smD ε (rreg ε)) ∈ LinearMap.range (jSm hP T'.w)`. Rewrite using `[← datumV_eq_range hP T'.w]`. Conclude with `(φ ⟨v, hv⟩).2`. Take `⟨t, ht⟩` from `hmem`. Establish `ht' : (((φ ⟨v, hv⟩ : datumV ε (S7.PsiM T' μ') T'.w) : smD ε (rreg ε)) : L2 ε) = uniformisationL2 ε (S7.PsiM T' μ') T'.w t` using `by rw [← ht]; rfl`.

Use `⟨t, fun g hg => ?_⟩` and prove the remaining obligations. Establish `e` using `huniv g hg ⟨v, hv⟩ ⟨v, hv⟩`. Rewrite `e` using `[ht']`. Rewrite using `[← formulaF hstd hP hv₀ hg t t]`. Conclude with `e.symm`.

Introduce `a ha b hb a' ha' b' hb'`. Establish `key : ∀ (x z : closGen (smE ε (rreg ε)) W') (y : Formalism.REAL.UJ ε), ⟪(x : L2 ε), rreg ε (Formalism.MainNotions.S.umat y) (z : L2 ε)⟫_ℂ = Formalism.MainNotions.S.coefOn (sigLam ε (S7.PsiM T' μ') T'.w) (U z) (U x) y`. Introduce `x z y`. Establish `hy : Formalism.MainNotions.S.umat y ∈ UJset ε` using `unitary_matrix_mem_set ε y`. Set `z' : closGen (smE ε (rreg ε)) W'` to `⟨rreg ε (Formalism.MainNotions.S.umat y) z, hstab _ hy _ z.2⟩`.

Establish `e1` using `hU _ hy z' z rfl`. Use `show _ = ⟪U x, sigLam ε (S7.PsiM T' μ') T'.w (Formalism.MainNotions.S.umat y) (U z)⟫_ℂ`. Rewrite using `[Submodule.coe_inner, sigLam_coe hstd hP hv₀ hy, ← e1, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map, Submodule.coe_inner]`. Establish `hfun : (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ * star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) = fun y => Formalism.MainNotions.S.coefOn (sigLam ε (S7.PsiM T' μ') T'.w) (U ⟨b, hb⟩) (U ⟨a, ha⟩) y * star (Formalism.MainNotions.S.c …`. Use function extensionality and compare the values at `y`.

Rewrite using `[← key ⟨a, ha⟩ ⟨b, hb⟩ y, ← key ⟨a', ha'⟩ ⟨b', hb'⟩ y]`. Rewrite using `[hfun]`. Use `⟨(hd _ _ _ _).1, ?_⟩` and prove the remaining obligations. Rewrite using `[(hd _ _ _ _).2, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map, Submodule.coe_inner, Submodule.coe_inner]`.
-/
theorem closed_irreducible_lowest_type_data (ε : Fin n → Bool) (lam' : Fin n → ℝ) (h : ℝ) (hstd : StdGap ε lam')
    (hlam : S7.IsHCParam lam') (hgl : GapAtLeast ε lam' h) (hq0 : 1 ≤ S7.q0 ε)
    (h8 : 8 * (n : ℝ) * (S7.q0 ε : ℝ) < h) (W' : Submodule ℂ (smD ε (rreg ε)))
    (hirr : IsKIrrHW ε (smE ε (rreg ε)) (lowK ε lam') W')
    (hcas : ∀ v ∈ W', casimir (smE ε (rreg ε)) v = (casVal lam' : ℂ) • v)
    (hK : ∀ k' ∈ Kset ε, ∀ v ∈ W', ∃ v'' ∈ W', (v'' : L2 ε) = rreg ε k' (v : L2 ε)) :
    ∃ (T' : S7.KType ε (lowK ε lam')) (μ' : Fin n → ℤ), S7.IsMu lam' μ' ∧
      ∃ C : ℝ, 0 < C ∧ ∃ d : ℝ, 0 < d ∧
      (∀ v ∈ W', ∃ t : T'.V, ∀ g ∈ UJset ε,
        ⟪((v : smD ε (rreg ε)) : L2 ε), rreg ε g (v : L2 ε)⟫_ℂ = (C : ℂ) * ⟪t, S7.PsiM T' μ' g t⟫_ℂ) ∧
      (∀ g ∈ UJset ε, ∀ x ∈ closGen (smE ε (rreg ε)) W', rreg ε g x ∈ closGen (smE ε (rreg ε)) W') ∧
      ∀ a ∈ closGen (smE ε (rreg ε)) W', ∀ b ∈ closGen (smE ε (rreg ε)) W',
        ∀ a' ∈ closGen (smE ε (rreg ε)) W', ∀ b' ∈ closGen (smE ε (rreg ε)) W',
        Integrable (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ *
          star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) (Formalism.REAL.muG ε) ∧
        ∫ y, ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ * star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ
          ∂(Formalism.REAL.muG ε) = ⟪b', b⟫_ℂ * ⟪a, a'⟫_ℂ / (d : ℂ) := by
  obtain ⟨T'⟩ := HW.kType_exists_of_dom ε (lowK ε lam') (HW.lowK_int_dom ε lam' hlam).1
    (HW.lowK_int_dom ε lam' hlam).2
  obtain ⟨μ', hμ⟩ := exists_integral_parameter lam' hlam
  have hP := (S7.isPsiFor_psiM ε lam' h T' μ' hlam hμ hgl hq0 h8).1
  have hv₀ := HW.KType.w_ne_zero T'
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hV2 := datumV_isKIrrHW hP hv₀
  have hc2 := datumV_casimir hP T'.w
  have hVK2 := datumV_kStable hP T'.w
  have hV20 := datumV_ne_bot hP hv₀
  have hW0 : W' ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hirr.2.2.2
    intro hb
    rw [hb] at hw
    exact hw0 ((Submodule.mem_bot ℂ).1 hw)
  obtain ⟨φ, hφK, hφI⟩ := KTypeIsomorphism.exists_phi hσ hD hirr hσ hD hV2
  have huniv := rigid_universal hσ hD hirr hcas hK hσ hD hV2 hc2 hVK2 hstd φ hφK hφI
  have hjw := datumEmbedding_highest_ne_zero hstd hP hv₀
  have hstab := closGen_stable hstd hσ hD hirr hcas hK
  obtain ⟨U0, hU0⟩ := data_unitary_equiv hstd hσ hD hirr hcas hK hW0 hσ hD hV2 hc2 hVK2 hV20
  let U : closGen (smE ε (rreg ε)) W' ≃ₗᵢ[ℂ] Hlam ε (S7.PsiM T' μ') T'.w := U0
  have hU : ∀ g ∈ UJset ε, ∀ x y : closGen (smE ε (rreg ε)) W', (x : L2 ε) = rreg ε g (y : L2 ε) →
      ((U x : Hlam ε (S7.PsiM T' μ') T'.w) : L2 ε) = rreg ε g ((U y : Hlam ε (S7.PsiM T' μ') T'.w) : L2 ε) :=
    hU0
  obtain ⟨d, hd0, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS lam' (sigLam ε (S7.PsiM T' μ') T'.w)
    (isDS_sigLam hstd hP hv₀)
  refine ⟨T', μ', hμ, ‖uniformisationL2 ε (S7.PsiM T' μ') T'.w T'.w‖ ^ 2, by positivity, d, hd0, ?_, hstab, ?_⟩
  · intro v hv
    have hmem : ((φ ⟨v, hv⟩ : datumV ε (S7.PsiM T' μ') T'.w) : smD ε (rreg ε)) ∈
        LinearMap.range (jSm hP T'.w) := by
      rw [← datumV_eq_range hP T'.w]; exact (φ ⟨v, hv⟩).2
    obtain ⟨t, ht⟩ := hmem
    have ht' : (((φ ⟨v, hv⟩ : datumV ε (S7.PsiM T' μ') T'.w) : smD ε (rreg ε)) : L2 ε) =
        uniformisationL2 ε (S7.PsiM T' μ') T'.w t := by rw [← ht]; rfl
    refine ⟨t, fun g hg => ?_⟩
    have e := huniv g hg ⟨v, hv⟩ ⟨v, hv⟩
    rw [ht'] at e
    rw [← formulaF hstd hP hv₀ hg t t]
    exact e.symm
  · intro a ha b hb a' ha' b' hb'
    have key : ∀ (x z : closGen (smE ε (rreg ε)) W') (y : Formalism.REAL.UJ ε),
        ⟪(x : L2 ε), rreg ε (Formalism.MainNotions.S.umat y) (z : L2 ε)⟫_ℂ =
          Formalism.MainNotions.S.coefOn (sigLam ε (S7.PsiM T' μ') T'.w) (U z) (U x) y := by
      intro x z y
      have hy : Formalism.MainNotions.S.umat y ∈ UJset ε := unitary_matrix_mem_set ε y
      let z' : closGen (smE ε (rreg ε)) W' := ⟨rreg ε (Formalism.MainNotions.S.umat y) z, hstab _ hy _ z.2⟩
      have e1 := hU _ hy z' z rfl
      show _ = ⟪U x, sigLam ε (S7.PsiM T' μ') T'.w (Formalism.MainNotions.S.umat y) (U z)⟫_ℂ
      rw [Submodule.coe_inner, sigLam_coe hstd hP hv₀ hy, ← e1, ← Submodule.coe_inner,
        LinearIsometryEquiv.inner_map_map, Submodule.coe_inner]
    have hfun : (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ *
          star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) =
        fun y => Formalism.MainNotions.S.coefOn (sigLam ε (S7.PsiM T' μ') T'.w) (U ⟨b, hb⟩) (U ⟨a, ha⟩) y *
          star (Formalism.MainNotions.S.coefOn (sigLam ε (S7.PsiM T' μ') T'.w) (U ⟨b', hb'⟩) (U ⟨a', ha'⟩) y) := by
      funext y
      rw [← key ⟨a, ha⟩ ⟨b, hb⟩ y, ← key ⟨a', ha'⟩ ⟨b', hb'⟩ y]
    rw [hfun]
    refine ⟨(hd _ _ _ _).1, ?_⟩
    rw [(hd _ _ _ _).2, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map,
      Submodule.coe_inner, Submodule.coe_inner]

end ReciprocityTheory.ChartRestriction.DS.Lap
