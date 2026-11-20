import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.GelfandCentralHolds

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.admitted.gen casGen casSg Formalism.L2.SG.Pf.admitted.sg`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem gen_eq_A (p : Fin n × Fin n) : Formalism.L2.SG.Pf.admitted.gen ε p = casGen ε p := by
  unfold Formalism.L2.SG.Pf.admitted.gen casGen casSg Formalism.L2.SG.Pf.admitted.sg
  split_ifs <;> simp

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.admitted.wt Formalism.L2.SG.Pf.admitted.sg casWt casSg`. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem coef_eq_A (p : Fin n × Fin n) :
    (((Formalism.L2.SG.Pf.admitted.wt p * Formalism.L2.SG.Pf.admitted.sg ε p : ℝ)) : ℂ) = casWt p * casSg ε p := by
  unfold Formalism.L2.SG.Pf.admitted.wt Formalism.L2.SG.Pf.admitted.sg casWt casSg
  split_ifs <;> push_cast <;> ring

/- English proof (translation)
Rewrite using `[← casU_eq_casimir (isDerivedOn_smE hσ) v]`. Unfold `Formalism.L2.SG.Pf.admitted.Cas casU`. Use `congr 1`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[coef_eq_A, gen_eq_A]`.

Both sides reduce to the same expression.
-/
theorem cas_eq_A (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : smD ε σ) :
    Formalism.L2.SG.Pf.admitted.Cas ε σ v = ((casimir (smE ε σ) v : smD ε σ) : H) := by
  rw [← casU_eq_casimir (isDerivedOn_smE hσ) v]
  unfold Formalism.L2.SG.Pf.admitted.Cas casU
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coef_eq_A, gen_eq_A]
  rfl

/- English proof (translation)
The claim follows from `Formalism.MainNotions.BridgeCPX.HCAdm_of_mult (fun n ε H _ _ _ σ h1 h2 S h3 h4 => CompanionTheory.HCMult.harish_chandra_multiplicity n ε H σ h1 h2 S h3 h4) n ε H σ hσ hirr`.
-/
theorem admissibleProjection_of_irreducible_indefUnitary [CompleteSpace H] (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) : Formalism.MainNotions.BridgeCPX.AdmProjAt ε σ :=
  Formalism.MainNotions.BridgeCPX.HCAdm_of_mult (fun n ε H _ _ _ σ h1 h2 S h3 h4 => CompanionTheory.HCMult.harish_chandra_multiplicity n ε H σ h1 h2 S h3 h4)
    n ε H σ hσ hirr

/- English proof (translation)
Introduce `n ε H _ _ _ σ hσ hirr`. Distinguish the cases in `hex : ∃ w : H, Formalism.MainNotions.S.IsKFin ε σ w ∧ w ≠ 0`. Take `⟨w, hwK, hw⟩` from `hex`. Take `⟨c, hc⟩` from `Formalism.L2.SG.Pf.admitted.casScalar n ε H σ hσ hirr w hw`. Establish `hK : ∀ (x : smD ε σ), Formalism.MainNotions.S.IsKFin ε σ (x : H) → casimir (smE ε σ) x = (c : ℂ) • x` using `fun x hx => by`.

Establish `h1` using `hc x (Formalism.MainNotions.BridgeCPX.kfin_mem_Vsub hσ hirr (admissibleProjection_of_irreducible_indefUnitary hσ hirr) hw hx)`. Rewrite `h1` using `[cas_eq_A hσ]`. Conclude with `Subtype.ext (by rw [h1]; rfl)`. Use `⟨c, fun v => ?_⟩` and prove the remaining obligations. Establish `hy : ((casimir (smE ε σ) v - (c : ℂ) • v : smD ε σ) : H) = 0`.

Use `eq_zero_of_perp_A hσ (Submodule.coe_mem _) fun a ha => ?_` and prove the remaining obligations. Establish `haS` using `mem_smD_of_isKFin hσ hirr ha`. Establish `h1` using `casimir_symm_A hσ ⟨a, haS⟩ v`. Rewrite `h1` using `[hK ⟨a, haS⟩ ha, inner_smul_left, Complex.conj_ofReal]`. Rewrite using `[Submodule.coe_sub, Submodule.coe_smul, inner_sub_right, inner_smul_right]`.

Establish `h2 : ⟪a, ((casimir (smE ε σ) v : smD ε σ) : H)⟫_ℂ = (c : ℂ) * ⟪a, (v : H)⟫_ℂ`. Use `h1.symm` as an intermediate fact. Simplify using `using this`. Rewrite using `[h2, sub_self]`. Conclude with `Subtype.ext (sub_eq_zero.1 (by simpa using hy))`.

Use `push Not at hex`. Use `⟨0, fun v => ?_⟩` and prove the remaining obligations. Establish `h0 : (v : H) = 0` using `eq_zero_of_perp_A hσ v.2 fun a ha => by`. Rewrite using `[show a = 0 by by_contra h; exact h (hex a ha) |>.elim]`. Simplify using the standard rewrite rules.

Establish `hv : v = 0` using `Subtype.ext h0`. Rewrite using `[hv, map_zero, smul_zero]`.
-/
theorem casimirActsByScalar_indefUnitary : CasScal := by
  intro n ε H _ _ _ σ hσ hirr
  by_cases hex : ∃ w : H, Formalism.MainNotions.S.IsKFin ε σ w ∧ w ≠ 0
  · obtain ⟨w, hwK, hw⟩ := hex
    obtain ⟨c, hc⟩ := Formalism.L2.SG.Pf.admitted.casScalar n ε H σ hσ hirr w hw
    have hK : ∀ (x : smD ε σ), Formalism.MainNotions.S.IsKFin ε σ (x : H) →
        casimir (smE ε σ) x = (c : ℂ) • x := fun x hx => by
      have h1 := hc x (Formalism.MainNotions.BridgeCPX.kfin_mem_Vsub hσ hirr (admissibleProjection_of_irreducible_indefUnitary hσ hirr) hw hx)
      rw [cas_eq_A hσ] at h1
      exact Subtype.ext (by rw [h1]; rfl)
    refine ⟨c, fun v => ?_⟩
    have hy : ((casimir (smE ε σ) v - (c : ℂ) • v : smD ε σ) : H) = 0 := by
      refine eq_zero_of_perp_A hσ (Submodule.coe_mem _) fun a ha => ?_
      have haS := mem_smD_of_isKFin hσ hirr ha
      have h1 := casimir_symm_A hσ ⟨a, haS⟩ v
      rw [hK ⟨a, haS⟩ ha, inner_smul_left, Complex.conj_ofReal] at h1
      rw [Submodule.coe_sub, Submodule.coe_smul, inner_sub_right, inner_smul_right]
      have h2 : ⟪a, ((casimir (smE ε σ) v : smD ε σ) : H)⟫_ℂ = (c : ℂ) * ⟪a, (v : H)⟫_ℂ := by
        have := h1.symm
        simpa using this
      rw [h2, sub_self]
    exact Subtype.ext (sub_eq_zero.1 (by simpa using hy))
  · push Not at hex
    refine ⟨0, fun v => ?_⟩
    have h0 : (v : H) = 0 := eq_zero_of_perp_A hσ v.2 fun a ha => by
      rw [show a = 0 by by_contra h; exact h (hex a ha) |>.elim]
      simp
    have hv : v = 0 := Subtype.ext h0
    rw [hv, map_zero, smul_zero]

end CompanionTheory.D.gk.HC
