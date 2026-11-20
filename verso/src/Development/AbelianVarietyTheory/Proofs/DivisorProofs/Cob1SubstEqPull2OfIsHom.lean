import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.CobPull

/- English proof (translation)
Introduce `R _ d μ ν φ hμ hν hφ f`. Establish `hp : HasSubst φ` using `hasSubst_of_constantCoeff_zero hφ.const`. Establish `hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`. Establish `hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`. Establish `hu : ∀ j, constantCoeff (inL (φ j)) = 0` using `fun j => by`.

Unfold `inL`. Rewrite using `[SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]`. Establish `hv : ∀ j, constantCoeff (inR (φ j)) = 0` using `fun j => by`. Unfold `inR`. Rewrite using `[SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]`.

Take `⟨hL, hR, hAS, -, -, hsub, -, -⟩` from `SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (fun j => inL (φ j)) (fun j => inR (φ j)) hu hv`. Unfold `pull2 cob1`. Rewrite using `[(hAS _ _).2, (hAS _ _).2, hL, hR, hsub d ν hν f]`. Establish `e1 : subst μ (subst φ f) = subst (fun j => at2 (ν j) (fun j => inL (φ j)) (fun j => inR (φ j))) f`. Rewrite using `[subst_comp_subst_apply hp (hasSubst_of_constantCoeff_zero hμ)]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `hφ.hom j`. Establish `e2 : inL (subst φ f) = subst (fun j => inL (φ j)) f`. Unfold `inL`.

Rewrite using `[subst_comp_subst_apply hp hX]`. Establish `e3 : inR (subst φ f) = subst (fun j => inR (φ j)) f`. Unfold `inR`. Rewrite using `[subst_comp_subst_apply hp hY]`. Rewrite using `[e1, e2, e3]`.
-/
theorem cob1_subst_eq_pull2_of_isHom_formal : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), ∀ (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (φ : Fin d → MvPowerSeries (Fin d) R), (∀ i, constantCoeff (μ i) = 0) → (∀ i, constantCoeff (ν i) = 0) → IsHom μ ν φ → ∀ f : MvPowerSeries (Fin d) R, cob1 μ (subst φ f) = pull2 φ (cob1 ν f) := by
  intro R _ d μ ν φ hμ hν hφ f
  have hp : HasSubst φ := hasSubst_of_constantCoeff_zero hφ.const
  have hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hu : ∀ j, constantCoeff (inL (φ j)) = 0 := fun j => by
    unfold inL
    rw [SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]
  have hv : ∀ j, constantCoeff (inR (φ j)) = 0 := fun j => by
    unfold inR
    rw [SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]
  obtain ⟨hL, hR, hAS, -, -, hsub, -, -⟩ :=
    SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (fun j => inL (φ j))
      (fun j => inR (φ j)) hu hv
  unfold pull2 cob1
  rw [(hAS _ _).2, (hAS _ _).2, hL, hR, hsub d ν hν f]
  have e1 : subst μ (subst φ f) = subst (fun j => at2 (ν j) (fun j => inL (φ j)) (fun j => inR (φ j))) f := by
    rw [subst_comp_subst_apply hp (hasSubst_of_constantCoeff_zero hμ)]
    congr 1
    funext j
    exact hφ.hom j
  have e2 : inL (subst φ f) = subst (fun j => inL (φ j)) f := by
    unfold inL
    rw [subst_comp_subst_apply hp hX]
  have e3 : inR (subst φ f) = subst (fun j => inR (φ j)) f := by
    unfold inR
    rw [subst_comp_subst_apply hp hY]
  rw [e1, e2, e3]

end GlobalTheory.Katz.CobPull
