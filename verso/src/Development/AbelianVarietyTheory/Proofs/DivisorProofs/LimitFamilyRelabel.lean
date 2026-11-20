import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RenameLinRootPerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMetsRootStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeDifferenceTendsZeroStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology

namespace GlobalTheory.Mean4O.RelabelObj

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem relabel_onObj : Hypotheses2 → HypothesesH → OnObj fun _ O _ _ _ _ => ∀ Φ : ℝ → Fn O.Y, LimFam Φ → Relabel Φ := by
  intro hP hH D O hc hf A T H hr Φ hlim τ τ'
  obtain ⟨σ, hσ, hx⟩ := GlobalTheory.T.arithmetic_degree_mets_root hP hH D O hc τ τ'
  obtain ⟨x, P, hxP⟩ := hc
  obtain ⟨x', hx'⟩ := hx x
  refine ⟨σ, hσ, fun B hB2 => ?_⟩
  have hL := hlim B hB2
  have e : ∀ S R, O.Y.arDeg S R = (GlobalTheory.ShFam.Pad.arIn O.s O.Φ (GlobalTheory.ShFam.metsOf x O.Φ)).arDeg S R := by
    intro S R; rw [← hxP.hm_eq]; rfl
  have hzero : ∀ (P : Pol D.what₂.Tau O.Y.N) (d : ℕ), d ≠ Formalism.DegreeFormula.dimFl D.what₂.Tau O.Y.N + 1 → P.IsHomogeneous d → Φ B P = 0 := by
    intro P d hd hP
    have h1 := hL P
    simp only [O.Y.arDeg_homog _ _ P d hd hP] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hpow : ∀ u : Wt O.Y, Φ B (linRoot (fun ρ i => u (σ ρ) i) ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.Y.N + 1)) =
      Φ B (linRoot u ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.Y.N + 1)) := by
    intro u
    have h1 := hL (linRoot (fun ρ i => u (σ ρ) i) ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.Y.N + 1))
    have h3 := hL (linRoot u ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.Y.N + 1))
    have h2 := GlobalTheory.T.arithmetic_degree_difference_tends_zero hP hH D O ⟨x, P, hxP⟩ hf A T H hr x' B hB2 u
    have h4 := h3.sub h2
    rw [sub_zero] at h4
    refine tendsto_nhds_unique h1 (h4.congr fun R => ?_)
    refine Eq.trans (sub_sub_cancel (O.Y.arDeg (setB O.Y B) R (linRoot u ^ (dimFl D.what₂.Tau O.N + 1))) _) ?_
    rw [e]
    exact (hx' B R u).symm
  set Ψ : Pol D.what₂.Tau O.Y.N →ₗ[ℝ] ℝ :=
    Φ B ∘ₗ (rename (Prod.map σ id) : Pol D.what₂.Tau O.Y.N →ₐ[ℝ] Pol D.what₂.Tau O.Y.N).toLinearMap - Φ B with hΨ
  have hΨa : ∀ F, Ψ F = Φ B (rename (Prod.map σ id) F) - Φ B F := fun F => rfl
  have hΨpow : ∀ u : D.what₂.Tau → Fin O.Y.N → ℝ,
      ev u (0 : Pol D.what₂.Tau O.Y.N) = Ψ (linRoot u ^ (Formalism.DegreeFormula.dimFl D.what₂.Tau O.Y.N + 1)) := by
    intro u
    have hu : u = fun ρ i => (fun ρ i => u (σ.symm ρ) i) (σ ρ) i := by
      funext ρ i
      simp
    rw [hΨa, map_pow, hu, GlobalTheory.Mean4.rename_linRoot_perm σ (fun ρ i => u (σ.symm ρ) i), hpow (fun ρ i => u (σ.symm ρ) i)]
    simp [ev]
  have hmon : ∀ m, Ψ (monomial m 1) = 0 := by
    intro m
    by_cases hm : m.degree = Formalism.DegreeFormula.dimFl D.what₂.Tau O.Y.N + 1
    · have := (coeff_eq_of_polarisation _ _ _ Ψ 0 hΨpow m hm).2
      simpa using this
    · have h1 : (monomial m (1 : ℝ) : Pol D.what₂.Tau O.Y.N).IsHomogeneous m.degree := isHomogeneous_monomial _ rfl
      rw [hΨa, hzero _ _ hm h1, hzero _ _ hm h1.rename_isHomogeneous, sub_zero]
  intro F
  have hF : Ψ F = 0 := by
    induction F using MvPolynomial.induction_on' with
    | monomial m a =>
      have : (monomial m a : Pol D.what₂.Tau O.Y.N) = a • monomial m 1 := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, map_smul, hmon, smul_zero]
    | add p q hp hq => rw [map_add, hp, hq, add_zero]
  rw [hΨa] at hF
  exact sub_eq_zero.mp hF

end GlobalTheory.Mean4O.RelabelObj
