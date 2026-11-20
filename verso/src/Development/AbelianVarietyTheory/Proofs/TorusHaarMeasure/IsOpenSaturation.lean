import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SatOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (lact δ : Frame Ψ r → Frame Ψ r) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpen_cell {r : ℕ} (X : Data E r) {x1 : Frame X.Ψ r} (ho : IsOrth X x1)
    {N : Set (V (nd X))} (hN : IsOpen N) (hNO : N ⊆ OmF X x1) :
    IsOpen {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} := by
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X x1 ho
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have heq : {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} =
      {x | x ∈ X.dom ∧ Δ x ≠ 0} ∩ zOf ⁻¹' N := by
    ext x
    constructor
    · rintro ⟨y, hy, b, hb, rfl⟩
      obtain ⟨h1, h2, -⟩ := huniq y (hNO hy) b hb
      refine ⟨⟨OntoS.dom_rmul X (hNO hy) hb, h1⟩, ?_⟩
      rw [Set.mem_preimage, h2]
      exact hy
    · rintro ⟨⟨hx, hd⟩, hzN⟩
      obtain ⟨-, h2, h3⟩ := hsplit x hx hd
      exact ⟨zOf x, hzN, bOf x, h2, h3⟩
  rw [heq]
  exact hz.continuousOn.isOpen_inter_preimage hU hN

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpen_saturation : ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 →
    ∀ N : Set (V (nd X)), IsOpen N → N ⊆ OmF X x1 →
    IsOpen {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} := by
  intro r X x1 ho N hN hNO
  have heq : {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} =
      ⋃ γ ∈ X.Γ, lact γ⁻¹ ⁻¹' {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, γ, hγ, b, hb, rfl⟩
      exact ⟨γ, hγ, y, hy, b, hb, FundSetPf.lact_inv _ _⟩
    · rintro ⟨γ, hγ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ, hγ, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
  rw [heq]
  exact isOpen_biUnion fun γ _ => (isOpen_cell X ho hN hNO).preimage (continuous_lact _)

end GlobalTheory.SatOpen
