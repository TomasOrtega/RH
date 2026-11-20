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
Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [lact, mat, Matrix.mul_apply, Matrix.of_apply]`. Use `fun_prop`.
-/
theorem continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (lact δ : Frame Ψ r → Frame Ψ r) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Take `⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩` from `lu_holds r X x1 ho`. Establish `hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0}` using `(FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)`. Establish `heq : {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} = {x | x ∈ X.dom ∧ Δ x ≠ 0} ∩ zOf ⁻¹' N`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, b, hb, rfl⟩`. Take `⟨h1, h2, -⟩` from `huniq y (hNO hy) b hb`. Use `⟨⟨OntoS.dom_rmul X (hNO hy) hb, h1⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.mem_preimage, h2]`. Conclude with `hy`.

Introduce and unpack `⟨⟨hx, hd⟩, hzN⟩`. Take `⟨-, h2, h3⟩` from `hsplit x hx hd`. Conclude with `⟨zOf x, hzN, bOf x, h2, h3⟩`. Rewrite using `[heq]`. Conclude with `hz.continuousOn.isOpen_inter_preimage hU hN`.
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
Introduce `r X x1 ho N hN hNO`. Establish `heq : {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} = ⋃ γ ∈ X.Γ, lact γ⁻¹ ⁻¹' {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b}`. Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, γ, hγ, b, hb, rfl⟩`. Conclude with `⟨γ, hγ, y, hy, b, hb, FundSetPf.lact_inv _ _⟩`. Introduce and unpack `⟨γ, hγ, y, hy, b, hb, h⟩`. Use `⟨y, hy, γ, hγ, b, hb, ?_⟩` and prove the remaining obligations. Rewrite using `[← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]`.

Rewrite using `[heq]`. Conclude with `isOpen_biUnion fun γ _ => (isOpen_cell X ho hN hNO).preimage (continuous_lact _)`.
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
