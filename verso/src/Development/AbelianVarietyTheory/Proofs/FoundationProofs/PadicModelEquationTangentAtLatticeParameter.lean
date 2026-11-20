import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar.ModelPoint

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem wpD_sq {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    wpD Λ v ^ 2 = 4 * wpF Λ v ^ 3 - g2 Λ * wpF Λ v - g3 Λ := by
  obtain ⟨w₁, w₂, hi, hΛ⟩ := h
  let L : PeriodPair := ⟨w₁, w₂, hi⟩
  have hL : ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  rw [GlobalTheory.LatticeInvariants.wpD_eq hL, GlobalTheory.LatticeInvariants.wpF_eq hL,
    GlobalTheory.LatticeInvariants.g2_eq hL, GlobalTheory.LatticeInvariants.lattice_invariant_g3_eq hL]
  exact L.derivWeierstrassP_sq v fun h => hv ((hL v).2 h)

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lamC_coe (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := dif_pos x.2

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lamC_neg_div_four (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) :
    lamC lam (-x / 4) = -lamC lam x / 4 := by
  lift x to Qbar using hx
  have e : (-(x : ℂ) / 4) = ((-x / 4 : Qbar) : ℂ) := by push_cast; rfl
  rw [e, lamC_coe, lamC_coe, map_div₀, map_neg, map_ofNat]

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Move the embeddings inside the algebraic operations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem lamC_eqn (lam : Qbar →+* ℂ_[p]) {x y a b : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar)
    (ha : a ∈ Qbar) (hb : b ∈ Qbar) (h : y ^ 2 = 4 * x ^ 3 - a * x - b) :
    lamC lam y ^ 2 = 4 * lamC lam x ^ 3 - lamC lam a * lamC lam x - lamC lam b := by
  lift x to Qbar using hx
  lift y to Qbar using hy
  lift a to Qbar using ha
  lift b to Qbar using hb
  have e : y ^ 2 = 4 * x ^ 3 - a * x - b := by
    apply Subtype.ext
    push_cast
    exact h
  have := congrArg lam e
  simpa only [lamC_coe, map_sub, map_mul, map_pow, map_ofNat] using this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Take a linear combination of the given relations to obtain the conclusion. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem model_point : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → wpD g.abelian₂ v ∈ Qbar → g.W.toAffine.Equation (GlobalTheory.EvenTheta.xAt g v) (GlobalTheory.ThetaPar.yAt g v) ∧ 2 * GlobalTheory.ThetaPar.yAt g v + g.W.a₁ * GlobalTheory.EvenTheta.xAt g v + g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * lamC g.lam (wpD g.abelian₂ v) := by
  intro p _ g v hL h2 h3 hv hx hy
  have key := lamC_eqn g.lam hx hy h2 h3 (wpD_sq hL hv)
  constructor
  · rw [WeierstrassCurve.Affine.equation_iff]
    simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt,
      lamC_neg_div_four g.lam h2, lamC_neg_div_four g.lam h3]
    linear_combination ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 / 4 * key
  · simp only [GL3Theta.G1.W, WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₃, wModel, GlobalTheory.EvenTheta.xAt, GlobalTheory.ThetaPar.yAt]
    ring

end GlobalTheory.ThetaPar.ModelPoint
