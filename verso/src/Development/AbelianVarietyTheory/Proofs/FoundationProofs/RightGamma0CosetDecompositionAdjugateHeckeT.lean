import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLeftGamma0CosetDecompositionHeckeRepTOperatorStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_adjugate]`. Simplify using `using h1`. Rewrite using `[Matrix.adjugate_fin_two]`.

Simplify using `using h2`.
-/
theorem adjugate_mem_intMatricesDetLowerLeftDvd {L q : ℕ} {δ : M2} (h : δ ∈ DT L q) : δ.adjugate ∈ DT L q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Matrix.det_adjugate]; simpa using h1
  · rw [Matrix.adjugate_fin_two]; simpa using h2

/- English proof (translation)
Rewrite using `[Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp`.
-/
theorem intMatrixTwo_adjugate_adjugate (δ : M2) : δ.adjugate.adjugate = δ := by
  rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Introduce `L q hq hqL`. Establish `hL` using `GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator L q hq hqL`. Unfold `LRep at hL`. Unfold `RRep`. Set `φ : Option (Fin q) × Gamma0 L → Gamma0 L × Option (Fin q)` to `fun p => (p.2⁻¹, p.1)`.

Establish `hφ : Set.BijOn φ Set.univ Set.univ`. Rewrite using `[Set.bijOn_univ]`. Use `⟨fun a b h => ?_, fun b => ⟨(b.2, b.1⁻¹), by simp [φ]⟩⟩` and prove the remaining obligations. Simplify using `only [φ, Prod.mk.injEq, inv_inj] at h`. Conclude with `Prod.ext h.2 h.1`.

Establish `hA : Set.BijOn (fun δ : M2 => δ.adjugate) (DT L q) (DT L q)` using `Set.InvOn.bijOn ⟨fun δ _ => intMatrixTwo_adjugate_adjugate δ, fun δ _ => intMatrixTwo_adjugate_adjugate δ⟩ (fun δ h => adjugate_mem_intMatricesDetLowerLeftDvd h) (fun δ h => adjugate_mem_intMatricesDetLowerLeftDvd h)`. Establish `hc` using `hA.comp (hL.comp hφ)`. Use `hc using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp, φ]`.

Rewrite using `[Matrix.adjugate_mul_distrib]`. Use `congr 1`. Rewrite using `[Subgroup.coe_inv, ← Matrix.SpecialLinearGroup.coe_inv, inv_inv]`.
-/
theorem rrep_DT_adj_repT : ∀ L q : ℕ, q.Prime → ¬ q ∣ L →
    RRep L (DT L q) (fun i => (repT q i).adjugate) := by
  intro L q hq hqL
  have hL := GlobalTheory.T.isLeftGamma0CosetDecomposition_heckeRepTOperator L q hq hqL
  unfold LRep at hL
  unfold RRep
  let φ : Option (Fin q) × Gamma0 L → Gamma0 L × Option (Fin q) := fun p => (p.2⁻¹, p.1)
  have hφ : Set.BijOn φ Set.univ Set.univ := by
    rw [Set.bijOn_univ]
    refine ⟨fun a b h => ?_, fun b => ⟨(b.2, b.1⁻¹), by simp [φ]⟩⟩
    simp only [φ, Prod.mk.injEq, inv_inj] at h
    exact Prod.ext h.2 h.1
  have hA : Set.BijOn (fun δ : M2 => δ.adjugate) (DT L q) (DT L q) :=
    Set.InvOn.bijOn ⟨fun δ _ => intMatrixTwo_adjugate_adjugate δ, fun δ _ => intMatrixTwo_adjugate_adjugate δ⟩
      (fun δ h => adjugate_mem_intMatricesDetLowerLeftDvd h) (fun δ h => adjugate_mem_intMatricesDetLowerLeftDvd h)
  have hc := hA.comp (hL.comp hφ)
  convert hc using 1
  funext p
  simp only [Function.comp, φ]
  rw [Matrix.adjugate_mul_distrib]
  congr 1
  rw [Subgroup.coe_inv, ← Matrix.SpecialLinearGroup.coe_inv, inv_inv]

end GlobalTheory.EisM
