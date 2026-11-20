import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryStabiliserOrthogonalSummand
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D X u wt hw γ₀ hγ hfix`. Take `⟨Q, Qi, G', h1, h2, hq, he, hf, hz, hG', hD⟩` from `GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hw`. Establish `hU : ((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (starRingEnd X.B.I.E))ᵀ * X.B.I.J * (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J` using `hγ`. Establish `hcol : ∀ b, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b)`. Introduce `b`.

Break down `b with a | a | ⟨⟩` into its components or cases. Establish `e : (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a` using `funext (he a)`. Rewrite using `[e]`. Conclude with `hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))`. Establish `e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a` using `funext (hf a)`.

Rewrite using `[e]`. Conclude with `hfix _ (Or.inl (Or.inr ⟨a, rfl⟩))`. Establish `e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u` using `funext hz`. Rewrite using `[e]`. Conclude with `hfix _ (Or.inr rfl)`.

Take `⟨y, hy, hγQ⟩` from `(GlobalTheory.unitary_stabiliser_orthogonal_summand X.B.I.E (starRingEnd X.B.I.E) _ _ _ X.B.I.J _ G' Q Qi h1 h2 hD hG').2 _ hU hcol`. Use `⟨y, hy, fun j => ?_⟩` and prove the remaining obligations. Establish `hQ : (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Q = Q * (Matrix.fromBlocks y (0 : Matrix (Fin (D.R.N 0)) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E) (0 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin (D.R.N 0)) X.B.I.E) (1 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R. …`. Rewrite using `[hγQ, Matrix.mul_assoc _ Qi Q, h2, Matrix.mul_one]`. Use function extensionality and compare the values at `i`.

Establish `e` using `congrFun (congrFun hQ i) (Sum.inl j)`. Rewrite `e` using `[Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]`. Simplify using `only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hq] at e`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[e]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem unitary_fix_acts_on_complement_frame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V), WittX X u wt → ∀ γ₀ : GL (Fin X.B.I.n) X.B.I.E, γ₀ ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ x ∈ fixSet X u, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ x = x) → ∃ y₀ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) X.B.I.E, (y₀.map (starRingEnd X.B.I.E))ᵀ * (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm * y₀ = (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)).map X.ιE.symm ∧ ∀ j, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd (qFr wt j) = ∑ i, y₀ i j • X.crd (qFr wt i) := by
  intro D X u wt hw γ₀ hγ hfix
  obtain ⟨Q, Qi, G', h1, h2, hq, he, hf, hz, hG', hD⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hw
  have hU : ((γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (starRingEnd X.B.I.E))ᵀ * X.B.I.J *
      (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hγ
  have hcol : ∀ b, (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ (fun i => Q i (Sum.inr b)) =
      fun i => Q i (Sum.inr b) := by
    intro b
    rcases b with a | a | ⟨⟩
    · have e : (fun i => Q i (Sum.inr (Sum.inl a))) = X.eR a := funext (he a)
      rw [e]; exact hfix _ (Or.inl (Or.inl ⟨a, rfl⟩))
    · have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inl a)))) = X.fR a := funext (hf a)
      rw [e]; exact hfix _ (Or.inl (Or.inr ⟨a, rfl⟩))
    · have e : (fun i => Q i (Sum.inr (Sum.inr (Sum.inr ())))) = X.zR u := funext hz
      rw [e]; exact hfix _ (Or.inr rfl)
  obtain ⟨y, hy, hγQ⟩ := (GlobalTheory.unitary_stabiliser_orthogonal_summand X.B.I.E (starRingEnd X.B.I.E) _ _ _
    X.B.I.J _ G' Q Qi h1 h2 hD hG').2 _ hU hcol
  refine ⟨y, hy, fun j => ?_⟩
  have hQ : (γ₀ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Q = Q * (Matrix.fromBlocks y (0 : Matrix (Fin (D.R.N 0)) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E) (0 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin (D.R.N 0)) X.B.I.E) (1 : Matrix (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit) X.B.I.E)) := by
    rw [hγQ, Matrix.mul_assoc _ Qi Q, h2, Matrix.mul_one]
  funext i
  have e := congrFun (congrFun hQ i) (Sum.inl j)
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type] at e
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁,
    Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, hq] at e
  rw [Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [e]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.St
