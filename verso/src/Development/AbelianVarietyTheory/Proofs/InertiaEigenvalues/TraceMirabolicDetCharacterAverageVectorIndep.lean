import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.MirAvg

open Matrix

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Introduce a local definition for the expression.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_gl_mulVec_single_eq {r : ℕ} (i : Fin r) {a : Fin r → ZMod g} (ha : a ≠ 0) :
    ∃ y : Gn g r, (y : Mt g r) *ᵥ Pi.single i 1 = a := by
  have he : (Pi.single i (1 : ZMod g) : Fin r → ZMod g) ≠ 0 := by
    intro h; have := congrFun h i; simp at this
  let f := (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) _ he).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) a ha)
  obtain ⟨e, hef⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : e (Pi.single i 1) = a := by
    have := hef ⟨_, Submodule.mem_span_singleton_self _⟩
    rw [← this]
    simp only [f, LinearEquiv.trans_apply]
    rw [← LinearEquiv.toSpanNonzeroSingleton_one (ZMod g) (Fin r → ZMod g) _ he, LinearEquiv.symm_apply_apply,
      LinearEquiv.toSpanNonzeroSingleton_one]
  refine ⟨⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · show LinearMap.toMatrix' e.toLinearMap *ᵥ _ = a
    rw [LinearMap.toMatrix'_mulVec]; exact h1

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mirSet_true_conj {r : ℕ} (a : Fin r → ZMod g) (y z : Gn g r) :
    mirSet a true (y * z * y⁻¹) ↔ mirSet ((↑y⁻¹ : Mt g r) *ᵥ a) true z := by
  have hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1 := y.mul_inv
  have hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1 := y.inv_mul
  simp only [mirSet, if_true, Units.val_mul]
  constructor
  · intro h x
    obtain ⟨c, hc⟩ := h ((y : Mt g r) *ᵥ x)
    refine ⟨c, ?_⟩
    have := congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) hc
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec] at this
    exact this
  · intro h x
    obtain ⟨c, hc⟩ := h ((↑y⁻¹ : Mt g r) *ᵥ x)
    refine ⟨c, ?_⟩
    have := congrArg (fun v => (y : Mt g r) *ᵥ v) hc
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hAB, Matrix.one_mul, one_mulVec] at this
    rw [← this]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mirSet_false_conj {r : ℕ} (a : Fin r → ZMod g) (y z : Gn g r) :
    mirSet a false (y * z * y⁻¹) ↔ mirSet (a ᵥ* (y : Mt g r)) false z := by
  have hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1 := y.mul_inv
  have hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1 := y.inv_mul
  simp only [mirSet, Bool.false_eq_true, if_false, Units.val_mul]
  constructor
  · intro h x hx
    rw [← dotProduct_mulVec] at hx
    have := h _ hx
    have := congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) this
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec] at this
    exact this
  · intro h x hx
    have h2 : (a ᵥ* (y : Mt g r)) ⬝ᵥ ((↑y⁻¹ : Mt g r) *ᵥ x) = 0 := by
      rw [← dotProduct_mulVec, mulVec_mulVec, hAB, one_mulVec]; exact hx
    have := h _ h2
    have := congrArg (fun v => (y : Mt g r) *ᵥ v) this
    simp only [mulVec_mulVec, hAB, one_mulVec] at this
    rw [Matrix.mul_assoc]; exact this

open Classical in
/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem mirEl_coeff {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) (x : Gn g r) :
    (mirEl θ a b).coeff x = if mirSet a b x then ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) else 0 := by
  unfold mirEl
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_eq_single x]
  · simp [MonoidAlgebra.coeff_single]
  · intro h _ hne; simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, hne]
  · intro h; exact absurd (Finset.mem_univ x) h

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem tr_mirEl_conj {r : ℕ} (ψ : Gn g r → ℂ) (hψ : IsClass ψ) (θ : (ZMod g)ˣ →* ℂˣ)
    (a a' : Fin r → ZMod g) (b : Bool) (y : Gn g r) (H : ∀ z, mirSet a b (y * z * y⁻¹) ↔ mirSet a' b z) :
    tr (mirEl θ a b) ψ = tr (mirEl θ a' b) ψ := by
  classical
  unfold tr
  simp only [mirEl_coeff]
  rw [← Equiv.sum_comp (MulAut.conj y).toEquiv]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  have hd : Matrix.GeneralLinearGroup.det (y * z * y⁻¹) = Matrix.GeneralLinearGroup.det z := by
    rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det y), mul_inv_cancel_right]
  rw [hd, hψ z y]
  simp only [H z]

end GlobalTheory.MirAvg

open GlobalTheory.GLq GlobalTheory.MirAvg Matrix in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Treat this case separately. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem GlobalTheory.MirAvg.tr_mirEl_indep : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsClass ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ)
    (a : Fin (n + 1) → ZMod g), a ≠ 0 → ∀ b : Bool,
      tr (mirEl θ a b) ψ = tr (mirEl θ (if b then Pi.single 0 1 else Pi.single (Fin.last n) 1) b) ψ := by
  intro g _ n ψ hψ θ a ha b
  cases b with
  | true =>
    obtain ⟨y, hy⟩ := exists_gl_mulVec_single_eq (0 : Fin (n + 1)) ha
    refine tr_mirEl_conj ψ hψ θ a _ true y fun z => ?_
    rw [mirSet_true_conj, if_pos rfl, ← hy, mulVec_mulVec, y.inv_mul, one_mulVec]
  | false =>
    obtain ⟨P, hP⟩ := exists_gl_mulVec_single_eq (Fin.last n) ha
    let y : Gn g (n + 1) := ⟨(↑P⁻¹ : Mt g (n + 1))ᵀ, (P : Mt g (n + 1))ᵀ,
      by rw [← transpose_mul, P.mul_inv, transpose_one], by rw [← transpose_mul, P.inv_mul, transpose_one]⟩
    refine tr_mirEl_conj ψ hψ θ a _ false y fun z => ?_
    rw [mirSet_false_conj]
    have : a ᵥ* (y : Mt g (n + 1)) = Pi.single (Fin.last n) 1 := by
      show a ᵥ* (↑P⁻¹ : Mt g (n + 1))ᵀ = _
      rw [vecMul_transpose, ← hP, mulVec_mulVec, P.inv_mul, one_mulVec]
    rw [this]; rfl
