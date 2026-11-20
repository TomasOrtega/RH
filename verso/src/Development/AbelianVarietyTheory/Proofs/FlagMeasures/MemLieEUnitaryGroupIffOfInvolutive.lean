import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlkExt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.TubeLie

open scoped Matrix.Norms.Operator in

/- English proof (translation)
Establish `hc : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • Xᴴ)`. Introduce `t`. Rewrite using `[← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]`. Establish `key : ∀ t : ℝ, H * NormedSpace.exp (t • X) = NormedSpace.exp (t • -Xᴴ) * H`. Introduce `t`.

Establish `ht : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H` using `h t`. Rewrite `ht` using `[hc t]`. Establish `e1 : NormedSpace.exp (-((t : ℂ) • Xᴴ)) * NormedSpace.exp ((t : ℂ) • Xᴴ) = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • Xᴴ)).neg_left, neg_add_cancel, NormedSpace.exp_zero]`. Establish `e2 : H * NormedSpace.exp ((t : ℂ) • X) = NormedSpace.exp (-((t : ℂ) • Xᴴ)) * H`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = NormedSpace.exp (-((t : ℂ) • Xᴴ)) * H := by rw [ht]`. Rewrite `e2` using `[← smul_neg, Complex.coe_smul, Complex.coe_smul]`. Conclude with `e2`.

Establish `d1 : HasDerivAt (fun t : ℝ => H * NormedSpace.exp (t • X)) (H * (NormedSpace.exp ((0 : ℝ) • X) * X)) 0` using `(hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul H`. Establish `d2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • -Xᴴ) * H) (NormedSpace.exp ((0 : ℝ) • -Xᴴ) * -Xᴴ * H) 0` using `(hasDerivAt_exp_smul_const (-Xᴴ) (0 : ℝ)).mul_const H`. Rewrite `d1` using `[show (fun t : ℝ => H * NormedSpace.exp (t • X)) = (fun t : ℝ => NormedSpace.exp (t • -Xᴴ) * H) from funext key]`. Establish `hu` using `d1.unique d2`. Simplify using `only [zero_smul, NormedSpace.exp_zero, one_mul] at hu`.

Rewrite using `[hu, neg_mul, add_neg_cancel]`.
-/
theorem skew_of_mem_lieOf {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : X ∈ lieOf (UH H)) :
    Xᴴ * H + H * X = 0 := by
  have hc : ∀ t : ℝ, (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • Xᴴ) := by
    intro t
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  have key : ∀ t : ℝ, H * NormedSpace.exp (t • X) = NormedSpace.exp (t • -Xᴴ) * H := by
    intro t
    have ht : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := h t
    rw [hc t] at ht
    have e1 : NormedSpace.exp (-((t : ℂ) • Xᴴ)) * NormedSpace.exp ((t : ℂ) • Xᴴ) = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.refl ((t : ℂ) • Xᴴ)).neg_left, neg_add_cancel,
        NormedSpace.exp_zero]
    have e2 : H * NormedSpace.exp ((t : ℂ) • X) = NormedSpace.exp (-((t : ℂ) • Xᴴ)) * H := by
      calc H * NormedSpace.exp ((t : ℂ) • X)
          = (NormedSpace.exp (-((t : ℂ) • Xᴴ)) * NormedSpace.exp ((t : ℂ) • Xᴴ)) * H *
              NormedSpace.exp ((t : ℂ) • X) := by rw [e1, one_mul]
        _ = NormedSpace.exp (-((t : ℂ) • Xᴴ)) *
              (NormedSpace.exp ((t : ℂ) • Xᴴ) * H * NormedSpace.exp ((t : ℂ) • X)) := by
            simp only [mul_assoc]
        _ = NormedSpace.exp (-((t : ℂ) • Xᴴ)) * H := by rw [ht]
    rw [← smul_neg, Complex.coe_smul, Complex.coe_smul] at e2
    exact e2
  have d1 : HasDerivAt (fun t : ℝ => H * NormedSpace.exp (t • X))
      (H * (NormedSpace.exp ((0 : ℝ) • X) * X)) 0 :=
    (hasDerivAt_exp_smul_const X (0 : ℝ)).const_mul H
  have d2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • -Xᴴ) * H)
      (NormedSpace.exp ((0 : ℝ) • -Xᴴ) * -Xᴴ * H) 0 :=
    (hasDerivAt_exp_smul_const (-Xᴴ) (0 : ℝ)).mul_const H
  rw [show (fun t : ℝ => H * NormedSpace.exp (t • X)) =
      (fun t : ℝ => NormedSpace.exp (t • -Xᴴ) * H) from funext key] at d1
  have hu := d1.unique d2
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hu
  rw [hu, neg_mul, add_neg_cancel]

/- English proof (translation)
Establish `hx : H * X = -(Xᴴ * H)`. Rewrite using `[← sub_eq_zero, sub_neg_eq_add, add_comm]`. Conclude with `h`. Establish `hs : SemiconjBy H ((t : ℂ) • X) (-((t : ℂ) • Xᴴ))`. Unfold `SemiconjBy`.

Rewrite using `[mul_smul_comm, hx, smul_neg, neg_mul, smul_mul_assoc]`. Establish `hc : (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • Xᴴ)`. Rewrite using `[← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]`. Set `_ : NormedRing (Matrix (Fin N) (Fin N) ℂ)` to `Matrix.linftyOpNormedRing`. Set `_ : NormedAlgebra ℚ (Matrix (Fin N) (Fin N) ℂ)` to `Matrix.linftyOpNormedAlgebra`.

Set `_ : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) ℂ)` to `Matrix.linftyOpNormedAlgebra`. Establish `_ : CompleteSpace (Matrix (Fin N) (Fin N) ℂ)` using `FiniteDimensional.complete ℂ _`. Use `hs.exp_neg_mul_mul_exp_eq_self` as an intermediate fact. Rewrite `this` using `[neg_neg]`. Rewrite using `[hc]`.

Conclude with `this`.
-/
private theorem conjTranspose_exp_mul_mul_exp_eq_of_skew {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : Xᴴ * H + H * X = 0)
    (t : ℝ) : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := by
  have hx : H * X = -(Xᴴ * H) := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h
  have hs : SemiconjBy H ((t : ℂ) • X) (-((t : ℂ) • Xᴴ)) := by
    unfold SemiconjBy
    rw [mul_smul_comm, hx, smul_neg, neg_mul, smul_mul_assoc]
  have hc : (NormedSpace.exp ((t : ℂ) • X))ᴴ = NormedSpace.exp ((t : ℂ) • Xᴴ) := by
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  let _ : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℚ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  have _ : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℂ _
  have := hs.exp_neg_mul_mul_exp_eq_self
  rw [neg_neg] at this
  rw [hc]
  exact this

/- English proof (translation)
Introduce `t`. Conclude with `conjTranspose_exp_mul_mul_exp_eq_of_skew H X h t`.
-/
theorem mem_lieOf_of_skew {N : ℕ} (H X : Matrix (Fin N) (Fin N) ℂ) (h : Xᴴ * H + H * X = 0) :
    X ∈ lieOf (UH H) := by
  intro t
  exact conjTranspose_exp_mul_mul_exp_eq_of_skew H X h t

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify, realifyFun]`.
-/
private theorem unrealify_equiv_symm_realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

/- English proof (translation)
Use extensionality with `⟨i, j, b⟩`. Apply the tactic sequence `cases b <;> simp [unrealify, realifyFun]`.
-/
private theorem equiv_symm_realifyFun_unrealify_eq {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    (WithLp.equiv 2 _).symm (realifyFun (unrealify x)) = x := by
  ext ⟨i, j, b⟩
  cases b <;> simp [unrealify, realifyFun]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify]`.
-/
private theorem unrealify_map_add {m : ℕ} (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify]`.
-/
private theorem unrealify_map_smul {m : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify]`.
-/
private theorem unrealify_map_zero {m : ℕ} :
    unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

/- English proof (translation)
Establish `hL : lieOf (UH H) = {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * H + H * X = 0}`. Use extensionality with `X`. Conclude with `⟨fun h => skew_of_mem_lieOf H X h, fun h => mem_lieOf_of_skew H X h⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Unfold `lieE at hx`. Rewrite `hx` using `[hL]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨X, hX, rfl⟩` from `hy`.

Rewrite using `[unrealify_equiv_symm_realifyFun]`. Conclude with `hX`. Consider the case `zero => simp [unrealify_map_zero]`. Consider the case `add y z _ _ hy hz`. Rewrite using `[unrealify_map_add, Matrix.conjTranspose_add, add_mul, mul_add]`.

Combine the equalities or inequalities in the displayed calculation. Normalize the expressions using the abelian group laws. Use `_ = 0 := by rw [hy, hz, add_zero]`. Consider the case `smul c y _ hy`. Rewrite using `[unrealify_map_smul, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc, mul_smul_comm, ← smul_add, hy, smul_zero]`.

Introduce `hx`. Unfold `lieE`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨unrealify x, ?_, equiv_symm_realifyFun_unrealify_eq x⟩` and prove the remaining obligations. Rewrite using `[hL]`.

Conclude with `hx`.
-/
theorem mem_lieE_UH (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0 := by
  have hL : lieOf (UH H) = {X : Matrix (Fin m) (Fin m) ℂ | Xᴴ * H + H * X = 0} := by
    ext X
    exact ⟨fun h => skew_of_mem_lieOf H X h, fun h => mem_lieOf_of_skew H X h⟩
  constructor
  · intro hx
    unfold lieE at hx
    rw [hL] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X, hX, rfl⟩ := hy
      rw [unrealify_equiv_symm_realifyFun]
      exact hX
    | zero => simp [unrealify_map_zero]
    | add y z _ _ hy hz =>
      rw [unrealify_map_add, Matrix.conjTranspose_add, add_mul, mul_add]
      calc (unrealify y)ᴴ * H + (unrealify z)ᴴ * H + (H * unrealify y + H * unrealify z)
          = ((unrealify y)ᴴ * H + H * unrealify y) + ((unrealify z)ᴴ * H + H * unrealify z) := by
            abel
        _ = 0 := by rw [hy, hz, add_zero]
    | smul c y _ hy =>
      rw [unrealify_map_smul, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
        smul_mul_assoc, mul_smul_comm, ← smul_add, hy, smul_zero]
  · intro hx
    unfold lieE
    apply Submodule.subset_span
    refine ⟨unrealify x, ?_, equiv_symm_realifyFun_unrealify_eq x⟩
    rw [hL]
    exact hx

/- English proof (translation)
Introduce `m H x _`. Conclude with `mem_lieE_UH m H x`.
-/
theorem mem_lieE_UH_of_sq : ∀ (m : ℕ) (H : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)),
    H * H = 1 → (x ∈ lieE (UH H) ↔ (unrealify x)ᴴ * H + H * unrealify x = 0) := by
  intro m H x _
  exact mem_lieE_UH m H x

end GlobalTheory.TubeLie
