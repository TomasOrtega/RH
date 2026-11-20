import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolP

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

/- English proof (translation)
Use `letI : SeminormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpSemiNormedRing`. Use `letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra`. Use `letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _`. Establish `hpow : ∀ n : ℕ, A ^ (n + 1) *ᵥ v = 0`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using h`. Consider the case `succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]`. Set `L0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (Fin d → ℂ)` to `{ toFun := fun M => M *ᵥ v map_add' := fun M N => Matrix.add_mulVec M N v map_smul' := fun c M => by ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }`.

Set `L : Matrix (Fin d) (Fin d) ℂ →L[ℂ] (Fin d → ℂ)` to `LinearMap.toContinuousLinearMap L0`. Establish `hL : ∀ M, L M = M *ᵥ v` using `fun M => rfl`. Rewrite using `[NormedSpace.exp_eq_tsum (𝕂 := ℂ), ← hL, L.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)]`. Rewrite using `[tsum_eq_single 0]`. Simplify using `[hL]`.

Introduce `n hn`. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn`. Rewrite using `[hL, Matrix.smul_mulVec, hpow m, smul_zero]`.
-/
theorem exp_mulVec_of_zero {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (h : A *ᵥ v = 0) :
    NormedSpace.exp A *ᵥ v = v := by
  letI : SeminormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hpow : ∀ n : ℕ, A ^ (n + 1) *ᵥ v = 0 := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  let L0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }
  let L : Matrix (Fin d) (Fin d) ℂ →L[ℂ] (Fin d → ℂ) := LinearMap.toContinuousLinearMap L0
  have hL : ∀ M, L M = M *ᵥ v := fun M => rfl
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ), ← hL, L.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)]
  rw [tsum_eq_single 0]
  · simp [hL]
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hL, Matrix.smul_mulVec, hpow m, smul_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adjH_def {k r : ℕ} (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.MainNotions.BridgeCSB.adjH X = Hpk k r * Xᴴ * Hpk k r := rfl

/- English proof (translation)
Rewrite using `[Formalism.MainNotions.BridgeCSB.mem_UH_iff, Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul]`. Establish `ha : Formalism.MainNotions.BridgeCSB.adjH X = -X` using `eq_neg_of_add_eq_zero_left hX`. Rewrite using `[ha, Complex.star_def, Complex.conj_ofReal, smul_neg, ← Matrix.exp_add_of_commute]`. Rewrite using `[neg_add_cancel, NormedSpace.exp_zero]`. Conclude with `(Commute.refl _).neg_left`.
-/
theorem exp_mem_UH {k r : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : Hpk k r * Xᴴ * Hpk k r + X = 0) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  rw [Formalism.MainNotions.BridgeCSB.mem_UH_iff, Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul]
  have ha : Formalism.MainNotions.BridgeCSB.adjH X = -X := eq_neg_of_add_eq_zero_left hX
  rw [ha, Complex.star_def, Complex.conj_ofReal, smul_neg, ← Matrix.exp_add_of_commute]
  · rw [neg_add_cancel, NormedSpace.exp_zero]
  · exact (Commute.refl _).neg_left

/- English proof (translation)
Establish `hadj : Formalism.MainNotions.BridgeCSB.adjH X = -X`. Apply `Formalism.MainNotions.BridgeCSB.exp_smul_inj` to reduce the goal to its premises. Introduce `t`. Establish `hU` using `hX t`. Establish `h1 : Formalism.MainNotions.BridgeCSB.adjH (NormedSpace.exp ((t : ℂ) • X)) = (NormedSpace.exp ((t : ℂ) • X))⁻¹` using `(Matrix.inv_eq_left_inv ((Formalism.MainNotions.BridgeCSB.mem_UH_iff _).1 hU)).symm`.

Rewrite `h1` using `[Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul, Complex.star_def, Complex.conj_ofReal, ← Matrix.exp_neg]`. Rewrite using `[h1, smul_neg]`. Rewrite using `[← adjH_def, hadj, neg_add_cancel]`.
-/
theorem adj_of_lie {k r : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r)) : Hpk k r * Xᴴ * Hpk k r + X = 0 := by
  have hadj : Formalism.MainNotions.BridgeCSB.adjH X = -X := by
    apply Formalism.MainNotions.BridgeCSB.exp_smul_inj
    intro t
    have hU := hX t
    have h1 : Formalism.MainNotions.BridgeCSB.adjH (NormedSpace.exp ((t : ℂ) • X)) = (NormedSpace.exp ((t : ℂ) • X))⁻¹ :=
      (Matrix.inv_eq_left_inv ((Formalism.MainNotions.BridgeCSB.mem_UH_iff _).1 hU)).symm
    rw [Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul, Complex.star_def, Complex.conj_ofReal,
      ← Matrix.exp_neg] at h1
    rw [h1, smul_neg]
  rw [← adjH_def, hadj, neg_add_cancel]

/- English proof (translation)
Introduce `k r`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce `hX`. Conclude with `adj_of_lie hX`.

Introduce `hX t`. Conclude with `exp_mem_UH hX t`.
-/
theorem lieG : LieG := by
  intro k r
  ext X
  constructor
  · intro hX
    exact adj_of_lie hX
  · intro hX t
    exact exp_mem_UH hX t

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hij : X i j = 0`. Use `Formalism.MainNotions.BridgeCSB.entry_zero_of_const' X i j (bvec j i) fun t => ?_` and prove the remaining obligations. Use `congrFun (h t) i` as an intermediate fact. Rewrite using `[← this, Matrix.mulVec, dotProduct]`.

Simplify using `[bvec, Pi.single_apply]`. Rewrite using `[Matrix.mulVec, dotProduct]`. Simplify using `[bvec, Pi.single_apply, hij]`.
-/
theorem col_zero {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (j : Fin d)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j = bvec j) : X *ᵥ bvec j = 0 := by
  funext i
  have hij : X i j = 0 := by
    refine Formalism.MainNotions.BridgeCSB.entry_zero_of_const' X i j (bvec j i) fun t => ?_
    have := congrFun (h t) i
    rw [← this, Matrix.mulVec, dotProduct]
    simp [bvec, Pi.single_apply]
  rw [Matrix.mulVec, dotProduct]
  simp [bvec, Pi.single_apply, hij]

/- English proof (translation)
Introduce `k r`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce `hX`. Use `⟨adj_of_lie fun t => (hX t).1, fun a => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `col_zero _ fun t => ((hX t).2 a).1`. Conclude with `col_zero _ fun t => ((hX t).2 a).2`. Introduce and unpack `⟨hX, hk⟩ t`. Use `⟨exp_mem_UH hX t, fun a => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).1, smul_zero])`.

Conclude with `exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).2, smul_zero])`.
-/
theorem lieWb : LieWb := by
  intro k r
  ext X
  constructor
  · intro hX
    refine ⟨adj_of_lie fun t => (hX t).1, fun a => ⟨?_, ?_⟩⟩
    · exact col_zero _ fun t => ((hX t).2 a).1
    · exact col_zero _ fun t => ((hX t).2 a).2
  · rintro ⟨hX, hk⟩ t
    refine ⟨exp_mem_UH hX t, fun a => ⟨?_, ?_⟩⟩
    · exact exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).1, smul_zero])
    · exact exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).2, smul_zero])

end Formalism.L2.SG.Pf.BH
