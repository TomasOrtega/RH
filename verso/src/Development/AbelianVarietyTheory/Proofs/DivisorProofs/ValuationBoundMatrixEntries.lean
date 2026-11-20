import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixNormFirstColumnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixNormInvariantUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixNormBlockReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularToBasisVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodularBlockFormStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

set_option autoImplicit false

/- English proof (translation)
Introduce `R K _ _ _ _ ι C _ _ θ h1 h2 h3 r`. Take `⟨t0, ht0⟩` from `h3`. Proceed by induction on `r with`. Consider the case `zero => intro M ρ _`. Conclude with `⟨1, fun l => l.elim0, fun j => j.elim0⟩`.

Consider the case `succ r ih`. Introduce `M ρ hM`. Establish `hcol : ∀ t, ‖θ t (ρ 0)‖ * Finset.univ.sup' Finset.univ_nonempty (fun l => ‖θ t (M l 0)‖) = 1` using `fun t => by`. Use `hM t 0` as an intermediate fact. Rewrite `this` using `[GlobalTheory.T.matrix_norm_first_column]`. Then use the resulting hypothesis.

Establish `hint : ∀ l, ∃ a, algebraMap R K a = ρ 0 * M l 0` using `fun l => h2 _ fun t => by`. Rewrite using `[map_mul, norm_mul, ← hcol t]`. Conclude with `mul_le_mul_of_nonneg_left (Finset.le_sup' (fun l => ‖θ t (M l 0)‖) (Finset.mem_univ l)) (norm_nonneg _)`. Use `choose a ha using hint`. Take `⟨l0, -, hl0⟩` from `Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun l => ‖θ t0 (M l 0)‖)`.

Establish `hunit : IsUnit (a l0)`. Assume the negation of the conclusion as `hn`. Use `ht0 _ ((IsLocalRing.mem_maximalIdeal _).2 hn)` as an intermediate fact. Rewrite `this` using `[ha, map_mul, norm_mul, ← hl0, hcol t0]`. Conclude with `lt_irrefl _ this`.

Establish `hρ0 : ρ 0 ≠ 0`. Introduce `h`. Use `hcol t0` as an intermediate fact. Rewrite `this` using `[h, map_zero, norm_zero, zero_mul]`. Conclude with `zero_ne_one this`.

Take `⟨Q, hQ⟩` from `GlobalTheory.T.exists_unimodular_to_basis_vector a l0 hunit`. Use `set N := (Q : Matrix (Fin (r+1)) (Fin (r+1)) R).map (algebraMap R K) * M with hN`. Establish `hN0 : ∀ l, N l 0 = (ρ 0)⁻¹ * algebraMap R K ((Pi.single 0 1 : Fin (r+1) → R) l)` using `fun l => by`. Rewrite using `[← hQ]`. Simplify using `only [N, Matrix.mul_apply, Matrix.map_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, ha, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, ← mul_assoc (ρ 0)⁻¹, inv_mul_cancel₀ hρ0, one_mul]`. Establish `hM' : ∀ t i, ‖θ t (ρ i.succ)‖ * matNorm ((N.submatrix Fin.succ Fin.succ).map (θ t)) i = 1` using `fun t i => by`. Set `f : R →+* C t` to `(θ t).comp (algebraMap R K)`. Establish `e1 : N.map (θ t) = (Q : Matrix (Fin (r+1)) (Fin (r+1)) R).map f * M.map (θ t)`.

Rewrite using `[hN, Matrix.map_mul, Matrix.map_map]`. Both sides reduce to the same expression. Establish `e2 : matNorm (N.map (θ t)) i.succ = matNorm (M.map (θ t)) i.succ`. Rewrite using `[e1]`. Use `GlobalTheory.T.matrix_norm_invariant_unimodular ((Q : Matrix (Fin (r+1)) (Fin (r+1)) R).map f) ((↑Q⁻¹ : Matrix (Fin (r+1)) (Fin (r+1)) R).map f) _ ?_ (fun l k => h1 t _) (fun l k => h1 t _) _` and prove the remaining obligations.

Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero f) (map_one f)]`. Establish `e3 : matNorm (N.map (θ t)) i.succ = matNorm ((N.map (θ t)).submatrix Fin.succ Fin.succ) i`. Use `GlobalTheory.T.matrix_norm_block_reduction _ ?_ ?_ i` and prove the remaining obligations. Rewrite using `[Matrix.map_apply, hN0]`. Simplify using `[hρ0]`.

Introduce `l`. Rewrite using `[Matrix.map_apply, hN0]`. Simplify using the standard rewrite rules. Establish `e4 : (N.submatrix Fin.succ Fin.succ).map (θ t) = (N.map (θ t)).submatrix Fin.succ Fin.succ` using `rfl`. Rewrite using `[e4, ← e3, e2]`.

Conclude with `hM t i.succ`. Take `⟨P', hP'1, hP'2⟩` from `ih (N.submatrix Fin.succ Fin.succ) (fun i => ρ i.succ) hM'`. Take `⟨D, hD00, hD0s, hDs0, hDss⟩` from `GlobalTheory.T.unimodular_block_form P'`. Establish `eP : ((D * Q : GL (Fin (r+1)) R) : Matrix (Fin (r+1)) (Fin (r+1)) R).map (algebraMap R K) * M = (D : Matrix (Fin (r+1)) (Fin (r+1)) R).map (algebraMap R K) * N`. Rewrite using `[Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]`.

Establish `hrow0 : ∀ j, ((D : Matrix (Fin (r+1)) (Fin (r+1)) R).map (algebraMap R K) * N) 0 j = N 0 j` using `fun j => by`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_succ, hD00, hD0s]`. Establish `hrows : ∀ l j, ((D : Matrix (Fin (r+1)) (Fin (r+1)) R).map (algebraMap R K) * N) l.succ j = ∑ k, algebraMap R K ((P' : Matrix (Fin r) (Fin r) R) l k) * N k.succ j` using `fun l j => by`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_succ, hDs0, hDss]`. Use `⟨D * Q, ?_, ?_⟩` and prove the remaining obligations.

Introduce `l j hjl`. Rewrite using `[eP]`. Proceed by induction on `l using Fin.cases with`. Consider the case `zero => exact absurd hjl (Fin.not_lt_zero _)`. Consider the case `succ l`.

Rewrite using `[hrows]`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => exact Finset.sum_eq_zero fun k _ => by rw [hN0]; simp`. Consider the case `succ j => exact hP'1 l j (Fin.succ_lt_succ_iff.1 hjl)`. Introduce `j`.

Rewrite using `[eP]`. Proceed by induction on `j using Fin.cases with`. Consider the case `zero => rw [hrow0, hN0]`. Simplify using `[hρ0]`. Consider the case `succ j => rw [hrows]`.

Conclude with `hP'2 j`.
-/
theorem GlobalTheory.TriFrame.exists_gl_upperTri_of_matNorm : ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Field K] [Algebra R K] (ι : Type) (C : ι → Type) [∀ t, NontriviallyNormedField (C t)] [∀ t, IsUltrametricDist (C t)] (θ : ∀ t, K →+* C t), (∀ t a, ‖θ t (algebraMap R K a)‖ ≤ 1) → (∀ κ : K, (∀ t, ‖θ t κ‖ ≤ 1) → ∃ a, algebraMap R K a = κ) → (∃ t, ∀ a ∈ maximalIdeal R, ‖θ t (algebraMap R K a)‖ < 1) → ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) K) (ρ : Fin r → K), (∀ t i, ‖θ t (ρ i)‖ * matNorm (M.map (θ t)) i = 1) → ∃ P : GL (Fin r) R, (∀ l j, j < l → ((P : Matrix (Fin r) (Fin r) R).map (algebraMap R K) * M) l j = 0) ∧ ∀ j, ((P : Matrix (Fin r) (Fin r) R).map (algebraMap R K) * M) j j * ρ j = 1 := by
  intro R K _ _ _ _ ι C _ _ θ h1 h2 h3 r
  obtain ⟨t0, ht0⟩ := h3
  induction r with
  | zero => intro M ρ _; exact ⟨1, fun l => l.elim0, fun j => j.elim0⟩
  | succ r ih =>
    intro M ρ hM
    have hcol : ∀ t, ‖θ t (ρ 0)‖ * Finset.univ.sup' Finset.univ_nonempty (fun l => ‖θ t (M l 0)‖) = 1 := fun t => by
      have := hM t 0; rwa [GlobalTheory.T.matrix_norm_first_column] at this
    have hint : ∀ l, ∃ a, algebraMap R K a = ρ 0 * M l 0 := fun l => h2 _ fun t => by
      rw [map_mul, norm_mul, ← hcol t]
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun l => ‖θ t (M l 0)‖) (Finset.mem_univ l)) (norm_nonneg _)
    choose a ha using hint
    obtain ⟨l0, -, hl0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun l => ‖θ t0 (M l 0)‖)
    have hunit : IsUnit (a l0) := by
      by_contra hn
      have := ht0 _ ((IsLocalRing.mem_maximalIdeal _).2 hn)
      rw [ha, map_mul, norm_mul, ← hl0, hcol t0] at this
      exact lt_irrefl _ this
    have hρ0 : ρ 0 ≠ 0 := by
      intro h; have := hcol t0; rw [h, map_zero, norm_zero, zero_mul] at this; exact zero_ne_one this
    obtain ⟨Q, hQ⟩ := GlobalTheory.T.exists_unimodular_to_basis_vector a l0 hunit
    set N := (Q : Matrix (Fin (r+1)) (Fin (r+1)) R).map (algebraMap R K) * M with hN
    have hN0 : ∀ l, N l 0 = (ρ 0)⁻¹ * algebraMap R K ((Pi.single 0 1 : Fin (r+1) → R) l) := fun l => by
      rw [← hQ]
      simp only [N, Matrix.mul_apply, Matrix.map_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_left_comm, ← mul_assoc (ρ 0)⁻¹, inv_mul_cancel₀ hρ0, one_mul]
    have hM' : ∀ t i, ‖θ t (ρ i.succ)‖ * matNorm ((N.submatrix Fin.succ Fin.succ).map (θ t)) i = 1 := fun t i => by
      let f : R →+* C t := (θ t).comp (algebraMap R K)
      have e1 : N.map (θ t) = (Q : Matrix (Fin (r+1)) (Fin (r+1)) R).map f * M.map (θ t) := by
        rw [hN, Matrix.map_mul, Matrix.map_map]; rfl
      have e2 : matNorm (N.map (θ t)) i.succ = matNorm (M.map (θ t)) i.succ := by
        rw [e1]
        refine GlobalTheory.T.matrix_norm_invariant_unimodular ((Q : Matrix (Fin (r+1)) (Fin (r+1)) R).map f) ((↑Q⁻¹ : Matrix (Fin (r+1)) (Fin (r+1)) R).map f) _ ?_ (fun l k => h1 t _) (fun l k => h1 t _) _
        rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero f) (map_one f)]
      have e3 : matNorm (N.map (θ t)) i.succ = matNorm ((N.map (θ t)).submatrix Fin.succ Fin.succ) i := by
        refine GlobalTheory.T.matrix_norm_block_reduction _ ?_ ?_ i
        · rw [Matrix.map_apply, hN0]; simp [hρ0]
        · intro l; rw [Matrix.map_apply, hN0]; simp
      have e4 : (N.submatrix Fin.succ Fin.succ).map (θ t) = (N.map (θ t)).submatrix Fin.succ Fin.succ := rfl
      rw [e4, ← e3, e2]; exact hM t i.succ
    obtain ⟨P', hP'1, hP'2⟩ := ih (N.submatrix Fin.succ Fin.succ) (fun i => ρ i.succ) hM'
    obtain ⟨D, hD00, hD0s, hDs0, hDss⟩ := GlobalTheory.T.unimodular_block_form P'
    have eP : ((D * Q : GL (Fin (r+1)) R) : Matrix (Fin (r+1)) (Fin (r+1)) R).map (algebraMap R K) * M
        = (D : Matrix (Fin (r+1)) (Fin (r+1)) R).map (algebraMap R K) * N := by
      rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]
    have hrow0 : ∀ j, ((D : Matrix (Fin (r+1)) (Fin (r+1)) R).map (algebraMap R K) * N) 0 j = N 0 j := fun j => by
      simp [Matrix.mul_apply, Fin.sum_univ_succ, hD00, hD0s]
    have hrows : ∀ l j, ((D : Matrix (Fin (r+1)) (Fin (r+1)) R).map (algebraMap R K) * N) l.succ j
        = ∑ k, algebraMap R K ((P' : Matrix (Fin r) (Fin r) R) l k) * N k.succ j := fun l j => by
      simp [Matrix.mul_apply, Fin.sum_univ_succ, hDs0, hDss]
    refine ⟨D * Q, ?_, ?_⟩
    · intro l j hjl
      rw [eP]
      induction l using Fin.cases with
      | zero => exact absurd hjl (Fin.not_lt_zero _)
      | succ l =>
        rw [hrows]
        induction j using Fin.cases with
        | zero => exact Finset.sum_eq_zero fun k _ => by rw [hN0]; simp
        | succ j => exact hP'1 l j (Fin.succ_lt_succ_iff.1 hjl)
    · intro j
      rw [eP]
      induction j using Fin.cases with
      | zero => rw [hrow0, hN0]; simp [hρ0]
      | succ j => rw [hrows]; exact hP'2 j
