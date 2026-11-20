import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MulVecInt

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {D : D7}

def IntM {D : D7} {m p : ℕ} (v : Pl D) (M : Mx D m p) : Prop := ∀ i j, cv D v (M i j) ∈ intLoc D.host.F D.host.E v

namespace IntM

variable {v : Pl D} {m p q : ℕ}

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem add {M N : Mx D m p} (hM : IntM v M) (hN : IntM v N) : IntM v (M + N) := fun i j => by
  rw [Matrix.add_apply, map_add]; exact add_mem (hM i j) (hN i j)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem neg {M : Mx D m p} (hM : IntM v M) : IntM v (-M) := fun i j => by
  rw [Matrix.neg_apply, map_neg]; exact neg_mem (hM i j)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem zero : IntM v (0 : Mx D m p) := fun i j => by
  rw [Matrix.zero_apply, map_zero]; exact zero_mem _

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem one : IntM v (1 : Mx D m m) := fun i j => by
  rw [Matrix.one_apply]
  split_ifs
  · rw [map_one]; exact one_mem _
  · rw [map_zero]; exact zero_mem _

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem mul {M : Mx D m p} {N : Mx D p q} (hM : IntM v M) (hN : IntM v N) : IntM v (M * N) := fun i j => by
  rw [Matrix.mul_apply, map_sum]
  exact sum_mem fun k _ => by rw [map_mul]; exact mul_mem (hM i k) (hN k j)

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem inv {M : Mx D m m} (hM : IntM v M) (hu : IsUnit M.det)
    (hdet : ∃ z ∈ intLoc D.host.F D.host.E v, cv D v M.det * z = 1) : IntM v M⁻¹ := by
  obtain ⟨z, hz, hdz⟩ := hdet
  obtain ⟨u, hu'⟩ := hu
  have hinv : cv D v (Ring.inverse M.det) = z := by
    rw [← hu', Ring.inverse_unit]
    have h1 : cv D v ((u⁻¹ : (AE D)ˣ) : AE D) * cv D v (u : AE D) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hu'] at h1
    calc cv D v ((u⁻¹ : (AE D)ˣ) : AE D) = cv D v ((u⁻¹ : (AE D)ˣ) : AE D) * (cv D v M.det * z) := by
          rw [hdz, mul_one]
      _ = z := by rw [← mul_assoc, h1, one_mul]

  let N : Matrix (Fin m) (Fin m) (intLoc D.host.F D.host.E v) := fun i j => ⟨cv D v (M i j), hM i j⟩
  have hN : N.map (intLoc D.host.F D.host.E v).subtype = M.map (cv D v) := rfl
  have hadj : ∀ i j, cv D v (M.adjugate i j) ∈ intLoc D.host.F D.host.E v := by
    intro i j
    have e1 : cv D v (M.adjugate i j) = (M.map (cv D v)).adjugate i j :=
      congrFun (congrFun (RingHom.map_adjugate (cv D v) M) i) j
    have e2 : (intLoc D.host.F D.host.E v).subtype (N.adjugate i j) =
        (N.map (intLoc D.host.F D.host.E v).subtype).adjugate i j :=
      congrFun (congrFun (RingHom.map_adjugate (intLoc D.host.F D.host.E v).subtype N) i) j
    rw [e1, ← hN, ← e2]
    exact (N.adjugate i j).2
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, hinv]
  exact mul_mem hz (hadj i j)

end IntM

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem integral_block_matrix_iff {v : Pl D} {n : ℕ} {a b c d : Mx D n n} :
    IntM v (blk4 a b c d) ↔ IntM v a ∧ IntM v b ∧ IntM v c ∧ IntM v d := by
  have key : ∀ x y, blk4 a b c d (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.fromBlocks a b c d x y := by
    intro x y; simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · have := h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j))
      rwa [key, Matrix.fromBlocks_apply₁₁] at this
    · have := h (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))
      rwa [key, Matrix.fromBlocks_apply₁₂] at this
    · have := h (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j))
      rwa [key, Matrix.fromBlocks_apply₂₁] at this
    · have := h (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))
      rwa [key, Matrix.fromBlocks_apply₂₂] at this
  · rintro ⟨ha, hb, hc, hd⟩ i j
    obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
    show cv D v (blk4 a b c d _ _) ∈ _
    rw [key]
    rcases i' with i' | i' <;> rcases j' with j' | j'
    · rw [Matrix.fromBlocks_apply₁₁]; exact ha i' j'
    · rw [Matrix.fromBlocks_apply₁₂]; exact hb i' j'
    · rw [Matrix.fromBlocks_apply₂₁]; exact hc i' j'
    · rw [Matrix.fromBlocks_apply₂₂]; exact hd i' j'

end PositivityTheory.Rg.Rsw.L.LGenK
