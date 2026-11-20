import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockRelationTwistedHeight

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ}

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lift_lift_V (j ρ n r : ℕ) (hn : 1 + ρ = n) (h1 : j + n = r) (h2 : j + 1 + ρ = r)
    (v : Fin (2 * ρ + k + 1) → ℂ) :
    D.castV h1 (liftVec k j n (D.castV hn (liftVec k 1 ρ v))) = D.castV h2 (liftVec k (j + 1) ρ v) := by
  funext i
  simp only [D.castV, liftVec, Fin.coe_cast]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, Fin.coe_cast] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk, Fin.coe_cast] <;> omega)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem lift_lift_M (j ρ n r : ℕ) (hn : 1 + ρ = n) (h1 : j + n = r) (h2 : j + 1 + ρ = r) (y : B.Mat k ρ) :
    D.castM h1 (ιLev k j n (D.castM hn (ιLev k 1 ρ y))) = D.castM h2 (ιLev k (j + 1) ρ y) := by
  ext p q
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Fin.coe_cast, ιLev]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, Fin.coe_cast] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk, Fin.coe_cast] <;> omega)

/- English proof (translation)
Substitute using the available equality. Apply function extensionality and compare values at an arbitrary argument. Simplify to obtain the desired conclusion from the available facts.
-/
theorem castV_inj {a b : ℕ} (h : a = b) {v w : Fin (2 * a + k + 1) → ℂ} (e : D.castV h v = D.castV h w) : v = w := by
  subst h
  funext i
  simpa [D.castV] using congrFun e i

section tower

variable {r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem levTower_bs_z_eq_castV_liftVec (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) :
    (T.bs j).z = D.castV (by omega : 1 + (r - (j + 1)) = r - j) (liftVec k 1 (r - (j + 1)) (T.bs (j + 1)).z) := by
  have e1 := T.z_lev j (by omega)
  have e2 := T.z_lev (j + 1) hj
  rw [← lift_lift_V j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)] at e2
  have e3 := castV_inj _ (e1.trans e2.symm)
  funext i
  have hi := i.isLt
  have hi' : i.val ≤ 2 * (r - j) + k := by omega
  have := congrFun e3 ⟨i.val + j, by omega⟩
  simpa [liftVec, hi'] using this

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem levTower_bs_z'_eq_castV_liftVec (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) :
    (T.bs j).z' = D.castV (by omega : 1 + (r - (j + 1)) = r - j) (liftVec k 1 (r - (j + 1)) (T.bs (j + 1)).z') := by
  have e1 := T.z'_lev j (by omega)
  have e2 := T.z'_lev (j + 1) hj
  rw [← lift_lift_V j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)] at e2
  have e3 := castV_inj _ (e1.trans e2.symm)
  funext i
  have hi := i.isLt
  have hi' : i.val ≤ 2 * (r - j) + k := by omega
  have := congrFun e3 ⟨i.val + j, by omega⟩
  simpa [liftVec, hi'] using this

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem tower_π (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) (y : B.Mat k (r - (j + 1))) :
    (T.bs (j + 1)).π y = (T.bs j).π (D.castM (by omega : 1 + (r - (j + 1)) = r - j) (ιLev k 1 (r - (j + 1)) y)) := by
  rw [T.π_lev (j + 1) hj y, T.π_lev j (by omega),
    lift_lift_M j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem tower_π' (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) (y : B.Mat k (r - (j + 1))) :
    (T.bs (j + 1)).π' y = (T.bs j).π' (D.castM (by omega : 1 + (r - (j + 1)) = r - j) (ιLev k 1 (r - (j + 1)) y)) := by
  rw [T.π'_lev (j + 1) hj y, T.π'_lev j (by omega),
    lift_lift_M j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)]

end tower

end Formalism.FourierDecayAlt.P.PBH
