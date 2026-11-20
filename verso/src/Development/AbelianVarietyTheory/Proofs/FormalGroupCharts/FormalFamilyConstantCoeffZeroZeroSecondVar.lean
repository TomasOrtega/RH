import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalEvSecondPointOfXZero

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d : ℕ}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem cc_ev {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have hz : CZ (fun (_ : Fin n) (_ : Fin d) => (0 : PS k n d)) := fun _ _ => map_zero _
  have h1 := ev_zeroFam (n := n) (ev a f)
  rw [ev_ev hz ha] at h1
  have e : (fun j i => ev (fun (_ : Fin n) (_ : Fin d) => (0 : PS k n d)) (a j i)) =
      fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d) := by
    funext j i; rw [ev_zeroFam, ha j i, map_zero]
  rw [e, ev_zeroFam] at h1
  simpa using (congrArg constantCoeff h1).symm

variable (G : FGLaw k d)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem formalFamilyConstantCoeffZero_zero_secondVar : CZ (![0, pt k (n := 1) d 0] : Fin 2 → Pt k 1 d) := CZ.cons cc_zero (CZ.cons (cc_pt 0) CZ.nil)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem cc_jac (i b : Fin d) : constantCoeff (Jac G i b) = if i = b then 1 else 0 := by
  rw [Jac, cc_ev cz1, ← cc_ev formalFamilyConstantCoeffZero_zero_secondVar]
  have h := congrArg (pderiv k ((0 : Fin 1), b)) (G.unit i)
  rw [pderiv_ev formalFamilyConstantCoeffZero_zero_secondVar, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, map_zero, mul_zero,
    Finset.sum_const_zero, zero_add, pderiv_pt] at h
  simp only [Fin.isValue, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h
  rw [h, pderiv_X]
  simp [Pi.single_apply, eq_comm]

def JM : Matrix (Fin d) (Fin d) (PS k 1 d) := Matrix.of (Jac G)

def Om : Matrix (Fin d) (Fin d) (PS k 1 d) := (JM G)⁻¹

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem jm_map_cc : (JM G).map constantCoeff = 1 := by
  refine Matrix.ext fun i b => ?_
  simp [JM, cc_jac, Matrix.one_apply]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isUnit_det_jm : IsUnit (JM G).det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, jm_map_cc,
    Matrix.det_one]
  exact isUnit_one

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem om_mul : Om G * JM G = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_jm G)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mul_om : JM G * Om G = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_jm G)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem map_ev_mul {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (M N : Matrix (Fin d) (Fin d) (PS k m d)) :
    (M * N).map (ev a) = M.map (ev a) * N.map (ev a) := by
  have h : (M * N).map (evHom ha) = M.map (evHom ha) * N.map (evHom ha) := Matrix.map_mul
  have e : (⇑(evHom ha)) = ev a := funext (evHom_apply ha)
  rw [e] at h
  exact h

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem map_ev_one {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) :
    (1 : Matrix (Fin d) (Fin d) (PS k m d)).map (ev a) = 1 := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h; simp [← evHom_apply ha]
  · simp [h, ev_zero' ha]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem cc_om : (Om G).map constantCoeff = 1 := by
  have h := congrArg (fun M => M.map constantCoeff) (mul_om G)
  simp only [Matrix.map_mul (f := constantCoeff), jm_map_cc, Matrix.one_mul] at h
  rw [h]; refine Matrix.ext fun i j => ?_; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem om_Q (i b : Fin d) : ∑ j, ev (n := 2) ![G.F] (Om G i j) * Ar G j b = ev (n := 2) ![pt k d 1] (Om G i b) := by
  have hJ : (JM G).map (ev (n := 2) ![G.F]) = Matrix.of (Ar G) * (JM G).map (ev (n := 2) ![pt k d 1]) := by
    refine Matrix.ext fun i b => ?_
    simp only [Matrix.map_apply, JM, Matrix.of_apply, Matrix.mul_apply]
    exact jac_F G i b
  have hy : (JM G).map (ev (n := 2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1]) = 1 := by
    rw [← map_ev_mul czY, mul_om, map_ev_one czY]
  have hF : (Om G).map (ev (n := 2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) = 1 := by
    rw [← map_ev_mul (czFF G), om_mul, map_ev_one (czFF G)]
  have key : (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G) = (Om G).map (ev (n := 2) ![pt k d 1]) := by
    calc _ = (Om G).map (ev (n := 2) ![G.F]) * Matrix.of (Ar G) *
          ((JM G).map (ev (n := 2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1])) := by rw [hy, Matrix.mul_one]
      _ = (Om G).map (ev (n := 2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) *
          (Om G).map (ev (n := 2) ![pt k d 1]) := by rw [hJ, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = _ := by rw [hF, Matrix.one_mul]
  have := congrFun (congrFun key i) b
  simpa [Matrix.mul_apply] using this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem czSw : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem czX : CZ (![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt 0) CZ.nil

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem sw_F (h : PS k 1 d) : ev (n := 2) ![pt k d 1, pt k d 0] (ev (n := 2) ![G.F] h) = ev (n := 2) ![G.F] h := by
  rw [ev_ev czSw (czFF G)]
  congr 1
  funext j c
  fin_cases j
  exact G.comm c

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sw_y (h : PS k 1 d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (ev (n := 2) ![pt k d 1] h) = ev (n := 2) ![pt k d 0] h := by
  rw [ev_ev czSw czY]
  congr 1
  funext j c
  fin_cases j
  simp [pt_apply, ev_X czSw]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem sw_dF (j b : Fin d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (pderiv k ((1 : Fin 2), b) (G.F j)) = pderiv k ((0 : Fin 2), b) (G.F j) := by
  have h := congrArg (pderiv k ((0 : Fin 2), b)) (G.comm j)
  rw [pderiv_ev czSw, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pderiv_pt] at h
  exact h

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem om_P (i a : Fin d) :
    ∑ j, ev (n := 2) ![G.F] (Om G i j) * pderiv k ((0 : Fin 2), a) (G.F j) = ev (n := 2) ![pt k d 0] (Om G i a) := by
  have h := congrArg (ev (n := 2) ![pt k d 1, pt k d 0]) (om_Q G i a)
  rw [ev_sum czSw, sw_y] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_mul czSw, sw_F, Ar, sw_dF]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem d_evF (h : PS k 1 d) (v : Fin 2 × Fin d) :
    pderiv k v (ev (n := 2) ![G.F] h) = ∑ c, ev (n := 2) ![G.F] (pderiv k ((0 : Fin 1), c) h) * pderiv k v (G.F c) := by
  rw [pderiv_ev (czFF G), Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem ez_F (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  rw [ev_ev cz1 (czFF G)]
  conv_rhs => rw [← ev_pt h]
  congr 1
  funext j c
  fin_cases j
  exact formalGroupLaw_ev_x_zero G c

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem ez_dx (j a : Fin d) :
    ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) (G.F j)) = if j = a then 1 else 0 := by
  have h := congrArg (pderiv k ((0 : Fin 1), a)) (formalGroupLaw_ev_x_zero G j)
  rw [pderiv_ev cz1, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pderiv_pt] at h
  rw [h, pderiv_X]
  simp [Pi.single_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ez_dy (c b : Fin d) : ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F c)) = Jac G c b := rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. A detailed English derivation is pending.
-/
theorem om_key (i a b : Fin d) :
    ∑ j, Jac G j b * pderiv k ((0 : Fin 1), a) (Om G i j) = ∑ c, pderiv k ((0 : Fin 1), c) (Om G i a) * Jac G c b := by
  have hQ := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) g)) (om_Q G i b)
  have hP := congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) g)) (om_P G i a)
  beta_reduce at hQ hP
  rw [pderiv_ev_zero czY _ _ (fun j l => by fin_cases j; simp [pderiv_pt]), ev_zero' cz1] at hQ
  rw [pderiv_ev_zero czX _ _ (fun j l => by fin_cases j; simp [pderiv_pt]), ev_zero' cz1] at hP
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, d_evF, ev_sum cz1, ev_add cz1, ev_mul cz1, ez_F, ez_dx,
    ez_dy, Ar, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hQ hP
  rw [Finset.sum_add_distrib] at hQ hP
  have hR : ∑ j, Om G i j * ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) (pderiv k ((1 : Fin 2), b) (G.F j))) =
      ∑ j, Om G i j * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (pderiv k ((0 : Fin 2), a) (G.F j))) := by
    simp only [pderiv_comm ((0 : Fin 2), a) ((1 : Fin 2), b)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, one_mul, zero_mul] at hQ hP
  rw [hR] at hQ
  linear_combination hQ - hP

end GlobalTheory.FormalLog
