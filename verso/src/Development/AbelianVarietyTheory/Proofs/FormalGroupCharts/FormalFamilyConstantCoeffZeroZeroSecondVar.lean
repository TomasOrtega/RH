import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalEvSecondPointOfXZero

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d : ℕ}

/- English proof (translation)
Establish `hz : CZ (fun (_ : Fin n) (_ : Fin d) => (0 : PS k n d))` using `fun _ _ => map_zero _`. Establish `h1` using `ev_zeroFam (n := n) (ev a f)`. Rewrite `h1` using `[ev_ev hz ha]`. Establish `e : (fun j i => ev (fun (_ : Fin n) (_ : Fin d) => (0 : PS k n d)) (a j i)) = fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d)`. Use function extensionality and compare the values at `j i`.

Rewrite using `[ev_zeroFam, ha j i, map_zero]`. Rewrite `h1` using `[e, ev_zeroFam]`. Simplify using `using (congrArg constantCoeff h1).symm`.
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
The claim follows from `CZ.cons cc_zero (CZ.cons (cc_pt 0) CZ.nil)`.
-/
theorem formalFamilyConstantCoeffZero_zero_secondVar : CZ (![0, pt k (n := 1) d 0] : Fin 2 → Pt k 1 d) := CZ.cons cc_zero (CZ.cons (cc_pt 0) CZ.nil)

/- English proof (translation)
Rewrite using `[Jac, cc_ev cz1, ← cc_ev formalFamilyConstantCoeffZero_zero_secondVar]`. Establish `h` using `congrArg (pderiv k ((0 : Fin 1), b)) (G.unit i)`. Rewrite `h` using `[pderiv_ev formalFamilyConstantCoeffZero_zero_secondVar, Fintype.sum_prod_type, Fin.sum_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, zero_add, pderiv_pt] at h`. Simplify using `only [Fin.isValue, Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`.

Rewrite using `[h, pderiv_X]`. Simplify using `[Pi.single_apply, eq_comm]`.
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
Use `Matrix.ext fun i b => ?_` and prove the remaining obligations. Simplify using `[JM, cc_jac, Matrix.one_apply]`.
-/
theorem jm_map_cc : (JM G).map constantCoeff = 1 := by
  refine Matrix.ext fun i b => ?_
  simp [JM, cc_jac, Matrix.one_apply]

/- English proof (translation)
Rewrite using `[MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, jm_map_cc, Matrix.det_one]`. Conclude with `isUnit_one`.
-/
theorem isUnit_det_jm : IsUnit (JM G).det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, jm_map_cc,
    Matrix.det_one]
  exact isUnit_one

/- English proof (translation)
The claim follows from `Matrix.nonsing_inv_mul _ (isUnit_det_jm G)`.
-/
theorem om_mul : Om G * JM G = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_jm G)

/- English proof (translation)
The claim follows from `Matrix.mul_nonsing_inv _ (isUnit_det_jm G)`.
-/
theorem mul_om : JM G * Om G = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_jm G)

/- English proof (translation)
Establish `h : (M * N).map (evHom ha) = M.map (evHom ha) * N.map (evHom ha)` using `Matrix.map_mul`. Establish `e : (⇑(evHom ha)) = ev a` using `funext (evHom_apply ha)`. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem map_ev_mul {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (M N : Matrix (Fin d) (Fin d) (PS k m d)) :
    (M * N).map (ev a) = M.map (ev a) * N.map (ev a) := by
  have h : (M * N).map (evHom ha) = M.map (evHom ha) * N.map (evHom ha) := Matrix.map_mul
  have e : (⇑(evHom ha)) = ev a := funext (evHom_apply ha)
  rw [e] at h
  exact h

/- English proof (translation)
Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[← evHom_apply ha]`. Simplify using `[h, ev_zero' ha]`.
-/
theorem map_ev_one {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) :
    (1 : Matrix (Fin d) (Fin d) (PS k m d)).map (ev a) = 1 := by
  refine Matrix.ext fun i j => ?_
  by_cases h : i = j
  · subst h; simp [← evHom_apply ha]
  · simp [h, ev_zero' ha]

/- English proof (translation)
Establish `h` using `congrArg (fun M => M.map constantCoeff) (mul_om G)`. Simplify using `only [Matrix.map_mul (f := constantCoeff), jm_map_cc, Matrix.one_mul] at h`. Apply the tactic sequence `rw [h]; refine Matrix.ext fun i j => ?_; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.
-/
theorem cc_om : (Om G).map constantCoeff = 1 := by
  have h := congrArg (fun M => M.map constantCoeff) (mul_om G)
  simp only [Matrix.map_mul (f := constantCoeff), jm_map_cc, Matrix.one_mul] at h
  rw [h]; refine Matrix.ext fun i j => ?_; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/- English proof (translation)
Establish `hJ : (JM G).map (ev (n` using `2) ![G.F]) = Matrix.of (Ar G) * (JM G).map (ev (n := 2) ![pt k d 1]) := by`. Use `Matrix.ext fun i b => ?_` and prove the remaining obligations. Simplify using `only [Matrix.map_apply, JM, Matrix.of_apply, Matrix.mul_apply]`. Conclude with `jac_F G i b`. Establish `hy : (JM G).map (ev (n` using `2) ![pt k d 1]) * (Om G).map (ev (n := 2) ![pt k d 1]) = 1 := by`.

Rewrite using `[← map_ev_mul czY, mul_om, map_ev_one czY]`. Establish `hF : (Om G).map (ev (n` using `2) ![G.F]) * (JM G).map (ev (n := 2) ![G.F]) = 1 := by`. Rewrite using `[← map_ev_mul (czFF G), om_mul, map_ev_one (czFF G)]`. Establish `key : (Om G).map (ev (n` using `2) ![G.F]) * Matrix.of (Ar G) = (Om G).map (ev (n := 2) ![pt k d 1]) := by`. Combine the equalities or inequalities in the displayed calculation.

Use `congrFun (congrFun key i) b` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply]`.
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
The claim follows from `CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)`.
-/
theorem czSw : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)
/- English proof (translation)
The claim follows from `CZ.cons (cc_pt 0) CZ.nil`.
-/
theorem czX : CZ (![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt 0) CZ.nil

/- English proof (translation)
Rewrite using `[ev_ev czSw (czFF G)]`. Use `congr 1`. Use function extensionality and compare the values at `j c`. Use `fin_cases j`. Conclude with `G.comm c`.
-/
theorem sw_F (h : PS k 1 d) : ev (n := 2) ![pt k d 1, pt k d 0] (ev (n := 2) ![G.F] h) = ev (n := 2) ![G.F] h := by
  rw [ev_ev czSw (czFF G)]
  congr 1
  funext j c
  fin_cases j
  exact G.comm c

/- English proof (translation)
Rewrite using `[ev_ev czSw czY]`. Use `congr 1`. Use function extensionality and compare the values at `j c`. Use `fin_cases j`. Simplify using `[pt_apply, ev_X czSw]`.
-/
theorem sw_y (h : PS k 1 d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (ev (n := 2) ![pt k d 1] h) = ev (n := 2) ![pt k d 0] h := by
  rw [ev_ev czSw czY]
  congr 1
  funext j c
  fin_cases j
  simp [pt_apply, ev_X czSw]

/- English proof (translation)
Establish `h` using `congrArg (pderiv k ((0 : Fin 2), b)) (G.comm j)`. Rewrite `h` using `[pderiv_ev czSw, Fintype.sum_prod_type, Fin.sum_univ_two]`. Simplify using `[pderiv_pt] at h`. Conclude with `h`.
-/
theorem sw_dF (j b : Fin d) :
    ev (n := 2) ![pt k d 1, pt k d 0] (pderiv k ((1 : Fin 2), b) (G.F j)) = pderiv k ((0 : Fin 2), b) (G.F j) := by
  have h := congrArg (pderiv k ((0 : Fin 2), b)) (G.comm j)
  rw [pderiv_ev czSw, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp [pderiv_pt] at h
  exact h

/- English proof (translation)
Establish `h` using `congrArg (ev (n := 2) ![pt k d 1, pt k d 0]) (om_Q G i a)`. Rewrite `h` using `[ev_sum czSw, sw_y]`. Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[ev_mul czSw, sw_F, Ar, sw_dF]`.
-/
theorem om_P (i a : Fin d) :
    ∑ j, ev (n := 2) ![G.F] (Om G i j) * pderiv k ((0 : Fin 2), a) (G.F j) = ev (n := 2) ![pt k d 0] (Om G i a) := by
  have h := congrArg (ev (n := 2) ![pt k d 1, pt k d 0]) (om_Q G i a)
  rw [ev_sum czSw, sw_y] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_mul czSw, sw_F, Ar, sw_dF]

/- English proof (translation)
Rewrite using `[pderiv_ev (czFF G), Fintype.sum_prod_type, Fin.sum_univ_one]`. Both sides reduce to the same expression.
-/
theorem d_evF (h : PS k 1 d) (v : Fin 2 × Fin d) :
    pderiv k v (ev (n := 2) ![G.F] h) = ∑ c, ev (n := 2) ![G.F] (pderiv k ((0 : Fin 1), c) h) * pderiv k v (G.F c) := by
  rw [pderiv_ev (czFF G), Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

/- English proof (translation)
Rewrite using `[ev_ev cz1 (czFF G)]`. Use `conv_rhs => rw [← ev_pt h]`. Use `congr 1`. Use function extensionality and compare the values at `j c`. Use `fin_cases j`.

Conclude with `formalGroupLaw_ev_x_zero G c`.
-/
theorem ez_F (h : PS k 1 d) : ev (n := 1) ![pt k d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  rw [ev_ev cz1 (czFF G)]
  conv_rhs => rw [← ev_pt h]
  congr 1
  funext j c
  fin_cases j
  exact formalGroupLaw_ev_x_zero G c

/- English proof (translation)
Establish `h` using `congrArg (pderiv k ((0 : Fin 1), a)) (formalGroupLaw_ev_x_zero G j)`. Rewrite `h` using `[pderiv_ev cz1, Fintype.sum_prod_type, Fin.sum_univ_two]`. Simplify using `[pderiv_pt] at h`. Rewrite using `[h, pderiv_X]`. Simplify using `[Pi.single_apply]`.
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
Establish `hQ` using `congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) g)) (om_Q G i b)`. Establish `hP` using `congrArg (fun g => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) g)) (om_P G i a)`. Use `beta_reduce at hQ hP`. Rewrite `hQ` using `[pderiv_ev_zero czY _ _ (fun j l => by fin_cases j; simp [pderiv_pt]), ev_zero' cz1]`. Rewrite `hP` using `[pderiv_ev_zero czX _ _ (fun j l => by fin_cases j; simp [pderiv_pt]), ev_zero' cz1]`.

Simplify using `only [map_sum, Derivation.leibniz, smul_eq_mul, d_evF, ev_sum cz1, ev_add cz1, ev_mul cz1, ez_F, ez_dx, ez_dy, Ar, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hQ hP`. Rewrite `hQ`, `hP` using `[Finset.sum_add_distrib]`. Establish `hR : ∑ j, Om G i j * ev (n` using `1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), a) (pderiv k ((1 : Fin 2), b) (G.F j))) = ∑ j, Om G i j * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (pderiv k ((0 : Fin 2), a) (G.F j))) := by`. Simplify using `only [pderiv_comm ((0 : Fin 2), a) ((1 : Fin 2), b)]`. Simplify using `only [Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, one_mul, zero_mul] at hQ hP`.

Rewrite `hQ` using `[hR]`. Take the linear combination `hQ - hP`.
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
