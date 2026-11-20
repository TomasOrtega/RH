import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Unfold `iy`. Use `split_ifs`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `pLoc ℚ v ((1 : Af ℚ) - 0 + 0) = 1`. Rewrite using `[sub_zero, add_zero, map_one]`.
-/
private theorem cp_iy (v : H.P ℚ) (r : ℝ) : H.cp v ((iy r : (A ℚ)ˣ) : A ℚ) = 1 := by
  unfold iy
  split_ifs
  · simp
  · change pLoc ℚ v ((1 : Af ℚ) - 0 + 0) = 1
    rw [sub_zero, add_zero, map_one]

/- English proof (translation)
Unfold `pin`. Use `finprod_induction (fun x : (A ℚ)ˣ => H.cp v (x : A ℚ) = 1) (by simp) ?_ ?_` and prove the remaining obligations. Introduce `x y hx hy`. Rewrite using `[Units.val_mul, map_mul, hx, hy, one_mul]`. Introduce `v'`.

Distinguish the cases in `hv : v = v'`. Substitute `hv` using the available equality. Rewrite using `[Nat.factorization_eq_zero_of_not_dvd h]`. Simplify using the standard rewrite rules. Establish `: H.cp v ((pv v' : (A ℚ)ˣ) : A ℚ) = 1` using `by classical`.

Conclude with `Pi.mulSingle_eq_of_ne hv _`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow, this, one_pow]`.
-/
private theorem cp_pin (v : H.P ℚ) (n : ℕ) (h : ¬ normV v ∣ n) :
    H.cp v ((pin n : (A ℚ)ˣ) : A ℚ) = 1 := by
  unfold pin
  refine finprod_induction (fun x : (A ℚ)ˣ => H.cp v (x : A ℚ) = 1) (by simp) ?_ ?_
  · intro x y hx hy
    rw [Units.val_mul, map_mul, hx, hy, one_mul]
  · intro v'
    by_cases hv : v = v'
    · subst hv
      rw [Nat.factorization_eq_zero_of_not_dvd h]
      simp
    · have : H.cp v ((pv v' : (A ℚ)ˣ) : A ℚ) = 1 := by
        classical
        exact Pi.mulSingle_eq_of_ne hv _
      rw [Units.val_pow_eq_pow_val, map_pow, this, one_pow]

/- English proof (translation)
Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun y : GL (Fin 2) (Af ℚ) => pLoc ℚ v (y.val i j)) (TR.pFin_infGL (E := ℚ) (a := 2) _ : Matrix.GeneralLinearGroup.map (pFin ℚ) (rot t) = 1)`. Use `h.trans ?_` and prove the remaining obligations. Simplify using `only [Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem cp_rot (v : H.P ℚ) (t : ℝ) :
    Matrix.GeneralLinearGroup.map (H.cp v) (rot t) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h := congrArg (fun y : GL (Fin 2) (Af ℚ) => pLoc ℚ v (y.val i j)) (TR.pFin_infGL (E := ℚ) (a := 2) _ :
    Matrix.GeneralLinearGroup.map (pFin ℚ) (rot t) = 1)
  refine h.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `H.cp v ((aE a).val i j) = _`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aE, h]`.
-/
private theorem cp_aE (v : H.P ℚ) (a : (A ℚ)ˣ) (h : H.cp v (a : A ℚ) = 1) :
    Matrix.GeneralLinearGroup.map (H.cp v) (aE a) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change H.cp v ((aE a).val i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE, h]

/- English proof (translation)
Introduce `E _ _ v n r t _ h w hw`. Establish `hx : Matrix.GeneralLinearGroup.map (H.cp v) (aE (iy r * pin n) * rot t) = 1`. Rewrite using `[map_mul, cp_rot, cp_aE v _ (by rw [Units.val_mul, map_mul, cp_iy, cp_pin v n h, one_mul]), one_mul]`. Generalize the expression as in `aE (iy r * pin n) * rot t = x at hx`. Substitute `hw` using the available equality.

Establish `: Matrix.GeneralLinearGroup.map (H.cp w) (em E x) = 1`. Use `Matrix.GeneralLinearGroup.ext fun i j => ?_` and prove the remaining obligations. Establish `e : H.cp (w.under (𝓞 ℚ)) (x.val i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j` using `congrArg (fun y : GL (Fin 2) _ => y.val i j) hx`. Express the relevant statement in the definitionally equal form `GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w (H.cp (w.under (𝓞 ℚ)) (x.val i j)) = (1 : Matrix (Fin 2) (Fin 2) _) i j`. Rewrite using `[e, Matrix.one_apply, Matrix.one_apply]`.

Use `split_ifs`. Conclude with `map_one (GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w)`. Conclude with `map_zero (GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w)`. Unfold `H.KAt`. Rewrite using `[this]`.

Conclude with `one_mem _`.
-/
theorem UpperTheory.kAt_diag_ideleOfNat_mul_rotation_of_not_dvd :
    ∀ (E : Type) [Field E] [NumberField E] (v : H.P ℚ) (n : ℕ) (r t : ℝ), 0 < n → ¬ normV v ∣ n → ∀ w : H.P E, w.under (𝓞 ℚ) = v →
          H.KAt w (em E (aE (iy r * pin n) * rot t)) := by
  intro E _ _ v n r t _ h w hw
  have hx : Matrix.GeneralLinearGroup.map (H.cp v) (aE (iy r * pin n) * rot t) = 1 := by
    rw [map_mul, cp_rot, cp_aE v _ (by rw [Units.val_mul, map_mul, cp_iy, cp_pin v n h, one_mul]), one_mul]
  generalize aE (iy r * pin n) * rot t = x at hx
  subst hw
  have : Matrix.GeneralLinearGroup.map (H.cp w) (em E x) = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have e : H.cp (w.under (𝓞 ℚ)) (x.val i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j :=
      congrArg (fun y : GL (Fin 2) _ => y.val i j) hx
    change GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w (H.cp (w.under (𝓞 ℚ)) (x.val i j)) = (1 : Matrix (Fin 2) (Fin 2) _) i j
    rw [e, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one (GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w)
    · exact map_zero (GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w)
  unfold H.KAt
  rw [this]
  exact one_mem _
