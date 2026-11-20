import Formalism.ThetaLogCoordinates.DualWeylCoordinates.FiltrationTheoremOfClauses
import Formalism.GradedWeylDivisibility.FinalB

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

variable {n : ℕ}

/- English proof (translation)
Establish `h : (evGLR (R` using `ℚ) x).comp (mapCoord ℚ) = evGL x := by`. Apply `IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det)` to reduce the goal to its premises. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using the standard rewrite rules.

Introduce `v`. Simplify using `[evGLR, mapCoord, evGL, IsLocalization.Away.lift_eq]`. Conclude with `congrArg (fun φ => φ z) h`.
-/
lemma qd_evGLR_mapCoord {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (z : GLCoord ℤ n) :
    evGLR (R := ℚ) x (mapCoord ℚ z) = evGL x z := by
  have h : (evGLR (R := ℚ) x).comp (mapCoord ℚ) = evGL x := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (genMat ℤ n).det)
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [evGLR, mapCoord, evGL, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ z) h

def qd_sig (n : ℕ) : MvPolynomial (Fin n × Fin n) ℚ →ₐ[ℚ] GLCoord ℚ n :=
  (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n)).comp (rename Prod.swap)

/- English proof (translation)
Simplify using `[qd_sig, Prod.swap]`.
-/
lemma qd_sig_X (v : Fin n × Fin n) :
    qd_sig n (X v) = algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (v.2, v.1)) := by
  simp [qd_sig, Prod.swap]

/- English proof (translation)
Introduce `h`. Use `congrArg (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℚ) else 0)) h` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Establish `h1 : (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℚ) else 0)).mapMatrix (genMat ℚ n) = 1`. Use extensionality with `a b`.

Simplify using `[genMat, Matrix.one_apply]`. Rewrite `this` using `[h1]`. Simplify using `at this`.
-/
lemma qd_genDet_ne (n : ℕ) : (genMat ℚ n).det ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℚ) else 0)) h
  rw [RingHom.map_det] at this
  have h1 : (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℚ) else 0)).mapMatrix (genMat ℚ n)
      = 1 := by
    ext a b; simp [genMat, Matrix.one_apply]
  rw [h1] at this
  simp at this

/- English proof (translation)
Establish `h1 : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n))` using `IsLocalization.injective (GLCoord ℚ n) (powers_le_nonZeroDivisors_of_noZeroDivisors (qd_genDet_ne n))`. Establish `h2 : Function.Injective (rename (R` using `ℚ) (Prod.swap : Fin n × Fin n → Fin n × Fin n)) := rename_injective _ Prod.swap_injective`. Introduce `p q hpq`. Conclude with `h2 (h1 hpq)`.
-/
lemma qd_sig_inj (n : ℕ) : Function.Injective (qd_sig n) := by
  have h1 : Function.Injective (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n)) :=
    IsLocalization.injective (GLCoord ℚ n)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (qd_genDet_ne n))
  have h2 : Function.Injective (rename (R := ℚ) (Prod.swap : Fin n × Fin n → Fin n × Fin n)) :=
    rename_injective _ Prod.swap_injective
  intro p q hpq
  exact h2 (h1 hpq)

/- English proof (translation)
Establish `h : (evGLR (R` using `ℚ) x).comp (qd_sig n).toRingHom = (aeval (R := ℚ) (fun v : Fin n × Fin n => x.val v.2 v.1)).toRingHom := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using the standard rewrite rules. Introduce `v`.

Simplify using `[qd_sig, evGLR, IsLocalization.Away.lift_eq]`. Conclude with `congrArg (fun φ => φ P) h`.
-/
lemma qd_ev_sig {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R')
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    evGLR (R := ℚ) x (qd_sig n P) = aeval (fun v : Fin n × Fin n => x.val v.2 v.1) P := by
  have h : (evGLR (R := ℚ) x).comp (qd_sig n).toRingHom
      = (aeval (R := ℚ) (fun v : Fin n × Fin n => x.val v.2 v.1)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro v
      simp [qd_sig, evGLR, IsLocalization.Away.lift_eq]
  exact congrArg (fun φ => φ P) h

/- English proof (translation)
Establish `h : Units.map (evGL x).toMonoidHom (detU n) = Matrix.GeneralLinearGroup.det x`. Use `ext`. Simplify using `only [Units.coe_map, detU, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply]`. Rewrite using `[evGL, IsLocalization.Away.lift_eq, RingHom.map_det, genMat_map_eval]`. Rewrite using `[← h, ← map_zpow]`.

Both sides reduce to the same expression.
-/
lemma qd_evGL_detU {R : Type} [CommRing R] (x : GL (Fin n) R) (m : ℤ) :
    evGL x ((detU n ^ m : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) = ((Matrix.GeneralLinearGroup.det x ^ m : Rˣ) : R) := by
  have h : Units.map (evGL x).toMonoidHom (detU n) = Matrix.GeneralLinearGroup.det x := by
    ext
    simp only [Units.coe_map, detU, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Matrix.GeneralLinearGroup.val_det_apply]
    rw [evGL, IsLocalization.Away.lift_eq, RingHom.map_det, genMat_map_eval]
  rw [← h, ← map_zpow]
  rfl

variable [NeZero n]

def qd_P (mu : Fin n → ℤ) (I : TIdx mu) : MvPolynomial (Fin n × Fin n) ℚ :=
  ∏ c : ↥(TCols mu), initMinor ℚ (fun p => (I c).1.orderEmbOfFin (I c).2 p) (colH_le mu c)

def qd_U (mu : Fin n → ℤ) : GLCoord ℚ n := mapCoord ℚ ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n)

/- English proof (translation)
Use `Finset.orderEmbOfFin_unique (s := (canT mu c).1) (canT mu c).2 (f := Fin.castLE (colH_le mu c)) (by intro x; simp [canT]) (Fin.strictMono_castLE _)` as an intermediate fact. Rewrite using `[← this]`.
-/
lemma qd_can_emb (mu : Fin n → ℤ) (c : ↥(TCols mu)) (a : Fin (colH mu c)) :
    (canT mu c).1.orderEmbOfFin (canT mu c).2 a = Fin.castLE (colH_le mu c) a := by
  have := Finset.orderEmbOfFin_unique (s := (canT mu c).1) (canT mu c).2 (f := Fin.castLE (colH_le mu c))
    (by intro x; simp [canT]) (Fin.strictMono_castLE _)
  rw [← this]

/- English proof (translation)
Unfold `brk TMat qd_U qd_P`. Rewrite using `[map_mul, map_prod, map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Unfold `minorC initMinor`.

Rewrite using `[mapCoord, IsLocalization.Away.lift_eq, RingHom.comp_apply, RingHom.map_det, AlgHom.map_det, RingHom.map_det, ← Matrix.det_transpose]`. Use `congr 1`. Use extensionality with `a b`. Simplify using `[genMat, qd_can_emb, qd_sig_X]`.
-/
lemma qd_brk (mu : Fin n → ℤ) (I : TIdx mu) :
    mapCoord ℚ (brk mu I) = qd_U mu * qd_sig n (qd_P mu I) := by
  unfold brk TMat qd_U qd_P
  rw [map_mul, map_prod, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold minorC initMinor
  rw [mapCoord, IsLocalization.Away.lift_eq, RingHom.comp_apply, RingHom.map_det, AlgHom.map_det,
    RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext a b
  simp [genMat, qd_can_emb, qd_sig_X]

def qd_nu (mu : Fin n → ℤ) : Fin n → ℕ := ∑ c : ↥(TCols mu), initW n (colH mu c)

/- English proof (translation)
Introduce `s t hst`. Unfold `qd_nu`. Rewrite using `[Finset.sum_apply, Finset.sum_apply]`. Use `Finset.sum_le_sum fun c _ => ?_` and prove the remaining obligations. Establish `: s.val ≤ t.val` using `hst`.

Unfold `initW`. Apply the tactic sequence `split_ifs <;> omega`.
-/
lemma qd_nu_anti (mu : Fin n → ℤ) : Antitone (qd_nu mu) := by
  intro s t hst
  unfold qd_nu
  rw [Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_le_sum fun c _ => ?_
  have : s.val ≤ t.val := hst
  unfold initW
  split_ifs <;> omega

/- English proof (translation)
The claim follows from `dualWeyl_prod univ _ _ (fun _ _ => initMinor_mem _ _)`.
-/
lemma tableauBideterminant_mem_dualWeyl' (mu : Fin n → ℤ) (I : TIdx mu) : qd_P mu I ∈ dualWeyl ℚ n n (qd_nu mu) :=
  dualWeyl_prod univ _ _ (fun _ _ => initMinor_mem _ _)

def qd_L (mu : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℚ →ₗ[ℚ] GLCoord ℚ n :=
  (LinearMap.mulLeft ℚ (qd_U mu)) ∘ₗ (qd_sig n).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma qd_L_apply (mu : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) ℚ) :
    qd_L mu P = qd_U mu * qd_sig n P := rfl

/- English proof (translation)
The claim follows from `(qd_brk mu I).symm`.
-/
lemma qd_L_P (mu : Fin n → ℤ) (I : TIdx mu) : qd_L mu (qd_P mu I) = mapCoord ℚ (brk mu I) :=
  (qd_brk mu I).symm

/- English proof (translation)
Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨I, rfl⟩`. Conclude with `⟨qd_P mu I, tableauBideterminant_mem_dualWeyl' mu I, qd_L_P mu I⟩`.
-/
lemma qd_span_le (mu : Fin n → ℤ) :
    Submodule.span ℚ (Set.range fun I : TIdx mu => mapCoord ℚ (brk mu I)) ≤
      (dualWeyl ℚ n n (qd_nu mu)).map (qd_L mu) := by
  rw [Submodule.span_le]
  rintro _ ⟨I, rfl⟩
  exact ⟨qd_P mu I, tableauBideterminant_mem_dualWeyl' mu I, qd_L_P mu I⟩

omit [NeZero n] in
/- English proof (translation)
Establish `: (Matrix.of fun a b : Fin n => Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))) = (Polynomial.C.comp (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n))).mapMatrix (genMat ℚ n)`. Use extensionality with `a b : 2`. Simplify using `[genMat]`. Rewrite using `[this, ← RingHom.map_det]`. Conclude with `(IsLocalization.Away.algebraMap_isUnit (S := GLCoord ℚ n) (genMat ℚ n).det).map Polynomial.C`.
-/
lemma generic_point_det_isUnit (n : ℕ) : IsUnit (Matrix.of fun a b : Fin n =>
    Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))).det := by
  have : (Matrix.of fun a b : Fin n =>
      Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (a, b)))) =
      (Polynomial.C.comp (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n))).mapMatrix (genMat ℚ n) := by
    ext a b : 2; simp [genMat]
  rw [this, ← RingHom.map_det]
  exact (IsLocalization.Away.algebraMap_isUnit (S := GLCoord ℚ n) (genMat ℚ n).det).map Polynomial.C

def qd_genPt (n : ℕ) : GL (Fin n) (Polynomial (GLCoord ℚ n)) :=
  Matrix.GeneralLinearGroup.mk'' _ (generic_point_det_isUnit n)

omit [NeZero n] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma qd_genPt_val (i j : Fin n) : (qd_genPt n).val i j =
    Polynomial.C (algebraMap (MvPolynomial (Fin n × Fin n) ℚ) (GLCoord ℚ n) (X (i, j))) := rfl

def qd_trans {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) : GL (Fin n) R :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.transvection a b t)
    (by rw [Matrix.det_transvection_of_ne _ _ hab]; exact isUnit_one)

omit [NeZero n] in
/- English proof (translation)
Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `Matrix.det_transvection_of_ne _ _ hab t`.
-/
lemma qd_trans_det {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) :
    Matrix.GeneralLinearGroup.det (qd_trans a b hab t) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transvection_of_ne _ _ hab t

omit [NeZero n] in
/- English proof (translation)
Establish `: (x * qd_trans a b hab t).val = x.val * Matrix.transvection a b t` using `rfl`. Rewrite using `[this]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Matrix.mul_transvection_apply_same]`.

Rewrite using `[Matrix.mul_transvection_apply_of_ne _ _ _ _ h, add_zero]`.
-/
lemma qd_mul_trans {R : Type} [CommRing R] (x : GL (Fin n) R) (a b : Fin n) (hab : a ≠ b) (t : R) (i j : Fin n) :
    (x * qd_trans a b hab t).val i j = x.val i j + if j = b then t * x.val i a else 0 := by
  have : (x * qd_trans a b hab t).val = x.val * Matrix.transvection a b t := rfl
  rw [this]
  split_ifs with h
  · subst h; rw [Matrix.mul_transvection_apply_same]
  · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ h, add_zero]

omit [NeZero n] in
/- English proof (translation)
Establish `: (qd_trans a b hab t).val = Matrix.transvection a b t` using `rfl`. Rewrite using `[this, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply]`. Rewrite using `[if_neg (by rintro ⟨rfl, h⟩; exact hab h.symm), add_zero]`.
-/
lemma qd_trans_diag {R : Type} [CommRing R] (a b : Fin n) (hab : a ≠ b) (t : R) (i : Fin n) :
    (qd_trans a b hab t).val i i = 1 := by
  have : (qd_trans a b hab t).val = Matrix.transvection a b t := rfl
  rw [this, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply]
  rw [if_neg (by rintro ⟨rfl, h⟩; exact hab h.symm), add_zero]

omit [NeZero n] in
/- English proof (translation)
Establish `: (qd_trans a b hab.ne t).val = Matrix.transvection a b t` using `rfl`. Rewrite using `[this, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hji.ne', Matrix.single_apply]`. Rewrite using `[if_neg (by rintro ⟨rfl, rfl⟩; exact absurd hab (not_lt.mpr hji.le)), add_zero]`.
-/
lemma qd_trans_low {R : Type} [CommRing R] (a b : Fin n) (hab : a < b) (t : R) (i j : Fin n) (hji : j < i) :
    (qd_trans a b hab.ne t).val i j = 0 := by
  have : (qd_trans a b hab.ne t).val = Matrix.transvection a b t := rfl
  rw [this, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hji.ne', Matrix.single_apply]
  rw [if_neg (by rintro ⟨rfl, rfl⟩; exact absurd hab (not_lt.mpr hji.le)), add_zero]

omit [NeZero n] in
/- English proof (translation)
Establish `h : (aeval (R` using `ℚ) (fun v : Fin n × Fin n => (qd_genPt n).val v.2 v.1)) = (Polynomial.CAlgHom (R := ℚ) (A := GLCoord ℚ n)).comp (qd_sig n) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `[qd_sig_X, qd_genPt_val]`. Conclude with `congrArg (fun φ => φ P) h`.
-/
lemma aeval_generic_point (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (qd_genPt n).val v.2 v.1) P = Polynomial.C (qd_sig n P) := by
  have h : (aeval (R := ℚ) (fun v : Fin n × Fin n => (qd_genPt n).val v.2 v.1))
      = (Polynomial.CAlgHom (R := ℚ) (A := GLCoord ℚ n)).comp (qd_sig n) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [qd_sig_X, qd_genPt_val]
  exact congrArg (fun φ => φ P) h

omit [NeZero n] in
/- English proof (translation)
Establish `h : (aeval (R` using `ℚ) (fun v : Fin n × Fin n => (qd_genPt n * qd_trans a b hab Polynomial.X).val v.2 v.1)) = (Polynomial.mapAlgHom (qd_sig n)).comp (rowGen ℚ a b) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [aeval_X, AlgHom.comp_apply, rowGen_X, qd_mul_trans, Polynomial.coe_mapAlgHom]`. Apply the tactic sequence `split_ifs <;> simp [qd_sig_X, qd_genPt_val]`.

Conclude with `congrArg (fun φ => φ P) h`.
-/
lemma qd_aeval_xu (a b : Fin n) (hab : a ≠ b) (P : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (fun v : Fin n × Fin n => (qd_genPt n * qd_trans a b hab Polynomial.X).val v.2 v.1) P
      = Polynomial.map (qd_sig n).toRingHom (rowGen ℚ a b P) := by
  have h : (aeval (R := ℚ)
      (fun v : Fin n × Fin n => (qd_genPt n * qd_trans a b hab Polynomial.X).val v.2 v.1))
      = (Polynomial.mapAlgHom (qd_sig n)).comp (rowGen ℚ a b) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [aeval_X, AlgHom.comp_apply, rowGen_X, qd_mul_trans, Polynomial.coe_mapAlgHom]
    split_ifs <;> simp [qd_sig_X, qd_genPt_val]
  exact congrArg (fun φ => φ P) h

/- English proof (translation)
Unfold `qd_U`. Rewrite using `[qd_evGLR_mapCoord, qd_evGL_detU]`. Conclude with `Units.isUnit _`.
-/
lemma qd_U_unit {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (mu : Fin n → ℤ) :
    IsUnit (evGLR (R := ℚ) x (qd_U mu)) := by
  unfold qd_U
  rw [qd_evGLR_mapCoord, qd_evGL_detU]
  exact Units.isUnit _

/- English proof (translation)
Unfold `qd_U`. Rewrite using `[qd_evGLR_mapCoord, qd_evGLR_mapCoord, qd_evGL_detU, qd_evGL_detU, map_mul, hu, mul_one]`.
-/
lemma qd_U_inv {R' : Type} [CommRing R'] [Algebra ℚ R'] (x u : GL (Fin n) R') (mu : Fin n → ℤ)
    (hu : Matrix.GeneralLinearGroup.det u = 1) :
    evGLR (R := ℚ) (x * u) (qd_U mu) = evGLR (R := ℚ) x (qd_U mu) := by
  unfold qd_U
  rw [qd_evGLR_mapCoord, qd_evGLR_mapCoord, qd_evGL_detU, qd_evGL_detU, map_mul, hu, mul_one]

/- English proof (translation)
Rewrite `h` using `[qd_L_apply, map_mul, map_mul, qd_U_inv _ _ _ (qd_trans_det a b hab _)]`. Establish `h2` using `(qd_U_unit (qd_genPt n) mu).mul_left_cancel h`. Rewrite `h2` using `[qd_ev_sig, qd_ev_sig, aeval_generic_point, qd_aeval_xu]`. Apply `Polynomial.map_injective (qd_sig n).toRingHom (qd_sig_inj n)` to reduce the goal to its premises. Rewrite using `[h2, Polynomial.map_C]`.

Both sides reduce to the same expression.
-/
lemma qd_raise (mu : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) ℚ) (a b : Fin n) (hab : a ≠ b)
    (h : evGLR (R := ℚ) (qd_genPt n * qd_trans a b hab Polynomial.X) (qd_L mu P)
      = evGLR (R := ℚ) (qd_genPt n) (qd_L mu P)) :
    rowGen ℚ a b P = Polynomial.C P := by
  rw [qd_L_apply, map_mul, map_mul, qd_U_inv _ _ _ (qd_trans_det a b hab _)] at h
  have h2 := (qd_U_unit (qd_genPt n) mu).mul_left_cancel h
  rw [qd_ev_sig, qd_ev_sig, aeval_generic_point, qd_aeval_xu] at h2
  apply Polynomial.map_injective (qd_sig n).toRingHom (qd_sig_inj n)
  rw [h2, Polynomial.map_C]
  rfl

/- English proof (translation)
Unfold `qd_P`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Unfold `initMinor lpMinor`. Simplify using `only [qd_can_emb]`.
-/
lemma tableauBideterminant_canonical_eq_prod_leadingMinor (mu : Fin n → ℤ) :
    qd_P mu (canT mu) = ∏ c : ↥(TCols mu), lpMinor ℚ (colH mu c) (colH_le mu c) (colH_le mu c) := by
  unfold qd_P
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold initMinor lpMinor
  simp only [qd_can_emb]

/- English proof (translation)
Take `⟨c0, h0⟩` from `hwLine ℚ n n le_rfl (qd_nu mu) (qd_nu_anti mu) _ (tableauBideterminant_mem_dualWeyl' mu (canT mu)) (by`. Introduce `a b hab k hk`. Unfold `rowDiv`. Rewrite using `[tableauBideterminant_canonical_eq_prod_leadingMinor, map_prod]`. Simplify using `only [rowGen_lpMinor ℚ a b hab]`.

Rewrite using `[← map_prod, Polynomial.coeff_C, if_neg (by omega)])`. Use `⟨c0, ?_, h0⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `h0` using `[zero_smul, tableauBideterminant_canonical_eq_prod_leadingMinor]`. Use `congrArg (eval (idPoint ℚ n n)) h0` as an intermediate fact.

Simplify using `[eval_idPoint_lpMinor] at this`.
-/
lemma tableauBideterminant_canonical_eq_smul_highestWeight (mu : Fin n → ℤ) : ∃ c0 : ℚ, c0 ≠ 0 ∧ qd_P mu (canT mu) = c0 • hw ℚ le_rfl (qd_nu mu) := by
  obtain ⟨c0, h0⟩ := hwLine ℚ n n le_rfl (qd_nu mu) (qd_nu_anti mu) _ (tableauBideterminant_mem_dualWeyl' mu (canT mu)) (by
    intro a b hab k hk
    unfold rowDiv
    rw [tableauBideterminant_canonical_eq_prod_leadingMinor, map_prod]
    simp only [rowGen_lpMinor ℚ a b hab]
    rw [← map_prod, Polynomial.coeff_C, if_neg (by omega)])
  refine ⟨c0, ?_, h0⟩
  rintro rfl
  rw [zero_smul, tableauBideterminant_canonical_eq_prod_leadingMinor] at h0
  have := congrArg (eval (idPoint ℚ n n)) h0
  simp [eval_idPoint_lpMinor] at this

/- English proof (translation)
Take `⟨P, hP, rfl⟩` from `qd_span_le mu hf`. Take `⟨c, hc⟩` from `hwLine ℚ n n le_rfl (qd_nu mu) (qd_nu_anti mu) P hP (by`. Introduce `a b hab k hk`. Unfold `rowDiv`. Rewrite using `[qd_raise mu P a b hab.ne (hinv _ _ _ (qd_trans_diag a b hab.ne _) (qd_trans_low a b hab _)), Polynomial.coeff_C, if_neg (by omega)])`.

Take `⟨c0, hc0, h0⟩` from `tableauBideterminant_canonical_eq_smul_highestWeight mu`. Use `⟨c / c0, ?_⟩` and prove the remaining obligations. Rewrite using `[← qd_L_P, ← map_smul, h0, hc, smul_smul, div_mul_cancel₀ _ hc0]`.
-/
theorem eq_smul_canonical_of_unipotent_invariant (mu : Fin n → ℤ) (f : GLCoord ℚ n)
    (hf : f ∈ Submodule.span ℚ (Set.range fun I : TIdx mu => mapCoord ℚ (brk mu I)))
    (hinv : ∀ (R' : Type) [CommRing R'] [Algebra ℚ R'] (x u : GL (Fin n) R'), (∀ a, u.val a a = 1) →
      (∀ a b, b < a → u.val a b = 0) → evGLR (R := ℚ) (x * u) f = evGLR (R := ℚ) x f) :
    ∃ c : ℚ, f = c • mapCoord ℚ (brk mu (canT mu)) := by
  obtain ⟨P, hP, rfl⟩ := qd_span_le mu hf
  obtain ⟨c, hc⟩ := hwLine ℚ n n le_rfl (qd_nu mu) (qd_nu_anti mu) P hP (by
    intro a b hab k hk
    unfold rowDiv
    rw [qd_raise mu P a b hab.ne (hinv _ _ _ (qd_trans_diag a b hab.ne _) (qd_trans_low a b hab _)),
      Polynomial.coeff_C, if_neg (by omega)])
  obtain ⟨c0, hc0, h0⟩ := tableauBideterminant_canonical_eq_smul_highestWeight mu
  refine ⟨c / c0, ?_⟩
  rw [← qd_L_P, ← map_smul, h0, hc, smul_smul, div_mul_cancel₀ _ hc0]

end Formalism.InvariantFactorPaths.ColumnFamilies
