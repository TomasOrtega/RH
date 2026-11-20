import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InvTransposeIso

def ctr {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) : GL n A →* GL m A where
  toFun g := ⟨((g⁻¹).1ᵀ).submatrix e.symm e.symm, (g.1ᵀ).submatrix e.symm e.symm,
    by rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
      Matrix.submatrix_one_equiv],
    by rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.submatrix_one_equiv]⟩
  map_one' := Units.ext (by ext i j; simp [Matrix.one_apply])
  map_mul' g h := Units.ext (by
    show (((g * h)⁻¹).1ᵀ).submatrix e.symm e.symm =
      ((g⁻¹).1ᵀ).submatrix e.symm e.symm * ((h⁻¹).1ᵀ).submatrix e.symm e.symm
    rw [Matrix.submatrix_mul_equiv, ← Matrix.transpose_mul, ← Units.val_mul, _root_.mul_inv_rev])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ctr_val {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : (ctr e g).1 = ((g⁻¹).1ᵀ).submatrix e.symm e.symm := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ctr_inv_val {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : ((ctr e g)⁻¹).1 = (g.1ᵀ).submatrix e.symm e.symm := rfl

/- English proof (translation)
The claim follows from `Units.ext (by rw [ctr_val, ctr_inv_val]; ext i j; simp)`.
-/
theorem ctr_ctr {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) (g : GL n A) : ctr e.symm (ctr e g) = g :=
  Units.ext (by rw [ctr_val, ctr_inv_val]; ext i j; simp)

/- English proof (translation)
Establish `hHiH : Hi * H = 1` using `mul_eq_one_comm.1 hHi`. Establish `h1 : g.1.map c * (g⁻¹).1.map c = 1`. Rewrite using `[← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hY : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H = 1`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.transpose_mul, Matrix.mul_assoc]`. Use `_ = 1 := by`. Rewrite using `[h1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc _ Hi H, hHiH, Matrix.mul_one, Units.inv_mul]`. Establish `hY' : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ = Hi`. Combine the equalities or inequalities in the displayed calculation.

Establish `hKt : Kᵀ = -Hi` using `by rw [hK, neg_neg]`. Apply `Matrix.transpose_injective` to reduce the goal to its premises. Rewrite using `[Matrix.transpose_map]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose]`. Rewrite using `[hKt, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hY']`.
-/
theorem key_rel {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (c : A →+* A)
    {H Hi K : Matrix n n A} (hHi : H * Hi = 1) (hK : Hi = -Kᵀ) (g : GL n A)
    (hg : (g.1.map c)ᵀ * H * g.1 = H) :
    (((g⁻¹).1ᵀ).map c)ᵀ * K * (g⁻¹).1ᵀ = K := by
  have hHiH : Hi * H = 1 := mul_eq_one_comm.1 hHi
  have h1 : g.1.map c * (g⁻¹).1.map c = 1 := by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hY : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H = 1 := by
    calc (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * H
        = (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * ((g.1.map c)ᵀ * H * g.1) := by rw [hg]
      _ = (g⁻¹).1 * Hi * (g.1.map c * (g⁻¹).1.map c)ᵀ * H * g.1 := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [h1, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc _ Hi H, hHiH, Matrix.mul_one,
            Units.inv_mul]
  have hY' : (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ = Hi := by
    calc _ = (g⁻¹).1 * Hi * ((g⁻¹).1.map c)ᵀ * (H * Hi) := by rw [hHi, Matrix.mul_one]
      _ = Hi := by rw [← Matrix.mul_assoc, hY, Matrix.one_mul]
  have hKt : Kᵀ = -Hi := by rw [hK, neg_neg]
  apply Matrix.transpose_injective
  rw [Matrix.transpose_map]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hKt, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc, hY']

/- English proof (translation)
Establish `hJ : J = (J.submatrix e e).submatrix e.symm e.symm` using `by ext i j; simp`. Establish `hM : ((M.submatrix e.symm e.symm).map c)ᵀ = ((M.map c)ᵀ).submatrix e.symm e.symm` using `rfl`. Rewrite using `[hM]`. Use `conv_lhs => rw [hJ]`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h, ← hJ]`.
-/
theorem reindex_rel {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : A →+* A) (e : n ≃ m) {J : Matrix m m A} {M : Matrix n n A}
    (h : (M.map c)ᵀ * J.submatrix e e * M = J.submatrix e e) :
    ((M.submatrix e.symm e.symm).map c)ᵀ * J * M.submatrix e.symm e.symm = J := by
  have hJ : J = (J.submatrix e e).submatrix e.symm e.symm := by ext i j; simp
  have hM : ((M.submatrix e.symm e.symm).map c)ᵀ = ((M.map c)ᵀ).submatrix e.symm e.symm := rfl
  rw [hM]
  conv_lhs => rw [hJ]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h, ← hJ]

/- English proof (translation)
The claim follows from `reindex_rel c e (key_rel c hHi hK g hg)`.
-/
theorem ctr_rel {A : Type} [CommRing A] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (c : A →+* A) (e : n ≃ m) {H Hi : Matrix n n A} {J : Matrix m m A} (hHi : H * Hi = 1)
    (hK : Hi = -(Jᵀ.submatrix e e)) (g : GL n A) (hg : Formalism.UG.cT c g.1 * H * g.1 = H) :
    Formalism.UG.cT c (ctr e g).1 * J * (ctr e g).1 = J :=
  reindex_rel c e (key_rel c hHi hK g hg)

/- English proof (translation)
Establish `h1 : A * -(Bᵀ.submatrix e e) = 1` using `by rw [← h]; exact Matrix.mul_nonsing_inv A hA`. Establish `h2 : -(B.submatrix e e) * Aᵀ = 1`. Use `congrArg Matrix.transpose h1` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_neg, Matrix.transpose_submatrix, Matrix.transpose_transpose, Matrix.transpose_one]`. Conclude with `this`.

Establish `h3 : Aᵀ * -(B.submatrix e e) = 1` using `mul_eq_one_comm.1 h2`. Establish `h4 : Aᵀ.submatrix e.symm e.symm * -B = 1`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Use `_ = (Aᵀ * -(B.submatrix e e)).submatrix e.symm e.symm := Matrix.submatrix_mul_equiv _ _ _ _ _`. Use `_ = 1 := by rw [h3, Matrix.submatrix_one_equiv]`. Conclude with `Matrix.inv_eq_left_inv (by rw [Matrix.neg_mul, ← Matrix.mul_neg]; exact h4)`.
-/
theorem inv_rel {K : Type} [Field K] {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A : Matrix n n K) (B : Matrix m m K) (e : n ≃ m) (h : A⁻¹ = -(Bᵀ.submatrix e e)) (hA : IsUnit A.det) :
    B⁻¹ = -(Aᵀ.submatrix e.symm e.symm) := by
  have h1 : A * -(Bᵀ.submatrix e e) = 1 := by rw [← h]; exact Matrix.mul_nonsing_inv A hA
  have h2 : -(B.submatrix e e) * Aᵀ = 1 := by
    have := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_neg, Matrix.transpose_submatrix, Matrix.transpose_transpose,
      Matrix.transpose_one] at this
    exact this
  have h3 : Aᵀ * -(B.submatrix e e) = 1 := mul_eq_one_comm.1 h2
  have h4 : Aᵀ.submatrix e.symm e.symm * -B = 1 := by
    calc Aᵀ.submatrix e.symm e.symm * -B
        = Aᵀ.submatrix e.symm e.symm * (-(B.submatrix e e)).submatrix e.symm e.symm := by
          congr 1; ext i j; simp
      _ = (Aᵀ * -(B.submatrix e e)).submatrix e.symm e.symm := Matrix.submatrix_mul_equiv _ _ _ _ _
      _ = 1 := by rw [h3, Matrix.submatrix_one_equiv]
  exact Matrix.inv_eq_left_inv (by rw [Matrix.neg_mul, ← Matrix.mul_neg]; exact h4)

end GlobalTheory.InvTransposeIso

namespace GlobalTheory.InvTransposeIso

variable {D : D7}

/- English proof (translation)
The claim follows from `inv_rel V.gram W.gram e h (Formalism.L2.Theta.gram_det_ne V).isUnit`.
-/
theorem gram_inv_rel {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    W.gram⁻¹ = -(V.gramᵀ.submatrix e.symm e.symm) :=
  inv_rel V.gram W.gram e h (Formalism.L2.Theta.gram_det_ne V).isUnit

/- English proof (translation)
Establish `hdet : IsUnit V.gram.det` using `(Formalism.L2.Theta.gram_det_ne V).isUnit`. Establish `hHi : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1`. Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hK : (V.gram⁻¹).map (incA D) = -(((W.gram.map (incA D))ᵀ).submatrix e e)`. Rewrite using `[h]`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Conclude with `ctr_rel (cA D) e hHi hK (matHom V g) g.2`.
-/
theorem mem_HR {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : ctr e (matHom V g) ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
  have hdet : IsUnit V.gram.det := (Formalism.L2.Theta.gram_det_ne V).isUnit
  have hHi : V.gram.map (incA D) * (V.gram⁻¹).map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hK : (V.gram⁻¹).map (incA D) = -(((W.gram.map (incA D))ᵀ).submatrix e e) := by
    rw [h]; ext i j; simp
  exact ctr_rel (cA D) e hHi hK (matHom V g) g.2

/- English proof (translation)
Establish `hdet : IsUnit V.gram.det` using `(Formalism.L2.Theta.gram_det_ne V).isUnit`. Conclude with `ctr_rel _ e (Matrix.mul_nonsing_inv _ hdet) h r hr`.
-/
theorem mem_UJ {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (r : GL (Fin V.rank) D.host.E) (hr : r ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram) :
    ctr e r ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram := by
  have hdet : IsUnit V.gram.det := (Formalism.L2.Theta.gram_det_ne V).isUnit
  exact ctr_rel _ e (Matrix.mul_nonsing_inv _ hdet) h r hr

def fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    GA D V →* GA D W where
  toFun g := (⟨ctr e (matHom V g), mem_HR e h g⟩ : HR (AF D.host.F) D.sp.cm.sig W.gram)
  map_one' := Subtype.ext (by simp only [map_one]; rfl)
  map_mul' g g' := Subtype.ext (by simp only [map_mul]; rfl)

/- English proof (translation)
Use `show (ctr e (matHom V g)).1 = _`. Rewrite using `[ctr_val, ← map_inv]`. Both sides reduce to the same expression.
-/
theorem mt_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : Formalism.L2.Theta.mt W (fwd e h g) = ((Formalism.L2.Theta.mt V g⁻¹)ᵀ).submatrix e.symm e.symm := by
  show (ctr e (matHom V g)).1 = _
  rw [ctr_val, ← map_inv]; rfl

end GlobalTheory.InvTransposeIso

namespace GlobalTheory.InvTransposeIso

variable {D : D7}

def iso {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    GA D V ≃* GA D W :=
  { fwd e h with
    invFun := fwd e.symm (gram_inv_rel e h)
    left_inv := fun g => Subtype.ext (ctr_ctr e g.1)
    right_inv := fun g => Subtype.ext (ctr_ctr e.symm g.1) }

/- English proof (translation)
Establish `hv : Continuous fun g : GA D V => (matHom V g).1` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hi : Continuous fun g : GA D V => ((matHom V g)⁻¹).1` using `Units.continuous_coe_inv.comp continuous_subtype_val`. Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Use `show Continuous fun g : GA D V => (((matHom V g)⁻¹).1ᵀ).submatrix e.symm e.symm`. Conclude with `hi.matrix_transpose.matrix_submatrix _ _`.

Use `show Continuous fun g : GA D V => ((matHom V g).1ᵀ).submatrix e.symm e.symm`. Conclude with `hv.matrix_transpose.matrix_submatrix _ _`.
-/
theorem continuous_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e)) :
    Continuous (fwd e h) := by
  have hv : Continuous fun g : GA D V => (matHom V g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hi : Continuous fun g : GA D V => ((matHom V g)⁻¹).1 :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun g : GA D V => (((matHom V g)⁻¹).1ᵀ).submatrix e.symm e.symm
    exact hi.matrix_transpose.matrix_submatrix _ _
  · show Continuous fun g : GA D V => ((matHom V g).1ᵀ).submatrix e.symm e.symm
    exact hv.matrix_transpose.matrix_submatrix _ _

/- English proof (translation)
Take `⟨r, hr, hrγ⟩` from `(Subgroup.mem_subgroupOf.1 hγ : γ.1 ∈ HFin (AF D.host.F) D.sp.cm.sig V.gram)`. Use `Subgroup.mem_subgroupOf.2 ⟨ctr e r, mem_UJ e h r hr, ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.bc (inclR (AF D.host.F)) (ctr e r) = ctr e γ.1`. Rewrite using `[← hrγ]`. Conclude with `Units.ext (by ext i j; rfl)`.
-/
theorem fwd_GQ {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (γ : GA D V) (hγ : γ ∈ GQ V) : fwd e h γ ∈ GQ W := by
  obtain ⟨r, hr, hrγ⟩ := (Subgroup.mem_subgroupOf.1 hγ : γ.1 ∈
    HFin (AF D.host.F) D.sp.cm.sig V.gram)
  refine Subgroup.mem_subgroupOf.2 ⟨ctr e r, mem_UJ e h r hr, ?_⟩
  show Formalism.UG.bc (inclR (AF D.host.F)) (ctr e r) = ctr e γ.1
  rw [← hrγ]
  exact Units.ext (by ext i j; rfl)

/- English proof (translation)
Establish `hYG : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1`. Simplify using `only [Formalism.L2.Theta.mt]`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `hsub : Formalism.L2.Theta.mt V g⁻¹ - 1 = -(Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g - 1))`. Rewrite using `[Matrix.mul_sub, hYG, Matrix.mul_one, neg_sub]`.

Introduce `i j`. Establish `hij : (Formalism.L2.Theta.mt W (fwd e h g) - 1) i j = (Formalism.L2.Theta.mt V g⁻¹ - 1) (e.symm j) (e.symm i)`. Rewrite using `[mt_fwd]`. Simplify using `only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.one_apply, e.symm.injective.eq_iff, eq_comm]`. Rewrite using `[hij, hsub, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, hg k (e.symm i)]`.
-/
theorem suppAt_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (a : AE D) (g : GA D V) (hg : SuppAt a V g) : SuppAt a W (fwd e h g) := by
  have hYG : Formalism.L2.Theta.mt V g⁻¹ * Formalism.L2.Theta.mt V g = 1 := by
    simp only [Formalism.L2.Theta.mt]
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hsub : Formalism.L2.Theta.mt V g⁻¹ - 1 = -(Formalism.L2.Theta.mt V g⁻¹ * (Formalism.L2.Theta.mt V g - 1)) := by
    rw [Matrix.mul_sub, hYG, Matrix.mul_one, neg_sub]
  intro i j
  have hij : (Formalism.L2.Theta.mt W (fwd e h g) - 1) i j = (Formalism.L2.Theta.mt V g⁻¹ - 1) (e.symm j) (e.symm i) := by
    rw [mt_fwd]
    simp only [Matrix.sub_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.one_apply,
      e.symm.injective.eq_iff, eq_comm]
  rw [hij, hsub, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, hg k (e.symm i)]

/- English proof (translation)
Rewrite using `[mt_fwd, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]`.
-/
theorem det_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : (Formalism.L2.Theta.mt W (fwd e h g)).det = (Formalism.L2.Theta.mt V g⁻¹).det := by
  rw [mt_fwd, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]

/- English proof (translation)
Rewrite using `[mt_fwd]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem sub_fwd {V W : HSp D} (e : Fin V.rank ≃ Fin W.rank) (h : V.gram⁻¹ = -(W.gramᵀ.submatrix e e))
    (g : GA D V) : (Formalism.L2.Theta.mt W (fwd e h g)).submatrix e e = (Formalism.L2.Theta.mt V g⁻¹)ᵀ := by
  rw [mt_fwd]; ext i j; simp

/- English proof (translation)
Introduce `D T S' e₂ h`. Conclude with `⟨iso e₂ h, continuous_fwd e₂ h, fun γ hγ => fwd_GQ e₂ h γ hγ, sub_fwd e₂ h, fun a g hg => suppAt_fwd e₂ h a g hg, det_fwd e₂ h⟩`.
-/
theorem grp_contra : ∀ (D : D7) (T S' : HSp D) (e₂ : Fin S'.rank ≃ Fin T.rank), S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) →
    ∃ φ : GA D S' ≃* GA D T, Continuous φ ∧ (∀ γ ∈ GQ S', φ γ ∈ GQ T) ∧
      (∀ g, (Formalism.L2.Theta.mt T (φ g)).submatrix e₂ e₂ = (Formalism.L2.Theta.mt S' g⁻¹)ᵀ) ∧
      (∀ e g, SuppAt e S' g → SuppAt e T (φ g)) ∧ ∀ g, (Formalism.L2.Theta.mt T (φ g)).det = (Formalism.L2.Theta.mt S' g⁻¹).det := by
  intro D T S' e₂ h
  exact ⟨iso e₂ h, continuous_fwd e₂ h, fun γ hγ => fwd_GQ e₂ h γ hγ, sub_fwd e₂ h,
    fun a g hg => suppAt_fwd e₂ h a g hg, det_fwd e₂ h⟩

end GlobalTheory.InvTransposeIso
