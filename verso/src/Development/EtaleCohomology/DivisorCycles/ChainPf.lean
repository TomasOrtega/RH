import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix MvPolynomial
namespace LateralTheory.DivDb.ChainPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N M : ℕ}

noncomputable def lin (φ : Mat C N →ₗ[C] Mat C M) (q : Fin M × Fin M) : MP C N :=
  ∑ r : Fin N × Fin N, MvPolynomial.C (φ (Matrix.single r.1 r.2 1) q.1 q.2) * X r

/- English proof (translation)
Establish `hx : x = ∑ r : Fin N × Fin N, x r.1 r.2 • Matrix.single r.1 r.2 (1 : C)`. Rewrite using `[Fintype.sum_prod_type]`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single x]`. Simplify using `[Matrix.smul_single]`. Use `conv_rhs => rw [hx]`.

Simplify using `only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun r _ => mul_comm _ _`.
-/
theorem sum_lin (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (q : Fin M × Fin M) :
    ∑ r : Fin N × Fin N, φ (Matrix.single r.1 r.2 1) q.1 q.2 * x r.1 r.2 = φ x q.1 q.2 := by
  have hx : x = ∑ r : Fin N × Fin N, x r.1 r.2 • Matrix.single r.1 r.2 (1 : C) := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp [Matrix.smul_single]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

/- English proof (translation)
Rewrite using `[← sum_lin φ x q]`. Simplify using `[ev, lin]`.
-/
theorem ev_lin (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (q : Fin M × Fin M) :
    ev x (lin φ q) = φ x q.1 q.2 := by
  rw [← sum_lin φ x q]; simp [ev, lin]

/- English proof (translation)
Rewrite using `[← sum_lin φ Y q]`. Simplify using `only [dAt, lin, map_sum, Derivation.leibniz, pderiv_X, pderiv_C, smul_zero, add_zero, smul_eq_mul]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `[ev, Pi.single_apply, Finset.sum_ite_eq']`.
-/
theorem dAt_lin (φ : Mat C N →ₗ[C] Mat C M) (x Y : Mat C N) (q : Fin M × Fin M) :
    dAt (lin φ q) x Y = φ Y q.1 q.2 := by
  rw [← sum_lin φ Y q]
  simp only [dAt, lin, map_sum, Derivation.leibniz, pderiv_X, pderiv_C, smul_zero, add_zero, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [ev, Pi.single_apply, Finset.sum_ite_eq']

/- English proof (translation)
Use `show eval₂Hom (RingHom.id C) _ (bind₁ (lin φ) f) = eval₂Hom (RingHom.id C) _ f`. Rewrite using `[eval₂Hom_bind₁]`. Use `congr 2`. Use function extensionality and compare the values at `q`. Conclude with `ev_lin φ x q`.
-/
theorem ev_bind (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (f : MP C M) :
    ev x (bind₁ (lin φ) f) = ev (φ x) f := by
  show eval₂Hom (RingHom.id C) _ (bind₁ (lin φ) f) = eval₂Hom (RingHom.id C) _ f
  rw [eval₂Hom_bind₁]
  congr 2; funext q; exact ev_lin φ x q

/- English proof (translation)
Simplify using `[dAt, ev, add_mul, Finset.sum_add_distrib]`.
-/
theorem dAt_add (f g : MP C N) (x Y : Mat C N) : dAt (f + g) x Y = dAt f x Y + dAt g x Y := by
  simp [dAt, ev, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [dAt, Derivation.leibniz, smul_eq_mul, ev, map_add, map_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]`.
-/
theorem dAt_mul (f g : MP C N) (x Y : Mat C N) :
    dAt (f * g) x Y = ev x f * dAt g x Y + ev x g * dAt f x Y := by
  simp only [dAt, Derivation.leibniz, smul_eq_mul, ev, map_add, map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

/- English proof (translation)
Simplify using `[dAt, ev]`.
-/
theorem dAt_C (a : C) (x Y : Mat C N) : dAt (MvPolynomial.C a : MP C N) x Y = 0 := by
  simp [dAt, ev]

/- English proof (translation)
Introduce `C _ N M φ f`. Use `⟨bind₁ (lin φ) f, fun x => ?_, ?_⟩` and prove the remaining obligations. Conclude with `ev_bind φ x f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => intro x Y`.

Simplify using `[dAt_C]`. Consider the case `add f g hf hg => intro x Y`. Rewrite using `[map_add, dAt_add, dAt_add, hf, hg]`. Consider the case `mul_X f q hf`. Introduce `x Y`.

Rewrite using `[map_mul, bind₁_X_right, dAt_mul, dAt_mul, hf, dAt_lin, ev_lin]`. Rewrite using `[ev_bind]`. Simplify using `[dAt, ev, pderiv_X, Pi.single_apply]`.
-/
theorem chain_of : Chain := by
  intro C _ N M φ f
  refine ⟨bind₁ (lin φ) f, fun x => ?_, ?_⟩
  · exact ev_bind φ x f
  · induction f using MvPolynomial.induction_on with
    | C a => intro x Y; simp [dAt_C]
    | add f g hf hg => intro x Y; rw [map_add, dAt_add, dAt_add, hf, hg]
    | mul_X f q hf =>
      intro x Y
      rw [map_mul, bind₁_X_right, dAt_mul, dAt_mul, hf, dAt_lin, ev_lin]
      rw [ev_bind]
      simp [dAt, ev, pderiv_X, Pi.single_apply]

end LateralTheory.DivDb.ChainPf

/- English proof (translation)
The claim follows from `LateralTheory.DivDb.ChainPf.chain_of`.
-/
theorem LateralTheory.DivDb.Chain_of : LateralTheory.DivDb.Chain := LateralTheory.DivDb.ChainPf.chain_of
