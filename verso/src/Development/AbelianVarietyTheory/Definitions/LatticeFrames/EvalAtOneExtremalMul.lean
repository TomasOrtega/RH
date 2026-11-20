import Mathlib
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.KernelLattices.ThDistC

noncomputable section

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker

namespace GlobalTheory.KJInf

variable {ι : Type} [Fintype ι] {a b : ℕ}

abbrev PY (ι : Type) (a : ℕ) : Type := MvPolynomial (ι × Fin a × Fin a) ℂ

abbrev FP (ι : Type) (a b : ℕ) : Type := MvPolynomial (ι × Fin b × Fin a) ℂ

def Vn (lam : ι → DomWeight a) (n : ι → ℕ) : Submodule ℂ (PY ι a) :=
  (CSpan lam).map (LinearMap.mulRight ℂ (∏ τ, (frDet ℂ a τ : PY ι a) ^ n τ))

def evalAt (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) : ℂ := eval (fun x => y x.1 x.2.1 x.2.2) F

def lft (g : ι → Matrix (Fin a) (Fin a) ℂ) : PY ι a →ₐ[ℂ] PY ι a :=
  aeval fun v => ∑ j, C (g v.1 v.2.1 j) * X (v.1, j, v.2.2)

def mvZ (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) : FP ι a b →ₐ[ℂ] FP ι a b :=
  aeval fun v => ∑ i, ∑ j, C (h v.1 i v.2.1 * g v.1 v.2.2 j) * X (v.1, i, j)

def subY (hab : a ≤ b) (y' : ι → Matrix (Fin b) (Fin b) ℂ) : PY ι a →ₐ[ℂ] FP ι a b :=
  aeval fun v => ∑ β, C (y' v.1 β (Fin.castLE hab v.2.2)) * X (v.1, β, v.2.1)

def jetL (c : ι → ℂ) (G : VCx ι a b → ℂ) : FP ι a b →ₗ[ℂ] ℂ :=
  (basisMonomials (ι × Fin b × Fin a) ℂ).constr ℂ fun m => jetC c G m

def IsInv (y : ι → Matrix (Fin a) (Fin a) ℂ) : Prop := ∀ τ, IsUnit (y τ).det

def IsUni (k : ι → Matrix (Fin a) (Fin a) ℂ) : Prop := ∀ τ, k τ ∈ Matrix.unitaryGroup (Fin a) ℂ

structure OntoUni {K : Type} [Group K] [TopologicalSpace K] (r : K → ι → Matrix (Fin a) (Fin a) ℂ) : Prop where
  cont : Continuous r
  mul : ∀ k k' τ, r (k * k') τ = r k τ * r k' τ
  uni : ∀ k, IsUni (r k)
  onto : ∀ u, IsUni u → ∃ k, r k = u

def HoweSpan (ι : Type) [Fintype ι] : Prop :=
  ∀ (a b : ℕ) (hab : a ≤ b), 0 < a → ∀ (lam : ι → DomWeight a) (n : ι → ℕ) (Q : PY ι a →ₗ[ℂ] FP ι a b),
    (∀ k, IsUni k → ∀ F ∈ Vn lam n, Q (lft k F) = mvZ k (fun _ => 1) (Q F)) →
    ∃ (m : ℕ) (y' : Fin m → ι → Matrix (Fin b) (Fin b) ℂ) (s : Fin m → ℂ), (∀ j, IsInv (y' j)) ∧
      ∀ F ∈ Vn lam n, Q F = ∑ j, s j • subY hab (y' j) F

/- English proof (translation)
Introduce `_` and use `one_mem _`.
-/
example : IsUni (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ)) := fun _ => one_mem _

/- English proof (translation)
Introduce `_` and use `by simp`.
-/
example : IsInv (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ)) := fun _ => by simp

omit [Fintype ι] in

/- English proof (translation)
Unfold `evalAt`. Proceed by induction on `F using MvPolynomial.induction_on`. Simplify using `[lft]`. Name the introduced variables `p q hp hq`. Rewrite using `[map_add, map_add, hp, hq, map_add]`.

Name the introduced variables `p v hp`. Rewrite using `[map_mul, map_mul, hp, map_mul]`. Use `congr 1`. Simplify using `[lft, Matrix.mul_apply]`.
-/
theorem evalAt_lft (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F := by
  unfold evalAt
  induction F using MvPolynomial.induction_on
  · simp [lft]
  · rename_i p q hp hq
    rw [map_add, map_add, hp, hq, map_add]
  · rename_i p v hp
    rw [map_mul, map_mul, hp, map_mul]
    congr 1
    simp [lft, Matrix.mul_apply]

/- English proof (translation)
Simplify using `only [mvZ, aeval_X, Matrix.one_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single p]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[Ne.symm hj]`. Simplify using the standard rewrite rules.
-/
private lemma mvZ_one_right_X_eq_sum {κ : Type} (h : κ → Matrix (Fin b) (Fin b) ℂ) (τ : κ) (β : Fin b) (p : Fin a) :
    mvZ (fun _ => 1) h (X (τ, β, p) : FP κ a b) = ∑ i, C (h τ i β) * X (τ, i, p) := by
  simp only [mvZ, aeval_X, Matrix.one_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single p]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

omit [Fintype ι] in

/- English proof (translation)
Establish `key : (mvZ (fun _ => 1) h).comp (subY hab y') = subY hab (fun τ => h τ * y' τ)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨τ, p, q⟩`. Rewrite using `[AlgHom.comp_apply]`. Simplify using `only [subY, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, mvZ_one_right_X_eq_sum, Matrix.mul_apply]`.

Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations. Conclude with `AlgHom.congr_fun key F`.
-/
theorem mvZ_subY (hab : a ≤ b) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a) :
    mvZ (fun _ => 1) h (subY hab y' F) = subY hab (fun τ => h τ * y' τ) F := by
  have key : (mvZ (fun _ => 1) h).comp (subY hab y') = subY hab (fun τ => h τ * y' τ) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, p, q⟩
    rw [AlgHom.comp_apply]
    simp only [subY, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq, mvZ_one_right_X_eq_sum, Matrix.mul_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  exact AlgHom.congr_fun key F

omit [Fintype ι] in

/- English proof (translation)
Establish `key : subY hab y' = (aeval (Sum.elim (fun x : ι × Fin b × Fin b => (C (y' x.1 x.2.1 x.2.2) : FP ι a b)) X)).comp (subD ℂ ι a b)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨τ, p, q⟩`. Establish `hq : (q : ℕ) < b` using `lt_of_lt_of_le q.2 hab`. Rewrite using `[AlgHom.comp_apply]`.

Simplify using `[subY, subD, dif_pos hq, Fin.castLE]`. Conclude with `AlgHom.congr_fun key F`.
-/
theorem subY_eq_subD (hab : a ≤ b) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a) :
    subY hab y' F = aeval (Sum.elim (fun x : ι × Fin b × Fin b => (C (y' x.1 x.2.1 x.2.2) : FP ι a b)) X)
      (subD ℂ ι a b F) := by
  have key : subY hab y' = (aeval (Sum.elim (fun x : ι × Fin b × Fin b => (C (y' x.1 x.2.1 x.2.2) : FP ι a b)) X)).comp
      (subD ℂ ι a b) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, p, q⟩
    have hq : (q : ℕ) < b := lt_of_lt_of_le q.2 hab
    rw [AlgHom.comp_apply]
    simp [subY, subD, dif_pos hq, Fin.castLE]
  exact AlgHom.congr_fun key F

/- English proof (translation)
Unfold `jetL`. Establish `h` using `(basisMonomials (ι × Fin b × Fin a) ℂ).constr_basis ℂ (fun m => jetC c G m) m`. Rewrite `h` using `[MvPolynomial.coe_basisMonomials]`. Then use the resulting hypothesis.
-/
theorem jetL_monomial (c : ι → ℂ) (G : VCx ι a b → ℂ) (m : ι × Fin b × Fin a →₀ ℕ) :
    jetL c G (monomial m 1) = jetC c G m := by
  unfold jetL
  have h := (basisMonomials (ι × Fin b × Fin a) ℂ).constr_basis ℂ (fun m => jetC c G m) m
  rwa [MvPolynomial.coe_basisMonomials] at h

end GlobalTheory.KJInf

end
