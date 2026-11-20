import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsRelationsDivPowBaseChangStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

def polyOfMv (k : Type) [CommRing k] (σ : Type) :
    MvPolynomial σ (Polynomial k) →+* Polynomial (MvPolynomial σ k) :=
  MvPolynomial.eval₂Hom (Polynomial.mapRingHom (C : k →+* MvPolynomial σ k)) (fun v => Polynomial.C (X v))

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C r => simp [polyOfMv]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp => simp only [map_mul, hp, map_X]`. Simplify using `[polyOfMv]`.
-/
theorem polyOfMv_map_C (k : Type) [CommRing k] (σ : Type) (f : MvPolynomial σ k) :
    polyOfMv k σ (map (algebraMap k (Polynomial k)) f) = Polynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [polyOfMv]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, map_X]; simp [polyOfMv]

/- English proof (translation)
Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨f, hf, rfl⟩` from `hy`. Introduce `j`. Rewrite using `[polyOfMv_map_C, Polynomial.coeff_C]`.

Use `split_ifs`. Conclude with `hf`. Conclude with `zero_mem _`. Consider the case `zero => intro j`. Simplify using the standard rewrite rules.

Consider the case `add y z _ _ hy hz => intro j`. Rewrite using `[map_add, Polynomial.coeff_add]`. Conclude with `add_mem (hy j) (hz j)`. Consider the case `smul c y _ hy`. Introduce `j`.

Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, Polynomial.coeff_mul]`. Use `Submodule.sum_mem _ fun x _ => ?_` and prove the remaining obligations. Establish `: polyOfMv k σ (C c) = Polynomial.map (C : k →+* MvPolynomial σ k) c` using `by simp [polyOfMv]`. Rewrite using `[this, Polynomial.coeff_map, ← MvPolynomial.smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ (hy x.2)`.
-/
theorem coeff_polyOfMv_mem (k : Type) [CommRing k] (σ : Type) (M : Submodule k (MvPolynomial σ k))
    (P : MvPolynomial σ (Polynomial k))
    (hP : P ∈ Submodule.span (Polynomial k) (map (algebraMap k (Polynomial k)) '' (M : Set (MvPolynomial σ k)))) :
    ∀ j, (polyOfMv k σ P).coeff j ∈ M := by
  induction hP using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    intro j
    rw [polyOfMv_map_C, Polynomial.coeff_C]
    split_ifs
    · exact hf
    · exact zero_mem _
  | zero => intro j; simp
  | add y z _ _ hy hz => intro j; rw [map_add, Polynomial.coeff_add]; exact add_mem (hy j) (hz j)
  | smul c y _ hy =>
    intro j
    rw [MvPolynomial.smul_eq_C_mul, map_mul, Polynomial.coeff_mul]
    refine Submodule.sum_mem _ fun x _ => ?_
    have : polyOfMv k σ (C c) = Polynomial.map (C : k →+* MvPolynomial σ k) c := by simp [polyOfMv]
    rw [this, Polynomial.coeff_map, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hy x.2)

end GlobalTheory.Alc

noncomputable section
namespace GlobalTheory.Alc

def transvGL (k : Type) [CommRing k] {N : ℕ} (a b : Fin N) (h : a ≠ b) : GL (Fin N) (Polynomial k) :=
  Matrix.nonsingInvUnit (Matrix.transvection a b (Polynomial.X : Polynomial k))
    (by rw [Matrix.det_transvection_of_ne a b h]; exact isUnit_one)

/- English proof (translation)
Establish `hdet : detPow (Polynomial k) N (transvGL k a b h) lam.detShift = 1`. Establish `h1 : Matrix.GeneralLinearGroup.det (transvGL k a b h) = 1`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `Matrix.det_transvection_of_ne a b h (Polynomial.X : Polynomial k)`.

Rewrite using `[detPow, h1, one_zpow, Units.val_one]`. Rewrite using `[sqAct, hdet, one_smul]`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C r => simp [polyOfMv, rowGen, rowAct]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.

Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, map_X]`. Use `congr 1`. Simplify using `only [rowGen, rowAct, aeval_X, map_sum, map_mul]`. Establish `hg : ∀ x, (transvGL k a b h : Matrix (Fin N) (Fin N) (Polynomial k)).transpose v.1 x = (if v.1 = x then 1 else 0) + (if a = x ∧ b = v.1 then Polynomial.X else 0)`.

Introduce `x`. Use `show (Matrix.transvection a b (Polynomial.X : Polynomial k)).transpose v.1 x = _`. Simplify using `only [Matrix.transpose_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`. Use `congr 1`. Simplify using `only [eq_comm]`.

Simplify using `only [hg, polyOfMv, eval₂Hom_C, eval₂Hom_X', Polynomial.coe_mapRingHom, Polynomial.map_add, add_mul, Finset.sum_add_distrib, apply_ite (Polynomial.map (C : k →+* MvPolynomial (Fin N × Fin N) k)), ite_mul, Polynomial.map_one, Polynomial.map_zero, Polynomial.map_X, one_mul, zero_mu …`. Take `⟨v1, v2⟩` from `v`. Distinguish the cases in `hb : v1 = b`. Substitute `hb` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hb, Ne.symm hb]`.
-/
theorem polyOfMv_sqAct_transv (k : Type) [CommRing k] (N : ℕ) (lam : DomWeight N) (a b : Fin N) (h : a ≠ b)
    (f : MvPolynomial (Fin N × Fin N) k) :
    polyOfMv k _ (sqAct (Polynomial k) N lam (transvGL k a b h) (map (algebraMap k (Polynomial k)) f)) =
      rowGen k a b f := by
  have hdet : detPow (Polynomial k) N (transvGL k a b h) lam.detShift = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det (transvGL k a b h) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact Matrix.det_transvection_of_ne a b h (Polynomial.X : Polynomial k)
    rw [detPow, h1, one_zpow, Units.val_one]
  rw [sqAct, hdet, one_smul]
  induction f using MvPolynomial.induction_on with
  | C r => simp [polyOfMv, rowGen, rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [rowGen, rowAct, aeval_X, map_sum, map_mul]
    have hg : ∀ x, (transvGL k a b h : Matrix (Fin N) (Fin N) (Polynomial k)).transpose v.1 x =
        (if v.1 = x then 1 else 0) + (if a = x ∧ b = v.1 then Polynomial.X else 0) := by
      intro x
      show (Matrix.transvection a b (Polynomial.X : Polynomial k)).transpose v.1 x = _
      simp only [Matrix.transpose_apply, Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      congr 1
      simp only [eq_comm]
    simp only [hg, polyOfMv, eval₂Hom_C, eval₂Hom_X', Polynomial.coe_mapRingHom, Polynomial.map_add, add_mul,
      Finset.sum_add_distrib, apply_ite (Polynomial.map (C : k →+* MvPolynomial (Fin N × Fin N) k)), ite_mul,
      Polynomial.map_one, Polynomial.map_zero, Polynomial.map_X, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ite_and, Finset.sum_ite_eq']
    obtain ⟨v1, v2⟩ := v
    by_cases hb : v1 = b
    · subst hb; simp
    · simp [hb, Ne.symm hb]

end GlobalTheory.Alc

noncomputable section
namespace GlobalTheory.Alc

/- English proof (translation)
Introduce `k _ N lam M hM a b hab f hf`. Establish `h1` using `coeff_polyOfMv_mem k _ M _ (hM (Polynomial k) (transvGL k a b hab) f hf) 1`. Rewrite `h1` using `[polyOfMv_sqAct_transv]`. Rewrite using `[((GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).2.1 a b f)]`. Conclude with `h1`.
-/
theorem rowE_mem_of_isGLSubmodule : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N)
    (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M →
    ∀ a b : Fin N, a ≠ b → ∀ f ∈ M, rowE k N N a b f ∈ M := by
  intro k _ N lam M hM a b hab f hf
  have h1 := coeff_polyOfMv_mem k _ M _ (hM (Polynomial k) (transvGL k a b hab) f hf) 1
  rw [polyOfMv_sqAct_transv] at h1
  rw [((GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange k N N).2.1 a b f)]
  exact h1

end GlobalTheory.Alc
