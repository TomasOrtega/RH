import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas

noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching Formalism.GradedWeylDivisibility Formalism.REAL
open scoped TensorProduct DirectSum Matrix

namespace GlobalTheory.ConjDual

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [rowAct]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, map_X]`.

Use `congr 1`. Simplify using `[rowAct]`.
-/
theorem map_rowAct {r n : ℕ} (φ : ℂ →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    map φ (rowAct ℂ A f) = rowAct ℂ (A.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [rowAct]

def bil (σ : Type) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f f' => fockF f (map (starRingEnd ℂ) f'))
    (fun _ _ _ => fischerInner_add_left _ _ _)
    (fun c f f' => by rw [smul_eq_C_mul, LFocks_C_mul_left, smul_eq_mul])
    (fun f a b => by rw [map_add, fischerInner_add_right])
    (fun c f f' => by
      rw [smul_eq_C_mul, map_mul, map_C, LFocks_C_mul_right, smul_eq_mul]
      simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bil_apply {σ : Type} (f f' : MvPolynomial σ ℂ) : bil σ f f' = fockF f (map (starRingEnd ℂ) f') := rfl

/- English proof (translation)
Rewrite using `[bil_apply, bil_apply, fockRowAdj, map_rowAct]`. Both sides reduce to the same expression.
-/
theorem bil_rowAct {r n : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (f f' : MvPolynomial (Fin r × Fin n) ℂ) :
    bil _ (rowAct ℂ A f) f' = bil _ f (rowAct ℂ Aᵀ f') := by
  rw [bil_apply, bil_apply, fockRowAdj, map_rowAct]
  rfl

/- English proof (translation)
Rewrite using `[bil_apply, map_map]`. Establish `: (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ` using `by ext; simp`. Rewrite using `[this, map_id]`.
-/
theorem bil_conj {σ : Type} (f : MvPolynomial σ ℂ) : bil σ f (map (starRingEnd ℂ) f) = fockF f f := by
  rw [bil_apply, map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext; simp
  rw [this, map_id]

def toDual (n : ℕ) (lam : DomWeight n) : nablaSq ℂ n lam →ₗ[ℂ] Module.Dual ℂ (nablaSq ℂ n lam) :=
  (bil _).compl₁₂ (nablaSq ℂ n lam).subtype (nablaSq ℂ n lam).subtype

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `f hf`. Assume the negation of the conclusion as `h0`. Establish `h1 : f.1 ≠ 0` using `fun h => h0 (Subtype.ext h)`. Establish `h2` using `LinearMap.congr_fun hf ⟨map (starRingEnd ℂ) f.1, dualWeylMap ℂ ℂ _ n n _ _ f.2⟩`.

Establish `h3 : fockF f.1 f.1 = 0` using `(bil_conj f.1).symm.trans h2`. Establish `h` using `fockPos _ f.1 h1`. Rewrite `h` using `[h3]`. Simplify using `at h`.
-/
theorem toDual_injective (n : ℕ) (lam : DomWeight n) : Function.Injective (toDual n lam) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra h0
  have h1 : f.1 ≠ 0 := fun h => h0 (Subtype.ext h)
  have h2 := LinearMap.congr_fun hf ⟨map (starRingEnd ℂ) f.1, dualWeylMap ℂ ℂ _ n n _ _ f.2⟩
  have h3 : fockF f.1 f.1 = 0 := (bil_conj f.1).symm.trans h2
  have h := fockPos _ f.1 h1
  rw [h3] at h
  simp at h

/- English proof (translation)
Unfold `detPow`. Use `congr 2`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, unitaryIncl_coe, unitaryIncl_coe, conjU_coe, Matrix.det_transpose]`. Both sides reduce to the same expression.
-/
theorem detPow_conjU (n : ℕ) (g : U n) (c : ℤ) :
    detPow ℂ n (unitaryIncl n (conjU n g)) c = detPow ℂ n (unitaryIncl n g⁻¹) c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, unitaryIncl_coe,
    unitaryIncl_coe, conjU_coe, Matrix.det_transpose]
  rfl

/- English proof (translation)
Introduce `n lam`. Use `⟨(toDual n lam).linearEquivOfInjective (toDual_injective n lam) Subspace.dual_finrank_eq.symm, fun g x => ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Express the relevant statement in the definitionally equal form `bil _ (sqAct ℂ n lam (unitaryIncl n (conjU n g)) x.1) y.1 = bil _ x.1 (sqAct ℂ n lam (unitaryIncl n g⁻¹) y.1)`. Unfold `sqAct`.

Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, detPow_conjU, bil_rowAct, Matrix.transpose_transpose]`. Both sides reduce to the same expression.
-/
theorem iso_conj_dual : ∀ (n : ℕ) (lam : DomWeight n),
    Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam).dual := by
  intro n lam
  refine ⟨(toDual n lam).linearEquivOfInjective (toDual_injective n lam) Subspace.dual_finrank_eq.symm,
    fun g x => ?_⟩
  ext y
  change bil _ (sqAct ℂ n lam (unitaryIncl n (conjU n g)) x.1) y.1 =
    bil _ x.1 (sqAct ℂ n lam (unitaryIncl n g⁻¹) y.1)
  unfold sqAct
  rw [map_smul, map_smul, LinearMap.smul_apply, detPow_conjU, bil_rowAct, Matrix.transpose_transpose]
  rfl

end GlobalTheory.ConjDual
