import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.GLm.ParBasic
open scoped Classical

namespace GlobalTheory.GLq.HcClass

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Introduce `x w`. Unfold `hcT`. Use `congr 1`. Use `Fintype.sum_equiv (Equiv.mulLeft w⁻¹) _ _ fun y => ?_` and prove the remaining obligations. Rewrite using `[Equiv.coe_mulLeft, show (w⁻¹ * y)⁻¹ * x * (w⁻¹ * y) = y⁻¹ * (w * x * w⁻¹) * y by group]`.
-/
theorem hcT_isClass (a b n : ℕ) (Φ : Gn g a → Gn g b → ℂ) : IsClass (hcT a b Φ n) := by
  intro x w
  unfold hcT
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft w⁻¹) _ _ fun y => ?_
  rw [Equiv.coe_mulLeft, show (w⁻¹ * y)⁻¹ * x * (w⁻¹ * y) = y⁻¹ * (w * x * w⁻¹) * y by group]

variable {a b : ℕ}

/- English proof (translation)
Rewrite using `[← blkM_eq hM, blkM_mul, blkM_mul, tl_blkM, br_blkM, tl_blkM, br_blkM]`. Conclude with `⟨inPar_blkM _ _ _, rfl, rfl⟩`.
-/
theorem conj_blk (P P' : Mt g a) (Q Q' : Mt g b) (M : Mt g (a + b)) (hM : InPar a M) :
    InPar a (blkM P 0 Q * M * blkM P' 0 Q') ∧ tl a (blkM P 0 Q * M * blkM P' 0 Q') = P * tl a M * P' ∧
      br a b (blkM P 0 Q * M * blkM P' 0 Q') = Q * br a b M * Q' := by
  rw [← blkM_eq hM, blkM_mul, blkM_mul, tl_blkM, br_blkM, tl_blkM, br_blkM]
  exact ⟨inPar_blkM _ _ _, rfl, rfl⟩

/- English proof (translation)
Rewrite using `[blkM, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]`.
-/
theorem blkM_one : blkM (1 : Mt g a) 0 (1 : Mt g b) = 1 := by
  rw [blkM, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

def dg (u : Gn g a) (v : Gn g b) : Gn g (a + b) :=
  ⟨blkM u.val 0 v.val, blkM (u⁻¹).val 0 (v⁻¹).val, by simp [blkM_mul, blkM_one], by simp [blkM_mul, blkM_one]⟩

/- English proof (translation)
Use extensionality with `: 1`. Simplify using `[dg, blkM_mul]`.
-/
theorem dg_mul (u u' : Gn g a) (v v' : Gn g b) : dg u v * dg u' v' = dg (u * u') (v * v') := by
  ext : 1
  simp [dg, blkM_mul]

/- English proof (translation)
Use extensionality with `: 1`. Simplify using `[dg, blkM_one]`.
-/
theorem dg_one : dg (1 : Gn g a) (1 : Gn g b) = 1 := by
  ext : 1
  simp [dg, blkM_one]

/- English proof (translation)
Use `symm`. Rewrite using `[eq_inv_iff_mul_eq_one, dg_mul, inv_mul_cancel, inv_mul_cancel, dg_one]`.
-/
theorem dg_inv (u : Gn g a) (v : Gn g b) : (dg u v)⁻¹ = dg u⁻¹ v⁻¹ := by
  symm
  rw [eq_inv_iff_mul_eq_one, dg_mul, inv_mul_cancel, inv_mul_cancel, dg_one]

def Cnd (h₁ : Gn g a) (h₂ : Gn g b) (x : Gn g (a + b)) : Prop :=
  InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (h₁ : Mt g a) ∧ br a b (x : Mt g (a + b)) = (h₂ : Mt g b)

/- English proof (translation)
Take `⟨hp, ht, hb⟩` from `hx`. Rewrite using `[dg_inv]`. Establish `e : ((dg u v * x * dg u⁻¹ v⁻¹ : Gn g (a + b)) : Mt g (a + b)) = blkM u.val 0 v.val * x.val * blkM (u⁻¹).val 0 (v⁻¹).val` using `rfl`. Use `conj_blk u.val (u⁻¹).val v.val (v⁻¹).val x.val hp` as an intermediate fact. Use `⟨e ▸ this.1, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, this.2.1, ht]`. Simplify using the standard rewrite rules. Rewrite using `[e, this.2.2, hb]`. Simplify using the standard rewrite rules.
-/
theorem cnd_conj (u : Gn g a) (v : Gn g b) (h₁ : Gn g a) (h₂ : Gn g b) (x : Gn g (a + b)) (hx : Cnd h₁ h₂ x) :
    Cnd (u * h₁ * u⁻¹) (v * h₂ * v⁻¹) (dg u v * x * (dg u v)⁻¹) := by
  obtain ⟨hp, ht, hb⟩ := hx
  rw [dg_inv]
  have e : ((dg u v * x * dg u⁻¹ v⁻¹ : Gn g (a + b)) : Mt g (a + b)) =
      blkM u.val 0 v.val * x.val * blkM (u⁻¹).val 0 (v⁻¹).val := rfl
  have := conj_blk u.val (u⁻¹).val v.val (v⁻¹).val x.val hp
  refine ⟨e ▸ this.1, ?_, ?_⟩
  · rw [e, this.2.1, ht]; simp
  · rw [e, this.2.2, hb]; simp

/- English proof (translation)
Use `⟨fun h => ?_, cnd_conj u v h₁ h₂ x⟩` and prove the remaining obligations. Use `cnd_conj u⁻¹ v⁻¹ _ _ _ h` as an intermediate fact. Simplify using `only [dg_inv] at this`. Establish `key : dg u⁻¹ v⁻¹ * (dg u v * x * dg u⁻¹ v⁻¹) * dg u⁻¹⁻¹ v⁻¹⁻¹ = x`. Rewrite using `[inv_inv, inv_inv, ← dg_inv]`.

Use `group`. Rewrite `this` using `[key, show u⁻¹ * (u * h₁ * u⁻¹) * u⁻¹⁻¹ = h₁ by group, show v⁻¹ * (v * h₂ * v⁻¹) * v⁻¹⁻¹ = h₂ by group]`. Then use the resulting hypothesis.
-/
theorem cnd_iff (u : Gn g a) (v : Gn g b) (h₁ : Gn g a) (h₂ : Gn g b) (x : Gn g (a + b)) :
    Cnd (u * h₁ * u⁻¹) (v * h₂ * v⁻¹) (dg u v * x * (dg u v)⁻¹) ↔ Cnd h₁ h₂ x := by
  refine ⟨fun h => ?_, cnd_conj u v h₁ h₂ x⟩
  have := cnd_conj u⁻¹ v⁻¹ _ _ _ h
  simp only [dg_inv] at this
  have key : dg u⁻¹ v⁻¹ * (dg u v * x * dg u⁻¹ v⁻¹) * dg u⁻¹⁻¹ v⁻¹⁻¹ = x := by
    rw [inv_inv, inv_inv, ← dg_inv]; group
  rwa [key, show u⁻¹ * (u * h₁ * u⁻¹) * u⁻¹⁻¹ = h₁ by group,
    show v⁻¹ * (v * h₂ * v⁻¹) * v⁻¹⁻¹ = h₂ by group] at this

/- English proof (translation)
Unfold `res`. Use `congr 1`. Use `(Fintype.sum_equiv (MulAut.conj (dg u v)).toEquiv _ _ fun x => ?_).symm` and prove the remaining obligations. Establish `hc` using `cnd_iff u v h₁ h₂ x`. Unfold `Cnd at hc`.

Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hc, hχ x (dg u v)]`.
-/
theorem res_conj (χ : Gn g (a + b) → ℂ) (hχ : IsClass χ) (u : Gn g a) (v : Gn g b) (h₁ : Gn g a) (h₂ : Gn g b) :
    res a b χ (u * h₁ * u⁻¹) (v * h₂ * v⁻¹) = res a b χ h₁ h₂ := by
  unfold res
  congr 1
  refine (Fintype.sum_equiv (MulAut.conj (dg u v)).toEquiv _ _ fun x => ?_).symm
  have hc := cnd_iff u v h₁ h₂ x
  unfold Cnd at hc
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hc, hχ x (dg u v)]

/- English proof (translation)
Introduce `g _ a b n hn`. Substitute `hn` using the available equality. Use `⟨fun Φ => hcT_isClass _ _ _ Φ, fun χ hχ => ⟨fun h x y => ?_, fun h x y => ?_⟩⟩` and prove the remaining obligations. Simplify using `using res_conj χ hχ 1 y h x`. Simplify using `using res_conj χ hχ y 1 x h`.
-/
theorem hc_class : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∀ Φ : Gn g a → Gn g b → ℂ, IsClass (hcT a b Φ n)) ∧ ∀ χ : Gn g n → ℂ, IsClass χ → (∀ h, IsClass (res a b χ h)) ∧ ∀ h, IsClass (fun x => res a b χ x h) := by
  intro g _ a b n hn
  subst hn
  refine ⟨fun Φ => hcT_isClass _ _ _ Φ, fun χ hχ => ⟨fun h x y => ?_, fun h x y => ?_⟩⟩
  · simpa using res_conj χ hχ 1 y h x
  · simpa using res_conj χ hχ y 1 x h

end GlobalTheory.GLq.HcClass
