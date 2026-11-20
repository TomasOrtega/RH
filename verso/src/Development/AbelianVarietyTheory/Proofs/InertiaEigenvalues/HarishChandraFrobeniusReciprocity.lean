import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.GLm.ParBasic
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.FrobRecHC

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

/- English proof (translation)
Take `⟨P, hP⟩` from `(par_basic g a b (a + b) rfl).1`. Conclude with `(hP _).1 (P.inv_mem ((hP x).2 h))`.
-/
theorem inPar_inv (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    InPar a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
  obtain ⟨P, hP⟩ := (par_basic g a b (a + b) rfl).1
  exact (hP _).1 (P.inv_mem ((hP x).2 h))

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by simpa using inPar_inv x⁻¹ h, inPar_inv x⟩`.
-/
theorem inPar_inv_iff (x : Gn g (a + b)) :
    InPar a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) ↔ InPar a (x : Mt g (a + b)) :=
  ⟨fun h => by simpa using inPar_inv x⁻¹ h, inPar_inv x⟩

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[tl_apply]`. Simplify using `[Matrix.one_apply]`.
-/
theorem tl_one : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [tl_apply]
  simp [Matrix.one_apply]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[br_apply]`. Simplify using `[Matrix.one_apply]`.
-/
theorem br_one : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [br_apply]
  simp [Matrix.one_apply]

/- English proof (translation)
Establish `hi` using `inPar_inv x h`. Establish `hm` using `blocks_mul (x : Mt g (a + b)) ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) h hi`. Rewrite `hm` using `[← Units.val_mul, mul_inv_cancel, Units.val_one, tl_one, br_one]`. Establish `u1` using `isUnit_blocks x h`. Establish `u2` using `isUnit_blocks _ hi`.

Prove the components needed by the constructor for the conclusion. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, toG_val u1.1, toG_val u2.1, ← hm.2.1, Units.val_one]`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, toG_val u1.2, toG_val u2.2, ← hm.2.2, Units.val_one]`.
-/
theorem toG_inv (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    (toG (tl a (x : Mt g (a + b))))⁻¹ = toG (tl a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b))) ∧
    (toG (br a b (x : Mt g (a + b))))⁻¹ = toG (br a b ((x⁻¹ : Gn g (a + b)) : Mt g (a + b))) := by
  have hi := inPar_inv x h
  have hm := blocks_mul (x : Mt g (a + b)) ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) h hi
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, tl_one, br_one] at hm
  have u1 := isUnit_blocks x h
  have u2 := isUnit_blocks _ hi
  constructor
  · apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, toG_val u1.1, toG_val u2.1, ← hm.2.1, Units.val_one]
  · apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, toG_val u1.2, toG_val u2.2, ← hm.2.2, Units.val_one]

def fz (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (z : Gn g (a + b)) : ℂ :=
  χ z * (if InPar a ((z⁻¹ : Gn g (a + b)) : Mt g (a + b)) then
    Φ (toG (tl a ((z⁻¹ : Gn g (a + b)) : Mt g (a + b)))) (toG (br a b ((z⁻¹ : Gn g (a + b)) : Mt g (a + b))))
    else 0)

/- English proof (translation)
Establish `key : ∀ y : Gn g (a + b), (∑ x : Gn g (a + b), χ x * (if InPar a ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)) then Φ (toG (tl a ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)))) (toG (br a b ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)))) else 0)) = ∑ z, fz χ Φ z`. Introduce `y`. Use `symm`. Use `Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ fun z => ?_` and prove the remaining obligations. Establish `e : y⁻¹ * ((MulAut.conj y).toEquiv z)⁻¹ * y = z⁻¹`.

Simplify using `[MulAut.conj_apply, mul_assoc]`. Rewrite using `[e, fz]`. Use `congr 1`. Simplify using `only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]`. Conclude with `(hχ z y).symm`.

Unfold `ip hcT`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Establish `hN : (Fintype.card (Gn g (a + b)) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[← key y, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN, one_mul, Finset.mul_sum]`.
-/
theorem lhs_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (hχ : IsClass χ) :
    ip χ (hcT a b Φ (a + b)) =
      ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
        ∑ z, fz χ Φ z := by
  have key : ∀ y : Gn g (a + b), (∑ x : Gn g (a + b), χ x *
      (if InPar a ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)) then
        Φ (toG (tl a ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b))))
          (toG (br a b ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)))) else 0)) = ∑ z, fz χ Φ z := by
    intro y
    symm
    refine Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ fun z => ?_
    have e : y⁻¹ * ((MulAut.conj y).toEquiv z)⁻¹ * y = z⁻¹ := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [e, fz]
    congr 1
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    exact (hχ z y).symm
  unfold ip hcT
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hN : (Fintype.card (Gn g (a + b)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  calc _ = (Fintype.card (Gn g (a + b)) : ℂ)⁻¹ * ∑ y : Gn g (a + b),
        ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
          ∑ z, fz χ Φ z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← key y, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN, one_mul, Finset.mul_sum]

/- English proof (translation)
Rewrite using `[fz, inPar_inv_iff]`. Use `split_ifs with h`. Rewrite using `[(toG_inv x h).1, (toG_inv x h).2]`. Rewrite using `[mul_zero]`.
-/
theorem fz_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (x : Gn g (a + b)) :
    fz χ Φ x = if InPar a (x : Mt g (a + b)) then
      χ x * Φ (toG (tl a (x : Mt g (a + b))))⁻¹ (toG (br a b (x : Mt g (a + b))))⁻¹ else 0 := by
  rw [fz, inPar_inv_iff]
  split_ifs with h
  · rw [(toG_inv x h).1, (toG_inv x h).2]
  · rw [mul_zero]

/- English proof (translation)
Rewrite using `[fz_eq]`. Distinguish the cases in `h : InPar a (x : Mt g (a + b))`. Establish `hu` using `isUnit_blocks x h`. Rewrite using `[if_pos h]`. Establish `hc : ∀ p : Gn g a × Gn g b, (InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (p.1 : Mt g a) ∧ br a b (x : Mt g (a + b)) = (p.2 : Mt g b)) ↔ (toG (tl a (x : Mt g (a + b))), toG (br a b (x : Mt g (a + b)))) = p`.

Introduce `p`. Rewrite using `[Prod.ext_iff, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]`. Simplify using `[h]`. Repeatedly rewrite using `[hc]`. Rewrite using `[Finset.sum_ite_eq]`.

Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem fibre_sum (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (x : Gn g (a + b)) :
    (∑ p : Gn g a × Gn g b, if InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (p.1 : Mt g a) ∧
        br a b (x : Mt g (a + b)) = (p.2 : Mt g b) then χ x * Φ p.1⁻¹ p.2⁻¹ else 0) = fz χ Φ x := by
  rw [fz_eq]
  by_cases h : InPar a (x : Mt g (a + b))
  · have hu := isUnit_blocks x h
    rw [if_pos h]
    have hc : ∀ p : Gn g a × Gn g b, (InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (p.1 : Mt g a) ∧
        br a b (x : Mt g (a + b)) = (p.2 : Mt g b)) ↔ (toG (tl a (x : Mt g (a + b))), toG (br a b (x : Mt g (a + b)))) = p := by
      intro p
      rw [Prod.ext_iff, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]
      simp [h]
    simp_rw [hc]
    rw [Finset.sum_ite_eq]
    simp
  · simp [h]

/- English proof (translation)
Unfold `ip res`. Simplify using `only [Prod.fst_inv, Prod.snd_inv, Fintype.card_prod]`. Repeatedly rewrite using `[← fibre_sum]`. Simplify using `only [Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> push_cast <;> ring`.
-/
theorem rhs_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) :
    ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) =
      ((Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) : ℕ) : ℂ)⁻¹ * ∑ z, fz χ Φ z := by
  unfold ip res
  simp only [Prod.fst_inv, Prod.snd_inv, Fintype.card_prod]
  simp_rw [← fibre_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> push_cast <;> ring

/- English proof (translation)
Introduce `g _ a b n hn χ Φ hχ`. Substitute `hn` using the available equality. Rewrite using `[lhs_eq χ Φ hχ, rhs_eq, card_par]`.
-/
theorem hcT_adjoint : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ),
    IsClass χ → ip χ (hcT a b Φ n) = ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) := by
  intro g _ a b n hn χ Φ hχ
  subst hn
  rw [lhs_eq χ Φ hχ, rhs_eq, card_par]

end GlobalTheory.GLq.FrobRecHC
