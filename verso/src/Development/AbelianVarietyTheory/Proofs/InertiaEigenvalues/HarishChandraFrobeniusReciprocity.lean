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
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem inPar_inv (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    InPar a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
  obtain ⟨P, hP⟩ := (par_basic g a b (a + b) rfl).1
  exact (hP _).1 (P.inv_mem ((hP x).2 h))

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem inPar_inv_iff (x : Gn g (a + b)) :
    InPar a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) ↔ InPar a (x : Mt g (a + b)) :=
  ⟨fun h => by simpa using inPar_inv x⁻¹ h, inPar_inv x⟩

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem tl_one : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [tl_apply]
  simp [Matrix.one_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem br_one : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [br_apply]
  simp [Matrix.one_apply]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fz_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (x : Gn g (a + b)) :
    fz χ Φ x = if InPar a (x : Mt g (a + b)) then
      χ x * Φ (toG (tl a (x : Mt g (a + b))))⁻¹ (toG (br a b (x : Mt g (a + b))))⁻¹ else 0 := by
  rw [fz, inPar_inv_iff]
  split_ifs with h
  · rw [(toG_inv x h).1, (toG_inv x h).2]
  · rw [mul_zero]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
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
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
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
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Rewrite the conclusion using the stated equalities.
-/
theorem hcT_adjoint : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ),
    IsClass χ → ip χ (hcT a b Φ n) = ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) := by
  intro g _ a b n hn χ Φ hχ
  subst hn
  rw [lhs_eq χ Φ hχ, rhs_eq, card_par]

end GlobalTheory.GLq.FrobRecHC
