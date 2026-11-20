import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockDiagonalWithIdentityGLEqOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.GGNorm

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Unfold `wh tr eU eDat`. Simplify using `only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.smul_apply, Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`.

Use `congr 2`. Rewrite using `[Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.
-/
theorem wh_formula (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (χ : Gn g n → ℂ) :
    wh ψ χ = ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ *
      ∑ u : Gn g n, (if IsUniUp (u : Mt g n) then
        (ψ (∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)))⁻¹ else 0) * χ u := by
  unfold wh tr eU eDat
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.smul_apply,
    Finsupp.finsetSum_apply, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc]
  congr 2
  rw [Finset.sum_ite_eq']
  simp

/- English proof (translation)
Distinguish the cases in `hu : IsUniUp (u : Mt g n)`. Establish `hi` using `GlobalTheory.BadCount.Inh.isUniUp_inv u hu`. Rewrite using `[if_pos hi, if_pos hu]`. Establish `h` using `GlobalTheory.BadCount.Inh.sd_mul hi hu`. Rewrite `h` using `[← Units.val_mul, inv_mul_cancel, Units.val_one, GlobalTheory.BadCount.Inh.sd_one]`.

Establish `e : (∑ i ∈ Finset.range (n - 1), entN ((u⁻¹ : Gn g n) : Mt g n) i (i + 1)) = -(∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1))` using `eq_neg_of_add_eq_zero_left h.symm`. Rewrite using `[e, AddChar.map_neg_eq_inv]`. Establish `hi : ¬ IsUniUp ((u⁻¹ : Gn g n) : Mt g n)` using `fun h => hu (by simpa using GlobalTheory.BadCount.Inh.isUniUp_inv u⁻¹ h)`. Rewrite using `[if_neg hi, if_neg hu]`.
-/
theorem gg_term_inv (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (u : Gn g n) :
    (if IsUniUp ((u⁻¹ : Gn g n) : Mt g n) then
        ψ (∑ i ∈ Finset.range (n - 1), entN ((u⁻¹ : Gn g n) : Mt g n) i (i + 1)) else 0) =
      if IsUniUp (u : Mt g n) then (ψ (∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)))⁻¹ else 0 := by
  by_cases hu : IsUniUp (u : Mt g n)
  · have hi := GlobalTheory.BadCount.Inh.isUniUp_inv u hu
    rw [if_pos hi, if_pos hu]
    have h := GlobalTheory.BadCount.Inh.sd_mul hi hu
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, GlobalTheory.BadCount.Inh.sd_one] at h
    have e : (∑ i ∈ Finset.range (n - 1), entN ((u⁻¹ : Gn g n) : Mt g n) i (i + 1)) =
        -(∑ i ∈ Finset.range (n - 1), entN (u : Mt g n) i (i + 1)) :=
      eq_neg_of_add_eq_zero_left h.symm
    rw [e, AddChar.map_neg_eq_inv]
  · have hi : ¬ IsUniUp ((u⁻¹ : Gn g n) : Mt g n) := fun h =>
      hu (by simpa using GlobalTheory.BadCount.Inh.isUniUp_inv u⁻¹ h)
    rw [if_neg hi, if_neg hu]

/- English proof (translation)
Use `set c : ℂ := ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ with hc`. Use `set F : Gn g n → ℂ := fun z => if IsUniUp (z : Mt g n) then ψ (∑ i ∈ Finset.range (n - 1), entN (z : Mt g n) i (i + 1)) else 0 with hF`. Establish `hgg : ∀ x, gg ψ n x = c * ∑ y : Gn g n, F (y⁻¹ * x * y)` using `fun x => rfl`. Establish `hinner : ∀ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) = ∑ u : Gn g n, χ u * F u⁻¹`. Introduce `y`.

Set `e : Gn g n ≃ Gn g n` to `⟨fun x => y⁻¹ * x * y, fun u => y * u * y⁻¹, fun x => by group, fun u => by group⟩`. Use `Fintype.sum_equiv e _ _ fun x => ?_` and prove the remaining obligations. Establish `h1 : χ (y⁻¹ * x * y) = χ x`. Use `hχ x y⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Then use the resulting hypothesis.

Establish `h2 : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹` using `by group`. Express the relevant statement in the definitionally equal form `χ x * F (y⁻¹ * x⁻¹ * y) = χ (y⁻¹ * x * y) * F (y⁻¹ * x * y)⁻¹`. Rewrite using `[h1, h2]`. Establish `hG : (Fintype.card (Gn g n) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Establish `e1 : ∑ x : Gn g n, χ x * gg ψ n x⁻¹ = c * ∑ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y)`.

Simplify using `only [hgg, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring` and prove the remaining obligations. Establish `e2 : wh ψ χ = c * ∑ u : Gn g n, χ u * F u⁻¹`. Rewrite using `[wh_formula]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Use `congr 1`. Conclude with `(gg_term_inv ψ u).symm`.

Unfold `ip`. Rewrite using `[e1, e2, Finset.sum_congr rfl fun y _ => hinner y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[mul_left_comm, ← mul_assoc, ← mul_assoc, mul_assoc c, inv_mul_cancel₀ hG, mul_one]`.
-/
theorem ip_gg (ψ : AddChar (ZMod g) ℂ) (n : ℕ) (χ : Gn g n → ℂ) (hχ : IsClass χ) :
    ip χ (gg ψ n) = wh ψ χ := by
  set c : ℂ := ((Finset.univ.filter fun u : Gn g n => IsUniUp (u : Mt g n)).card : ℂ)⁻¹ with hc
  set F : Gn g n → ℂ := fun z => if IsUniUp (z : Mt g n) then
    ψ (∑ i ∈ Finset.range (n - 1), entN (z : Mt g n) i (i + 1)) else 0 with hF
  have hgg : ∀ x, gg ψ n x = c * ∑ y : Gn g n, F (y⁻¹ * x * y) := fun x => rfl
  have hinner : ∀ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) = ∑ u : Gn g n, χ u * F u⁻¹ := by
    intro y
    let e : Gn g n ≃ Gn g n :=
      ⟨fun x => y⁻¹ * x * y, fun u => y * u * y⁻¹, fun x => by group, fun u => by group⟩
    refine Fintype.sum_equiv e _ _ fun x => ?_
    have h1 : χ (y⁻¹ * x * y) = χ x := by
      have := hχ x y⁻¹
      rwa [inv_inv] at this
    have h2 : y⁻¹ * x⁻¹ * y = (y⁻¹ * x * y)⁻¹ := by group
    change χ x * F (y⁻¹ * x⁻¹ * y) = χ (y⁻¹ * x * y) * F (y⁻¹ * x * y)⁻¹
    rw [h1, h2]
  have hG : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have e1 : ∑ x : Gn g n, χ x * gg ψ n x⁻¹ = c * ∑ y : Gn g n, ∑ x : Gn g n, χ x * F (y⁻¹ * x⁻¹ * y) := by
    simp only [hgg, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  have e2 : wh ψ χ = c * ∑ u : Gn g n, χ u * F u⁻¹ := by
    rw [wh_formula]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_comm]
    congr 1
    exact (gg_term_inv ψ u).symm
  unfold ip
  rw [e1, e2, Finset.sum_congr rfl fun y _ => hinner y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_left_comm, ← mul_assoc, ← mul_assoc, mul_assoc c, inv_mul_cancel₀ hG, mul_one]

/- English proof (translation)
Establish `h1` using `GlobalTheory.GLm.GGSum.sum_wh_gg g ψ hψ n`. Establish `h2` using `GlobalTheory.GLm.GGSum.sum_wh_gg g ψ hψ (n - 1)`. Rewrite `h2` using `[Nat.sub_add_cancel hn]`. Rewrite `h1` using `[Finset.sum_range_succ, h2]`. Take the linear combination `h1`.
-/
theorem wh_gg (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (n : ℕ) (hn : 0 < n) :
    wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) := by
  have h1 := GlobalTheory.GLm.GGSum.sum_wh_gg g ψ hψ n
  have h2 := GlobalTheory.GLm.GGSum.sum_wh_gg g ψ hψ (n - 1)
  rw [Nat.sub_add_cancel hn] at h2
  rw [Finset.sum_range_succ, h2] at h1
  linear_combination h1

/- English proof (translation)
Introduce `_ _ ψ hψ n hn` and use `⟨wh_gg ψ hψ n hn, fun χ hχ => ip_gg ψ n χ hχ⟩`.
-/
theorem gg_norm : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n →
    wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) ∧
      ∀ χ : Gn g n → ℂ, IsClass χ → ip χ (gg ψ n) = wh ψ χ :=
  fun _ _ ψ hψ n hn => ⟨wh_gg ψ hψ n hn, fun χ hχ => ip_gg ψ n χ hχ⟩

end GlobalTheory.GLq.GGNorm
