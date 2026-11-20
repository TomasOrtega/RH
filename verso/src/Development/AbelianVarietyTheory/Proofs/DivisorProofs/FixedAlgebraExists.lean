import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsConjOfMinpolyEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfNilpotentCommuteSeparableMinpoly
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FixedCentraliserReg

/- English proof (translation)
Introduce `p _ G β Y hsep hdeg`. Establish `hcomm : ∀ a b : G.C, Commute a (Y : G.C) → Commute b (Y : G.C) → Commute a b` using `fun a b ha hb => GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G (Y : G.C) hsep hdeg a b ha hb`. Establish `hshmul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x`. Introduce `x y`. Simplify using `only [sh, map_mul, MulOpposite.unop_mul]`.

Establish `hshadd : ∀ x y : G.C, sh G (x + y) = sh G x + sh G y`. Introduce `x y`. Simplify using `only [sh, map_add, MulOpposite.unop_add]`. Establish `hshalg : ∀ q : ℚ, sh G (algebraMap ℚ G.C q) = algebraMap ℚ G.C q`. Introduce `q`.

Establish `h` using `RingHom.congr_fun (RingHom.ext_rat (G.star.comp (algebraMap ℚ G.C)) (algebraMap ℚ G.Cᵐᵒᵖ)) q`. Simplify using `only [RingHom.comp_apply, MulOpposite.algebraMap_apply] at h`. Simplify using `only [sh, h, MulOpposite.unop_op]`. Establish `hββ : ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1` using `by simp`. Set `S : Subalgebra ℚ G.C` to `{ carrier := {c | Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c} mul_mem' := by`.

Introduce and unpack `a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩`. Use `⟨ha1.mul_left hb1, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hshmul]`. Simplify using `only [mul_assoc]`.

Rewrite using `[← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), hββ, one_mul]`. Use `_ = b * a := by rw [ha2, hb2]`. Use `_ = a * b := (hcomm a b ha1 hb1).eq.symm`. Use the proof step `add_mem' := by`. Introduce and unpack `a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩`.

Use `⟨ha1.add_left hb1, ?_⟩` and prove the remaining obligations. Rewrite using `[hshadd, mul_add, add_mul, ha2, hb2]`. Use the proof step `algebraMap_mem' := by`. Introduce `q`. Use `⟨Algebra.commutes q _, ?_⟩` and prove the remaining obligations.

Rewrite using `[hshalg, ← Algebra.commutes q (β : G.C), mul_assoc, Units.mul_inv, mul_one] }`. Use `letI cr : CommRing S := { (inferInstance : Ring S) with mul_comm := fun a b => Subtype.ext (hcomm a b a.2.1 b.2.1).eq }`. Establish `hred : IsReduced S`. Use `⟨fun x ⟨k, hk⟩ => Subtype.ext ?_⟩` and prove the remaining obligations. Establish `hk' : (x : G.C) ^ k = 0`.

Use `congrArg Subtype.val hk` as an intermediate fact. Simplify using `using this`. Conclude with `GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero p G (Y : G.C) hsep hdeg x x.2.1 k hk'`. Use `haveI := G.towerC`. Use `haveI := G.finC`.

Use `haveI : FiniteDimensional ℚ G.C := Module.Finite.trans G.F G.C`. Establish `hfd : FiniteDimensional ℚ S` using `Module.Finite.of_injective (S.val.toLinearMap) Subtype.val_injective`. Use `⟨S, cr, hred, S.algebra, hfd, S.val, Subtype.val_injective, fun c => ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Conclude with `x.2`. Introduce `h`. Conclude with `⟨⟨c, h⟩, rfl⟩`.
-/
theorem fixed_algebra_exists : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β Y : G.Cˣ),
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : CommRing L) (_ : IsReduced L) (_ : Algebra ℚ L) (_ : FiniteDimensional ℚ L) (ι : L →ₐ[ℚ] G.C), Function.Injective ι ∧
      ∀ c : G.C, c ∈ Set.range ι ↔ Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c := by
  intro p _ G β Y hsep hdeg
  have hcomm : ∀ a b : G.C, Commute a (Y : G.C) → Commute b (Y : G.C) → Commute a b :=
    fun a b ha hb => GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G (Y : G.C) hsep hdeg a b ha hb
  have hshmul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := by
    intro x y; simp only [sh, map_mul, MulOpposite.unop_mul]
  have hshadd : ∀ x y : G.C, sh G (x + y) = sh G x + sh G y := by
    intro x y; simp only [sh, map_add, MulOpposite.unop_add]
  have hshalg : ∀ q : ℚ, sh G (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := by
    intro q
    have h := RingHom.congr_fun (RingHom.ext_rat (G.star.comp (algebraMap ℚ G.C)) (algebraMap ℚ G.Cᵐᵒᵖ)) q
    simp only [RingHom.comp_apply, MulOpposite.algebraMap_apply] at h
    simp only [sh, h, MulOpposite.unop_op]
  have hββ : ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by simp
  let S : Subalgebra ℚ G.C :=
    { carrier := {c | Commute c (Y : G.C) ∧ (β : G.C) * sh G c * ((β⁻¹ : G.Cˣ) : G.C) = c}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨ha1.mul_left hb1, ?_⟩
        calc (β : G.C) * sh G (a * b) * ((β⁻¹ : G.Cˣ) : G.C)
            = ((β : G.C) * sh G b * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C)) := by
              rw [hshmul]
              simp only [mul_assoc]
              rw [← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), hββ, one_mul]
          _ = b * a := by rw [ha2, hb2]
          _ = a * b := (hcomm a b ha1 hb1).eq.symm
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨ha1.add_left hb1, ?_⟩
        rw [hshadd, mul_add, add_mul, ha2, hb2]
      algebraMap_mem' := by
        intro q
        refine ⟨Algebra.commutes q _, ?_⟩
        rw [hshalg, ← Algebra.commutes q (β : G.C), mul_assoc, Units.mul_inv, mul_one] }
  letI cr : CommRing S :=
    { (inferInstance : Ring S) with
      mul_comm := fun a b => Subtype.ext (hcomm a b a.2.1 b.2.1).eq }
  have hred : IsReduced S := by
    refine ⟨fun x ⟨k, hk⟩ => Subtype.ext ?_⟩
    have hk' : (x : G.C) ^ k = 0 := by
      have := congrArg Subtype.val hk
      simpa using this
    exact GlobalTheory.LKCx.ClsReg.eq_zero_of_commute_of_pow_eq_zero p G (Y : G.C) hsep hdeg x x.2.1 k hk'
  haveI := G.towerC
  haveI := G.finC
  haveI : FiniteDimensional ℚ G.C := Module.Finite.trans G.F G.C
  have hfd : FiniteDimensional ℚ S :=
    Module.Finite.of_injective (S.val.toLinearMap) Subtype.val_injective
  refine ⟨S, cr, hred, S.algebra, hfd, S.val, Subtype.val_injective, fun c => ?_⟩
  constructor
  · rintro ⟨x, rfl⟩; exact x.2
  · intro h; exact ⟨⟨c, h⟩, rfl⟩

end GlobalTheory.FixedCentraliserReg
