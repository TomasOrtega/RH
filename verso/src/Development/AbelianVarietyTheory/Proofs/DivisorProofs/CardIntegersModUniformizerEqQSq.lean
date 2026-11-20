import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

/- English proof (translation)
Establish `h` using `WithZero.lt_mul_exp_iff_le (x := x) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero`. Rewrite `h` using `[← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]`. Then use the resulting hypothesis.
-/
theorem lt_one_iff_le_exp_neg_one (x : WithZero (Multiplicative ℤ)) :
    x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  have h := WithZero.lt_mul_exp_iff_le (x := x) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero
  rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero] at h

/- English proof (translation)
Introduce `L _ _ ϖ σ q hU`. Take `⟨-, -, -, hϖ, -, -, hcard⟩` from `hU`. Use `set v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v with hv`. Use `set A := v.valuationSubring`. Use `set O := (intL L).toAddSubgroup`.

Set `e : O →+ A` to `{ toFun := fun x => ⟨x.1, x.2⟩ map_zero' := rfl map_add' := fun _ _ => rfl }`. Set `f : O →+ A ⧸ IsLocalRing.maximalIdeal A` to `(Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).toAddMonoidHom.comp e`. Establish `hf : Function.Surjective f`. Introduce `y`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Conclude with `⟨⟨a.1, a.2⟩, rfl⟩`. Establish `hϖ1 : v ϖ = WithZero.exp (-1 : ℤ)` using `hϖ`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h`. Rewrite `hϖ1` using `[h, map_zero]`.

Conclude with `WithZero.exp_ne_zero hϖ1.symm`. Establish `hker : (O.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf O = f.ker`. Use extensionality with `x`. Rewrite using `[AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]`. Express the relevant statement in the definitionally equal form `_ ↔ Ideal.Quotient.mk _ (e x) = 0`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_maximalIdeal_iff]`. Express the relevant statement in the definitionally equal form `_ ↔ v x.1 < 1`. Rewrite using `[AddSubgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hxy⟩`.

Establish `hy1 : v y ≤ 1` using `hy`. Rewrite using `[← hxy, AddMonoidHom.coe_mulLeft, map_mul, hϖ1]`. Combine the equalities or inequalities in the displayed calculation. Introduce `hx`. Use `⟨ϖ⁻¹ * x.1, ?_, ?_⟩` and prove the remaining obligations.

Use `show v (ϖ⁻¹ * x.1) ≤ 1`. Rewrite using `[map_mul, map_inv₀, hϖ1, ← WithZero.exp_neg, neg_neg]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[AddMonoidHom.coe_mulLeft] show ϖ * (ϖ⁻¹ * x.1) = x.1`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]`.

Rewrite using `[AddSubgroup.relIndex, hker, AddSubgroup.index_eq_card, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv]`. Conclude with `hcard`.
-/
theorem intIndex : GlobalTheory.SatakeWeyl.IntIndex := by
  intro L _ _ ϖ σ q hU
  obtain ⟨-, -, -, hϖ, -, -, hcard⟩ := hU
  set v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v with hv
  set A := v.valuationSubring
  set O := (intL L).toAddSubgroup
  let e : O →+ A :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : O →+ A ⧸ IsLocalRing.maximalIdeal A :=
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).toAddMonoidHom.comp e
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨⟨a.1, a.2⟩, rfl⟩
  have hϖ1 : v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ1
    exact WithZero.exp_ne_zero hϖ1.symm
  have hker : (O.map (AddMonoidHom.mulLeft ϖ)).addSubgroupOf O = f.ker := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker]
    change _ ↔ Ideal.Quotient.mk _ (e x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Valuation.mem_maximalIdeal_iff]
    change _ ↔ v x.1 < 1
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hy1 : v y ≤ 1 := hy
      rw [← hxy, AddMonoidHom.coe_mulLeft, map_mul, hϖ1]
      calc WithZero.exp (-1 : ℤ) * v y ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact (lt_one_iff_le_exp_neg_one _).2 le_rfl
    · intro hx
      refine ⟨ϖ⁻¹ * x.1, ?_, ?_⟩
      · show v (ϖ⁻¹ * x.1) ≤ 1
        rw [map_mul, map_inv₀, hϖ1, ← WithZero.exp_neg, neg_neg]
        calc WithZero.exp (1 : ℤ) * v x.1 ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) :=
              by gcongr; exact (lt_one_iff_le_exp_neg_one _).1 hx
          _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
      · rw [AddMonoidHom.coe_mulLeft]
        show ϖ * (ϖ⁻¹ * x.1) = x.1
        rw [← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  rw [AddSubgroup.relIndex, hker, AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  exact hcard

end GlobalTheory.SatakeWeyl
