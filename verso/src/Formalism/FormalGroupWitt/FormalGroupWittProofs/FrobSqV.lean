import Formalism.FormalGroupWitt.SubstInjectiveV

noncomputable section

namespace Formalism.FG

open Formalism.G

namespace PadicFrobeniusSquare

/- English proof (translation)
Establish `h1 : y ∈ RingHom.ker (PadicInt.toZMod (p` using `p)) := hy`. Rewrite `h1` using `[PadicInt.ker_toZMod]`. Establish `h2 : ‖y‖ < 1` using `PadicInt.mem_nonunits.1 ((IsLocalRing.mem_maximalIdeal _).1 h1)`. Take `⟨z, rfl⟩` from `(PadicInt.norm_lt_one_iff_dvd _).1 h2`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)`.
-/
theorem padicInt_norm_le_p {p : ℕ} [Fact p.Prime] (y : ℤ_[p]) (hy : PadicInt.toZMod y = 0) :
    ‖y‖ ≤ ‖(p : ℤ_[p])‖ := by
  have h1 : y ∈ RingHom.ker (PadicInt.toZMod (p := p)) := hy
  rw [PadicInt.ker_toZMod] at h1
  have h2 : ‖y‖ < 1 := PadicInt.mem_nonunits.1 ((IsLocalRing.mem_maximalIdeal _).1 h1)
  obtain ⟨z, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h2
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)

end PadicFrobeniusSquare

/- English proof (translation)
Introduce `l _`. Use `⟨Fact.out, ⟨2, two_pos, rfl⟩, Padic.norm_p_lt_one, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Establish `hz : ∀ z : ZMod l, z ^ l ^ 2 = z` using `fun z => by`. Rewrite using `[pow_two, pow_mul, ZMod.pow_card, ZMod.pow_card]`.

Set `y : ℤ_[l]` to `⟨a, ha⟩`. Establish `h` using `PadicFrobeniusSquare.padicInt_norm_le_p (y - y ^ l ^ 2) (by rw [map_sub, map_pow, hz, sub_self])`. Rewrite `h` using `[PadicInt.norm_def, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_natCast]`. Use `show ‖a - a ^ l ^ 2‖ ≤ ‖(l : ℚ_[l])‖`. Conclude with `h`.
-/
theorem frobenius_lift_padic_square : Formalism.FG.FrobLiftPadicSq := by
  intro l _
  refine ⟨Fact.out, ⟨2, two_pos, rfl⟩, Padic.norm_p_lt_one, ?_⟩
  intro a ha
  have hz : ∀ z : ZMod l, z ^ l ^ 2 = z := fun z => by
    rw [pow_two, pow_mul, ZMod.pow_card, ZMod.pow_card]
  let y : ℤ_[l] := ⟨a, ha⟩
  have h := PadicFrobeniusSquare.padicInt_norm_le_p (y - y ^ l ^ 2) (by rw [map_sub, map_pow, hz, sub_self])
  rw [PadicInt.norm_def, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_natCast] at h
  show ‖a - a ^ l ^ 2‖ ≤ ‖(l : ℚ_[l])‖
  exact h

end Formalism.FG
