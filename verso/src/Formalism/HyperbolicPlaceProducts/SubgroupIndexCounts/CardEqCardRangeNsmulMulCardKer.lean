import Formalism.HyperbolicPlaceProducts.Statement

open Module

namespace Formalism.SLP.P

/- English proof (translation)
Introduce `A _ _ g`. Use `set f : A →+ A := nsmulAddMonoidHom g`. Rewrite using `[AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker, Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]`.
-/
theorem card_eq_card_range_nsmul_mul_card_ker : Formalism.SLP.TorsionIndexEq := by
  intro A _ _ g
  set f : A →+ A := nsmulAddMonoidHom g
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]

/- English proof (translation)
Introduce `A _ _ g K hK`. Establish `hle : K ≤ (nsmulAddMonoidHom g : A →+ A).ker` using `fun x hx => by`. Simplify using `using hK x hx`. Rewrite using `[card_eq_card_range_nsmul_mul_card_ker A g]`. Conclude with `Nat.mul_le_mul_left _ (AddSubgroup.card_le_of_le hle)`.
-/
theorem card_range_nsmul_mul_card_le : Formalism.SLP.TorsionIndex := by
  intro A _ _ g K hK
  have hle : K ≤ (nsmulAddMonoidHom g : A →+ A).ker := fun x hx => by
    simpa using hK x hx
  rw [card_eq_card_range_nsmul_mul_card_ker A g]
  exact Nat.mul_le_mul_left _ (AddSubgroup.card_le_of_le hle)

end Formalism.SLP.P
