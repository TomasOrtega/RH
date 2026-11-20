import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Shapiro
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FinGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem UpperTheory.V.KH.permTrans :
    ∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] [Nonempty X] (s j : ℕ),
      StabLe G X s → CardLe (groupHomology (permRep G X) (j + 1)) (s ^ (s ^ (j + 1))) := by
  intro G X _ _ _ _ s j hs
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨hfin, hcard⟩ := hs x
  haveI := hfin
  obtain ⟨e⟩ := shapiro G X x (j + 1)
  have h1 := finGroup (MulAction.stabilizer G x) j
  have hpos : 0 < Nat.card (MulAction.stabilizer G x) := Nat.card_pos
  have hle : Nat.card (MulAction.stabilizer G x) ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1)
      ≤ s ^ s ^ (j + 1) := by
    have hs1 : 0 < s := lt_of_lt_of_le hpos hcard
    calc Nat.card (MulAction.stabilizer G x) ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1)
        ≤ s ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1) := Nat.pow_le_pow_left hcard _
      _ ≤ s ^ s ^ (j + 1) := Nat.pow_le_pow_right hs1 (Nat.pow_le_pow_left hcard _)
  exact transport.2.1 _ _ e.symm.toEquiv _ (transport.2.2.2 _ _ _ hle h1)
