import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `hsec het l Y T U hU`. Take `⟨hZ, hpts⟩` from `hsec l Y T U hU`. Establish `hfin` using `@IsFinite.finite_app _ _ _ T.fin U hU`. Use `letI : Algebra Γ(Y, U) Γ(T.Z, T.p ⁻¹ᵁ U) := (T.p.app U).hom.toAlgebra`. Use `EtAway.mk hfin (het l Y T U hU) ?_` and prove the remaining obligations.

Introduce `K _ _ _ hl`. Take `⟨e, -⟩` from `hpts K`. Rewrite using `[Nat.card_congr e]`. Conclude with `T.deg K hl _`.
-/
theorem UpperTheory.Gal.crystallineComparison.etAway_of :
    SecChart → EtChart → EtAwayChart := by
  intro hsec het l Y T U hU
  obtain ⟨hZ, hpts⟩ := hsec l Y T U hU
  have hfin := @IsFinite.finite_app _ _ _ T.fin U hU
  letI : Algebra Γ(Y, U) Γ(T.Z, T.p ⁻¹ᵁ U) := (T.p.app U).hom.toAlgebra
  refine EtAway.mk hfin (het l Y T U hU) ?_
  intro K _ _ _ hl
  obtain ⟨e, -⟩ := hpts K
  rw [Nat.card_congr e]
  exact T.deg K hl _
