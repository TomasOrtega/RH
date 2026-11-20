import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFromAlt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FinitePtsOfCurve

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

/- English proof (translation)
Introduce `hPi hBQ D B P j X ka wL wF G la Q S CRm T e c hOk k`. Establish `hC : Q.InCurve` using `hOk.2.1`. Use `haveI : FiniteDimensional (Kp X la G.N) (OsK X la G.w) := hC.1`. Use `haveI : IsReduced (OsK X la G.w) := hC.2.1`. Use `haveI : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC`.

Establish `hU` using `isUnif_of_curve Q hC`. Establish `hle : ballO (unifO X la G.N) Q.e Q.c ≤ ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ))`. Introduce `v hv`. Conclude with `ball_mono hU hC.2.2 (fun ζ => by dsimp only; omega) hv`. Establish `h1` using `hPi (Op X la G.N) (SectionSheafQuotient X la G.w wF) (Mon (WeightFamilies.dimY D j) k) (ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ))) (ballO (unifO X la G.N) Q.e Q.c) hle`.

Establish `h2` using `hBQ (Op X la G.N) (Kp X la G.N) (OsK X la G.w) (unifO X la G.N) (unifO_irreducible X la G.N) (finite_As_of_curve Q hC) (SectionSheafQuotient X la G.w wF) Q.e hC.2.2 Q.c (Q.mm S T e)`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[h2, Fintype.card_coe, Nat.cast_mul]`.
-/
theorem ball_product_length : PiBallFrom := by
  intro hPi hBQ D B P j X ka wL wF G la Q S CRm T e c hOk k

  have hC : Q.InCurve := hOk.2.1
  haveI : FiniteDimensional (Kp X la G.N) (OsK X la G.w) := hC.1
  haveI : IsReduced (OsK X la G.w) := hC.2.1
  haveI : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  have hU := isUnif_of_curve Q hC

  have hle : ballO (unifO X la G.N) Q.e Q.c ≤
      ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ)) := by
    intro v hv
    exact ball_mono hU hC.2.2 (fun ζ => by dsimp only; omega) hv

  have h1 := hPi (Op X la G.N) (SectionSheafQuotient X la G.w wF) (Mon (WeightFamilies.dimY D j) k)
    (ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ)))
    (ballO (unifO X la G.N) Q.e Q.c) hle
  have h2 := hBQ (Op X la G.N) (Kp X la G.N) (OsK X la G.w) (unifO X la G.N)
    (unifO_irreducible X la G.N) (finite_As_of_curve Q hC) (SectionSheafQuotient X la G.w wF) Q.e hC.2.2 Q.c (Q.mm S T e)
  refine h1.trans ?_
  rw [h2, Fintype.card_coe, Nat.cast_mul]

end PI.PoleLengthCount
