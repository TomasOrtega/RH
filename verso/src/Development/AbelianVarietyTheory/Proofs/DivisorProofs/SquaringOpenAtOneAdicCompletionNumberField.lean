import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZeroStatement
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

noncomputable section

namespace GlobalTheory.QSA

/- English proof (translation)
Introduce `F _ _ v`. Use `letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _`. Establish `h2 : (2 : v.adicCompletion F) ≠ 0`. Introduce `h`. Establish `h' : algebraMap F (v.adicCompletion F) 2 = algebraMap F (v.adicCompletion F) 0`.

Rewrite using `[map_ofNat, map_zero]`. Conclude with `h`. Conclude with `two_ne_zero ((algebraMap F (v.adicCompletion F)).injective h')`. Use `⟨GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero (v.adicCompletion F) h2, ?_⟩` and prove the remaining obligations. Use `infer_instance`.
-/
theorem sqOpen_and_nhdsNE_zero_neBot_adicCompletion :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      SqOpen (v.adicCompletion F) ∧ (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
  intro F _ _ v
  letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    intro h
    have h' : algebraMap F (v.adicCompletion F) 2 = algebraMap F (v.adicCompletion F) 0 := by
      rw [map_ofNat, map_zero]; exact h
    exact two_ne_zero ((algebraMap F (v.adicCompletion F)).injective h')
  refine ⟨GlobalTheory.T.squaringOpenAtOne_of_complete_two_ne_zero (v.adicCompletion F) h2, ?_⟩
  infer_instance

end GlobalTheory.QSA

end
