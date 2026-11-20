import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

/- English proof (translation)
Introduce `R _ tr nm ρ hρ hd u`. Take `⟨w, hw⟩` from `hd.exists_right_inv`. Use `⟨1 - ((tr : R) - ρ) * ((u - 1) * w), (u - 1) * w, ?_⟩` and prove the remaining obligations. Unfold `qf`. Take the linear combination `((u - 1) * w) ^ 2 * hρ + (u - 1) * hw`.
-/
theorem UpperTheory.Gal.G1.pSplitRep :
    SplitRep := by
  intro R _ tr nm ρ hρ hd u
  obtain ⟨w, hw⟩ := hd.exists_right_inv
  refine ⟨1 - ((tr : R) - ρ) * ((u - 1) * w), (u - 1) * w, ?_⟩
  unfold qf
  linear_combination ((u - 1) * w) ^ 2 * hρ + (u - 1) * hw
