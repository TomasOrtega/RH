import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtBC_of :
    WtBC := by
  intro Z' S' Z S v p' p g w h hw
  unfold IsWt at *
  intro A φ hφ
  obtain ⟨ψ, hψ, e⟩ := hw ⟨A.U, A.V, A.u ≫ g, A.v ≫ v, A.r, A.pb.paste_horiz h⟩ φ hφ
  refine ⟨ψ, hψ, ?_⟩
  intro Ω _ _ x
  rw [e]
  refine finsum_congr fun z => finsum_congr fun _ => ?_
  show w Ω (z ≫ A.v ≫ v) * _ = w Ω ((z ≫ A.v) ≫ v) * _
  rw [Category.assoc]
