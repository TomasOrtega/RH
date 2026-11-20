import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Introduce `Z' S' Z S v p' p g w h hw`. Unfold `IsWt at *`. Introduce `A φ hφ`. Take `⟨ψ, hψ, e⟩` from `hw ⟨A.U, A.V, A.u ≫ g, A.v ≫ v, A.r, A.pb.paste_horiz h⟩ φ hφ`. Use `⟨ψ, hψ, ?_⟩` and prove the remaining obligations.

Introduce `Ω _ _ x`. Rewrite using `[e]`. Use `finsum_congr fun z => finsum_congr fun _ => ?_` and prove the remaining obligations. Use `show w Ω (z ≫ A.v ≫ v) * _ = w Ω ((z ≫ A.v) ≫ v) * _`. Rewrite using `[Category.assoc]`.
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
