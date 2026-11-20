import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

/- English proof (translation)
Introduce `Q S hS h1 h3 P hP n hn`. Take `⟨z, hz⟩` from `GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS`. Establish `e` using `(hz (sgl ((free ℤ).obj P)) n).1`. Use `haveI := h1 P hP n hn`. Use `haveI := h3 P hP n hn`.

Use `⟨fun y y' => ?_⟩` and prove the remaining obligations. Establish `hy : ∀ u : HK ℤ (sgl ((free ℤ).obj P)) S.X₂ n, u = 0`. Introduce `u`. Take `⟨v, hv⟩` from `(e u).1 (Subsingleton.elim _ _)`. Rewrite using `[← hv, Subsingleton.elim v 0, map_zero]`.

Rewrite using `[hy y, hy y']`.
-/
theorem UpperTheory.acy_middle_of_shortExact :
    ∀ (Q : Scheme.{0} → Prop) (S : ShortComplex (Shv ℤ)), S.ShortExact → Acy Q S.X₁ → Acy Q S.X₃ → Acy Q S.X₂ := by
  intro Q S hS h1 h3 P hP n hn
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence ℤ S hS
  have e := (hz (sgl ((free ℤ).obj P)) n).1
  haveI := h1 P hP n hn
  haveI := h3 P hP n hn
  refine ⟨fun y y' => ?_⟩
  have hy : ∀ u : HK ℤ (sgl ((free ℤ).obj P)) S.X₂ n, u = 0 := by
    intro u
    obtain ⟨v, hv⟩ := (e u).1 (Subsingleton.elim _ _)
    rw [← hv, Subsingleton.elim v 0, map_zero]
  rw [hy y, hy y']
