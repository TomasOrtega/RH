import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Use symmetry to reverse the relation.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TranscendenceTraces.nwtDeg_of :
    WtNormal → WtDegConst → MultSum → MultBC → GenBasic → NwtDeg := by
  intro hN hD hMS hBC hG Z' Z S K _ v p' p g _ _ hpb hLoc hg
  obtain ⟨hW, hgen⟩ := hN p hLoc
  obtain ⟨d, hd⟩ := hD p (nwt p) hW
  rw [hd]
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  let Ω := AlgebraicClosure K
  let y : gp Ω ⟶ gp K := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have hval := congrArg (fun w : Wt S => w Ω (y ≫ g)) hd
  simp only [Wt.const] at hval
  have h1 : Wt.push p (nwt p) Ω (y ≫ g) = Wt.push p (mult p) Ω (y ≫ g) := by
    simp only [Wt.push]
    apply finsum_congr
    intro z
    apply finsum_congr
    intro hz
    apply hgen
    have hz' : z ≫ p = y ≫ g := hz
    rw [hz', pt_comp, Subsingleton.elim (pt y) (IsLocalRing.closedPoint K)]
    exact (hG.2.2 S _).mpr hg
  have h2 : Wt.push p (mult p) Ω (y ≫ g) = Wt.push p' (mult p') Ω y := by
    simp only [Wt.push]
    symm
    rw [finsum_mem_eq_of_bijOn (fun z => z ≫ v) (fib_bijOn hpb y)
      (g := fun z => mult p Ω z)]
    intro z _
    rw [hBC v p' p g hpb]
    rfl
  have h3 := hMS p' Ω y
  have h4 : pt y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  rw [h1, h2, h3, h4] at hval
  rw [hval]
