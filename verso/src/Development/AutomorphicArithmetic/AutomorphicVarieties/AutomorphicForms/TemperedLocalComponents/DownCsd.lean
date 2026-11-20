import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RankTwoAutomorphyDescendsFromAbelianCMToRat
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AutBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CsdOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclotomicCharacterSecond

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.Base

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree

attribute [local instance] tf

/- English proof (translation)
Supply the required witnesses or components.
-/
private theorem algClo (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem cyc_cont (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.ContinuityOfCyclotomicCharacter.cyc_cont F Ω l

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
private theorem cyc_conj {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    {c c' : G F Ω} (h : UpperTheory.V.Af.IsConjEl c) (h' : UpperTheory.V.Af.IsConjEl c') : cycBar F Ω l c = cycBar F Ω l c' := by
  have h1 : cycZ F Ω l c = -1 := UpperTheory.V.IsConjOm.cyc (E := F) (σ := c.toRingEquiv) h
  have h2 : cycZ F Ω l c' = -1 := UpperTheory.V.IsConjOm.cyc (E := F) (σ := c'.toRingEquiv) h'
  simp only [cycBar, MonoidHom.comp_apply, h1, h2]
