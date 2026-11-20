import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.TranscendenceTraces.wtUnique_of :
    WtVanish → WtLin → WtUnique := by
  intro hV hL Z S p _ w w' hw hw' D hD hagree
  have hdiff : IsWt p (w.add (Wt.smul (-1) w')) := hL.1 p w _ hw (hL.2.1 p (-1) w' hw')
  have h0 := hV p _ hdiff D hD (by
    intro Ω _ _ z hz
    show w Ω z + (-1) * w' Ω z = 0
    rw [hagree Ω z hz]
    ring)
  funext Ω _ _ z
  have h := congrFun (congrFun (congrFun (congrFun h0 Ω) ‹_›) ‹_›) z
  change w Ω z + (-1) * w' Ω z = 0 at h
  linarith
