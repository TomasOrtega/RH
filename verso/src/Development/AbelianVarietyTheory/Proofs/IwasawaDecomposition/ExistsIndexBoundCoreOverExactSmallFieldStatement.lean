import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsIndexBoundCoreOverExactSmallField.lean&line=39#L39)
-/
theorem _root_.GlobalTheory.T.character_value_mem_smallField_of_infPart_eq_one : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  first | exact @GlobalTheory.CoreExact.exists_core_exact | exact GlobalTheory.CoreExact.exists_core_exact | (intros; apply GlobalTheory.CoreExact.exists_core_exact <;> assumption)
