import Mathlib
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SplitLevelConjugates.IsPrincipalCongruenceAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjEqOfNormalises
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMemKOneOfSame

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.HeightCounting
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `L _ _ _ n a S hS s f hf hf0 hfix σ hσ`. Take `⟨c, T, hc, hci, -⟩` from `id hσ`. Establish `hiso : f ∈ NG.isoTyp a.ρ S` using `(le_sSup (s := {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'}) ⟨hS, LinearEquiv.refl ℂ S, fun _ _ _ e => e⟩ : S ≤ NG.isoTyp a.ρ S) hf`. Establish `hint : ∀ g ∈ KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n), g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring` using `fun g hg => by`. Rewrite using `[(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]`.

Conclude with `GlobalTheory.StepData.KOne_le_KO hg`. Take `⟨u, hu0, hu⟩` from `GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci (KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)) 1 hint (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ) f hiso hf0 (fun κ hκ h => by`. Rewrite using `[hfix κ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκ).1 (hint _ h)) hκ ((GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 h)]`. Use the proof step `simp)`. Rewrite using `[Submodule.ne_bot_iff]`.

Use `⟨u, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hu0⟩` and prove the remaining obligations. Establish `e : Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom h) = h`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `hg` using `GlobalTheory.FixedAtSplit.mem_KOne_of_map c hc _ (e.symm ▸ hh)`.

Establish `h3` using `hu _ hg`. Rewrite `h3` using `[e]`. Simplify using `using h3`.
-/
theorem UpperTheory.One.M.B.fixOne :
    UpperTheory.One.M.B.FixOne := by
  intro L _ _ _ n a S hS s f hf hf0 hfix σ hσ
  obtain ⟨c, T, hc, hci, -⟩ := id hσ
  have hiso : f ∈ NG.isoTyp a.ρ S :=
    (le_sSup (s := {S' | NG.IsIrrRep a.ρ S' ∧ NG.IsoRep S S'})
      ⟨hS, LinearEquiv.refl ℂ S, fun _ _ _ e => e⟩ : S ≤ NG.isoTyp a.ρ S) hf
  have hint : ∀ g ∈ KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n),
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun g hg => by
    rw [(GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne s.v n).1]
    exact GlobalTheory.StepData.KOne_le_KO hg
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.LocVec.main L n a S hS s σ hσ c hc hci
    (KOne (s.v.adicCompletion (maximalRealSubfield L)) (Fin n)) 1 hint
    (by rw [MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ)
    f hiso hf0 (fun κ hκ h => by
      rw [hfix κ ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hκ).1 (hint _ h)) hκ
        ((GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 h)]
      simp)
  rw [Submodule.ne_bot_iff]
  refine ⟨u, GlobalTheory.Parabolic.mem_fixed.2 fun h hh => ?_, hu0⟩
  have e : Matrix.GeneralLinearGroup.map c.toRingHom (Matrix.GeneralLinearGroup.map c.symm.toRingHom h) = h := by
    ext i j
    simp
  have hg := GlobalTheory.FixedAtSplit.mem_KOne_of_map c hc _ (e.symm ▸ hh)
  have h3 := hu _ hg
  rw [e] at h3
  simpa using h3
