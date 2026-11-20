import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 2000000

namespace GlobalTheory.GoodPlaceAtState

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem natCast_mem_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : ((n : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((n : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal := by
  rw [← Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
  refine Ideal.subset_span ⟨(n : 𝓞 K), h, ?_⟩
  simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem natCast_mem_of_conjPl {K : Type} [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (h : ((n : ℕ) : 𝓞 K) ∈ (Formalism.DivisionValues.conjPl w).asIdeal) : ((n : ℕ) : 𝓞 K) ∈ w.asIdeal := by
  have := natCast_mem_conjPl (Formalism.DivisionValues.conjPl w) n h
  rwa [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at this

end GlobalTheory.GoodPlaceAtState

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem GlobalTheory.GoodPlaceAtState.goodPlace_of_split_off : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} (P : Pre2 K w) (x : St P) (v : PlE (Dof x).host), IsSplitPl (Dof x).host v → v ∉ SbD (Dof x) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace x.m.z.R.toRealDat v := by
  intro K B f T w P x v hs hv
  have hc := x.m.z.pins.char
  have hA := hc.allPl
  have hL := hc.base.lev
  have hlow : ∀ k : Fin 2, (((Dof x).host.g k : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro k hk
    apply hv
    refine (lowSet_finite (Dof x)).mem_toFinset.2 ⟨(Dof x).host.g k, ?_, ((Dof x).host.g_prime k).ne_zero, hk⟩
    fin_cases k <;> simp [lowAll]
  have hdiv : ∀ PP, PP ∈ x.m.z.R.toRealDat.Sb → ∃ k : Fin 2, (((Dof x).host.g k : ℕ) : 𝓞 (Dof x).host.E) ∈ PP.asIdeal := by
    intro PP hPP
    have hm : PP ∈ x.m.z.R.Pg := by rw [← hA]; exact hPP
    obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
    exact ⟨k, Formalism.L2.Host.PiBar.overP _ hk⟩

  unfold GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.GoodPlace
  refine ⟨⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hs, fun hm => ?_, fun Q hQ he => ?_⟩, fun hm => ?_⟩
  · obtain ⟨k, hk⟩ := hdiv v hm
    exact hlow k hk
  · obtain ⟨k, hk⟩ := hdiv Q hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at he
    rw [he] at hk
    exact hlow k (GlobalTheory.GoodPlaceAtState.natCast_mem_of_conjPl v _ hk)
  · rw [Nat.cast_mul] at hm
    rcases v.isPrime.mem_or_mem hm with h | h
    · exact hlow 0 h
    · exact hlow 1 h
