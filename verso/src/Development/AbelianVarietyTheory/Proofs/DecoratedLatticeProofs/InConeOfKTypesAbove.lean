import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverCone

/- English proof (translation)
Introduce `KTA p q n e P T R σ hb hσ hds μ v hv`. Take `⟨S, hS⟩` from `GlobalTheory.RealPar.isKTypeOf_of_isHW R hb hσ μ ⟨v, hv⟩`. Take `⟨c, hc, hμ⟩` from `KTA n P.sgn P.lam R.U.H σ P.hc hds _ S hS`. Use `⟨fun a b => c (e a) (e b), fun a b hab => ?_, ?_⟩` and prove the remaining obligations. Establish `h2` using `P.hc.1 (hc _ _ hab)`.

Rewrite `h2` using `[← GlobalTheory.RealPar.ratEntry_cast, ← GlobalTheory.RealPar.ratEntry_cast]`. Conclude with `h2` after adjusting the coercions. Use function extensionality and compare the values at `x`. Apply `Rat.cast_injective (α := ℝ)` to reduce the goal to its premises. Establish `hx` using `congrFun hμ (e x)`.

Simplify using `only [Equiv.symm_apply_apply] at hx`. Use `push_cast`. Rewrite using `[hx, GlobalTheory.RealPar.blattner_eq P hb (lam := GlobalTheory.RealPar.blockPar P e) (fun a => GlobalTheory.RealPar.ratEntry_cast P (e a)) x]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]`. Use `congr 1`.

Rewrite using `[← e.sum_comp]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← e.sum_comp]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.RealPar.root_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem inCone_of_kTypesAbove : GlobalTheory.Dec.KTypesAbove → ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone (blockPar P e) μ := by
  intro KTA p q n e P T R σ hb hσ hds μ v hv
  obtain ⟨S, hS⟩ := GlobalTheory.RealPar.isKTypeOf_of_isHW R hb hσ μ ⟨v, hv⟩
  obtain ⟨c, hc, hμ⟩ := KTA n P.sgn P.lam R.U.H σ P.hc hds _ S hS
  refine ⟨fun a b => c (e a) (e b), fun a b hab => ?_, ?_⟩
  · have h2 := P.hc.1 (hc _ _ hab)
    rw [← GlobalTheory.RealPar.ratEntry_cast, ← GlobalTheory.RealPar.ratEntry_cast] at h2
    exact_mod_cast h2
  · funext x
    apply Rat.cast_injective (α := ℝ)
    have hx := congrFun hμ (e x)
    simp only [Equiv.symm_apply_apply] at hx
    push_cast
    rw [hx, GlobalTheory.RealPar.blattner_eq P hb (lam := GlobalTheory.RealPar.blockPar P e) (fun a => GlobalTheory.RealPar.ratEntry_cast P (e a)) x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.RealPar.root_apply]
    split_ifs <;> simp

end GlobalTheory.CoverCone
