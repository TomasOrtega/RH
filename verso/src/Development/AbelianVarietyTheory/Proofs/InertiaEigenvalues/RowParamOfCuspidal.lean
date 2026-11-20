import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodIdempotentFixesMemGoodTypeSpace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

/- English proof (translation)
Introduce `D Rw hP hC hS j hj1 hj2 σ hσ hg`. Take `⟨π, h⟩` from `hP j hj1 hj2 σ hσ hg`. Establish `hembb : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true` using `fun τ => by`. Use extensionality with `x`. Establish `e : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true x = starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false x)` using `D.host.conjE_apply (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false) x`.

Rewrite using `[e]`. Both sides reduce to the same expression. Establish `hpar : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) = (GlobalTheory.Triple.rowPar (D.hc τ)).map (fun p => ((p : ℚ) : ℂ))`. Introduce `τ`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma, GlobalTheory.Triple.rowPar, Multiset.map_add, Multiset.map_map, Function.comp_def]`.

Use `⟨π, ⟨h.1, h.2.1, fun τ => ?_, fun w hw => h.unr w hw, fun k v => ?_, hC j hj1 hj2 σ hσ hg⟩, h.2.2.1⟩` and prove the remaining obligations. Take `⟨a, b⟩` from `h.2.2.2.2.2 τ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hpar]`. Conclude with `a`.

Rewrite using `[← hembb, b, hpar, Multiset.map_map]`. Use `Multiset.map_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[Rw.lab_eq k σ v, h.2.2.1 _ (hS k v)]`.
-/
theorem rowParam_of_cuspParam : ∀ (D : D7) (Rw : RowSide D), GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw → (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → D.ntypes.cuspidal σ) → (∀ k v, IsSplitPl D.host (D.naut.plGw k v)) → RowParam D Rw := by
  intro D Rw hP hC hS j hj1 hj2 σ hσ hg
  obtain ⟨π, h⟩ := hP j hj1 hj2 σ hσ hg
  have hembb : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true := fun τ => by
    ext x
    have e : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ true x = starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false x) :=
      D.host.conjE_apply (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D τ false) x
    rw [e]
    rfl
  have hpar : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) = (GlobalTheory.Triple.rowPar (D.hc τ)).map (fun p => ((p : ℚ) : ℂ)) := by
    intro τ
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma, GlobalTheory.Triple.rowPar, Multiset.map_add, Multiset.map_map, Function.comp_def]
  refine ⟨π, ⟨h.1, h.2.1, fun τ => ?_, fun w hw => h.unr w hw, fun k v => ?_, hC j hj1 hj2 σ hσ hg⟩, h.2.2.1⟩
  · obtain ⟨a, b⟩ := h.2.2.2.2.2 τ
    refine ⟨?_, ?_⟩
    · rw [← hpar]; exact a
    · rw [← hembb, b, hpar, Multiset.map_map]
      refine Multiset.map_congr rfl fun p _ => ?_
      simp
  · rw [Rw.lab_eq k σ v, h.2.2.1 _ (hS k v)]
end GlobalTheory.TwInputs
