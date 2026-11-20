import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.WeightNat

/- English proof (translation)
Introduce `D ψ θ A A' WW FA FW a b α β ωA hθ hA hW hT hexp hWeil hf`. Take `⟨f, hf, hf0⟩` from `hf`. Establish `key : ∀ τ, ∃ z : ℤ, (z : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2 ∧ 0 ≤ z`. Introduce `τ`. Take `⟨a', b', ha', hb', hgap⟩` from `hT.gap τ`.

Establish `e1` using `GlobalTheory.Mem.HeckeExp.hasInfExp_unique ha' (hexp τ).1`. Establish `e2` using `GlobalTheory.Mem.HeckeExp.hasInfExp_unique hb' (hexp τ).2`. Establish `hdiv` using `GlobalTheory.RealQuot.hasInfExp_div D α β τ (a τ) (b τ) (hexp τ).1 (hexp τ).2`. Take `⟨x, y, hx, -, -⟩` from `GlobalTheory.CompactFockAction.compactFockAll D _ WW (GlobalTheory.SquareComm.frSgn true FA) FW θ ψ β (β / α) (ωA.toSgn true) f τ (b τ) (b τ - a τ) hθ hWeil (hexp τ).2 hdiv hf hf0`. Take `⟨p, q, -, hr, -⟩` from `hT.sig`.

Establish `hpos : 0 < A.rank` using `by omega`. Establish `h1` using `hx ⟨0, hpos⟩`. Generalize the expression as in `(GlobalTheory.SquareComm.frSgn true FA).ε τ ⟨0, hpos⟩ = e at h1`. Establish `h2` using `GlobalTheory.CompactFockAction.card_sign (FW.ε τ) e`. Use `set c := (Finset.univ.filter fun i => FW.ε τ i = e).card`.

Establish `hz : ((-(c : ℤ) - x e : ℤ) : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2`. Use `push_cast`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.wtS at h1`. Apply the tactic sequence `cases e <;> simp at h1 h2 <;> linarith`. Establish `hq : (0 : ℚ) < b τ - a τ - (WW.rank : ℚ) / 2`.

Rewrite using `[← e1, ← e2]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨-(c : ℤ) - x e, hz, ?_⟩` and prove the remaining obligations. Establish `: (0 : ℚ) ≤ ((-(c : ℤ) - x e : ℤ) : ℚ)` using `by rw [hz]; exact hq.le`. Conclude with `this` after adjusting the coercions.

Use `choose z hz hz0 using key`. Use `⟨fun τ => (z τ).toNat, fun τ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hz τ]`. Conclude with `Int.toNat_of_nonneg (hz0 τ)` after adjusting the coercions.
-/
theorem weight_nat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW)
    (a b : D.what₂.Tau → ℚ) (α β : (Formalism.L2.Theta.AE D)ˣ →* Circle) (ωA : GlobalTheory.Grid.WRep A WW), IsInfFam θ →
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
    GlobalTheory.Grid.IsWeil ψ true A WW β (β / α) ωA → (∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ f ≠ 0) →
    ∃ n₀ : D.what₂.Tau → ℕ, ∀ τ, (n₀ τ : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2 := by
  intro D ψ θ A A' WW FA FW a b α β ωA hθ hA hW hT hexp hWeil hf
  obtain ⟨f, hf, hf0⟩ := hf
  have key : ∀ τ, ∃ z : ℤ, (z : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2 ∧ 0 ≤ z := by
    intro τ
    obtain ⟨a', b', ha', hb', hgap⟩ := hT.gap τ
    have e1 := GlobalTheory.Mem.HeckeExp.hasInfExp_unique ha' (hexp τ).1
    have e2 := GlobalTheory.Mem.HeckeExp.hasInfExp_unique hb' (hexp τ).2
    have hdiv := GlobalTheory.RealQuot.hasInfExp_div D α β τ (a τ) (b τ) (hexp τ).1 (hexp τ).2
    obtain ⟨x, y, hx, -, -⟩ := GlobalTheory.CompactFockAction.compactFockAll D _ WW (GlobalTheory.SquareComm.frSgn true FA) FW θ ψ β (β / α)
      (ωA.toSgn true) f τ (b τ) (b τ - a τ) hθ hWeil (hexp τ).2 hdiv hf hf0
    obtain ⟨p, q, -, hr, -⟩ := hT.sig
    have hpos : 0 < A.rank := by omega
    have h1 := hx ⟨0, hpos⟩
    generalize (GlobalTheory.SquareComm.frSgn true FA).ε τ ⟨0, hpos⟩ = e at h1
    have h2 := GlobalTheory.CompactFockAction.card_sign (FW.ε τ) e
    set c := (Finset.univ.filter fun i => FW.ε τ i = e).card
    have hz : ((-(c : ℤ) - x e : ℤ) : ℚ) = b τ - a τ - (WW.rank : ℚ) / 2 := by
      push_cast
      unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.wtS at h1
      cases e <;> simp at h1 h2 <;> linarith
    have hq : (0 : ℚ) < b τ - a τ - (WW.rank : ℚ) / 2 := by
      rw [← e1, ← e2]; linarith
    refine ⟨-(c : ℤ) - x e, hz, ?_⟩
    have : (0 : ℚ) ≤ ((-(c : ℤ) - x e : ℤ) : ℚ) := by rw [hz]; exact hq.le
    exact_mod_cast this
  choose z hz hz0 using key
  refine ⟨fun τ => (z τ).toNat, fun τ => ?_⟩
  rw [← hz τ]
  exact_mod_cast Int.toNat_of_nonneg (hz0 τ)

end GlobalTheory.WeightNat
