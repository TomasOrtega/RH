import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistDiscreteCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterThetaInvariantExponent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
open scoped Classical

open NumberField GlobalTheory.CuspRep Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.WeightJoin

/- English proof (translation)
Introduce `E _ _ _ hU n a b μ e π lam n₁ n₂ hn hμ hπ hw h₁ h₂ hinf τ lam' hτ`. Take `⟨-, he, hc⟩` from `GlobalTheory.BCT.MuProps.main E hU μ e hμ`. Set `U : GlobalTheory.DefU.AutSub E n` to `⟨π, hπ⟩`. Rewrite using `[GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.TwistDisc.expo_pow]`. Break down `NumberField.InfinitePlace.embedding_mk_eq τ with h | h` into its components or cases.

Establish `hv` using `hw (InfinitePlace.mk τ)`. Establish `hinfv` using `hinf (InfinitePlace.mk τ)`. Establish `hev` using `he (InfinitePlace.mk τ)`. Rewrite `hv`, `hinfv`, `hev` using `[h]`. Rewrite using `[GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, hev, ← hinfv]`.

Apply the tactic sequence `congr 1 <;> exact Multiset.map_congr rfl fun x _ => by ring`. Establish `hv` using `GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn (hw (InfinitePlace.mk τ))`. Establish `hinfv` using `hinf (InfinitePlace.mk τ)`. Establish `hev` using `hc (InfinitePlace.mk τ)`. Establish `hs₁` using `(h₁ (InfinitePlace.mk τ).embedding).2`.

Establish `hs₂` using `(h₂ (InfinitePlace.mk τ).embedding).2`. Establish `hcc : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ`. Rewrite using `[h]`. Conclude with `star_star τ`. Establish `hcc' : (starRingEnd ℂ).comp (InfinitePlace.mk τ).embedding = τ` using `hcc`.

Rewrite `hs₁`, `hs₂` using `[hcc']`. Rewrite `hv`, `hev` using `[hcc]`. Rewrite using `[GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, GlobalTheory.DefiniteBC.infOfWeight_dual, ← hinfv, hev, hs₁, hs₂, Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map]`. Apply the tactic sequence `congr 1 <;> exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring`.
-/
theorem main : PositivityTheory.Rg.BcB.F.RS.WeightJoin := by
  intro E _ _ _ hU n a b μ e π lam n₁ n₂ hn hμ hπ hw h₁ h₂ hinf τ lam' hτ
  obtain ⟨-, he, hc⟩ := GlobalTheory.BCT.MuProps.main E hU μ e hμ
  let U : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.TwistDisc.expo_pow]
  rcases NumberField.InfinitePlace.embedding_mk_eq τ with h | h
  · have hv := hw (InfinitePlace.mk τ)
    have hinfv := hinf (InfinitePlace.mk τ)
    have hev := he (InfinitePlace.mk τ)
    rw [h] at hv hinfv hev
    rw [GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, hev, ← hinfv]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ => by ring
  · have hv := GlobalTheory.DefiniteBC.hasWeightAt_conjugate hn (hw (InfinitePlace.mk τ))
    have hinfv := hinf (InfinitePlace.mk τ)
    have hev := hc (InfinitePlace.mk τ)
    have hs₁ := (h₁ (InfinitePlace.mk τ).embedding).2
    have hs₂ := (h₂ (InfinitePlace.mk τ).embedding).2
    have hcc : ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding = τ := by
      rw [h]; exact star_star τ
    have hcc' : (starRingEnd ℂ).comp (InfinitePlace.mk τ).embedding = τ := hcc
    rw [hcc'] at hs₁ hs₂
    rw [hcc] at hv hev
    rw [GlobalTheory.DefU.hasWeightAt_unique U τ hτ hv, GlobalTheory.DefiniteBC.infOfWeight_dual, ← hinfv, hev, hs₁, hs₂,
      Multiset.map_add, Multiset.map_map, Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1 <;> exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

end GlobalTheory.CompanionTheory.WeightJoin

end
