import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGen
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.IwaAd

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simpa using holValueAt_const 0 s₀`. Consider the case `insert i T hi ih`. Establish `h` using `(a i (Finset.mem_insert_self i T)).add (ih fun j hj => a j (Finset.mem_insert_of_mem hj))`. Simplify `h` using `only [Finset.sum_insert hi]`.
-/
theorem holValueAt_finset_sum {ι : Type*} (T : Finset ι) {f : ι → ℂ → ℂ} {c : ι → ℂ} {s₀ : ℂ}
    (a : ∀ i ∈ T, HolValueAt (f i) s₀ (c i)) :
    HolValueAt (fun z => ∑ i ∈ T, f i z) s₀ (∑ i ∈ T, c i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using holValueAt_const 0 s₀
  | insert i T hi ih =>
    have h := (a i (Finset.mem_insert_self i T)).add
      (ih fun j hj => a j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h

/- English proof (translation)
Introduce `hGen hDict D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk`. Take `⟨N, φs, vals, ⟨t, ht⟩, hv, hm⟩` from `hDict D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk`. Take `⟨⟨𝓕, h𝓕⟩, -⟩` from `GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν hS.hν`. Establish `key : ∀ j, HolValueAt (whitT ψ V μ lam nb w H (φs j) (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n) (vals j)`. Introduce `j`.

Take `⟨d, bs, θG, lG, εG, frG, gG, PG, lamG, L₁, L₂, ΦG, Φf, Φv, μG, νG, ψG, hDat, C, ⟨t', ht'⟩, hval⟩` from `hm j`. Establish `h` using `hGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hDat ⟨t', fun z hz => (ht' z hz).1⟩ ν 𝓕 hS.hν h𝓕`. Establish `e : ((V.rank : ℂ) - n) / 2 = s0 V n`. Simplify using `only [s0]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hval ν 𝓕 hS.hν h𝓕]`. Establish `h2` using `(holValueAt_const C _).mul h`. Rewrite `h2` using `[e]`. Conclude with `h2.congr ⟨t', fun z hz => ((ht' z hz).2).symm⟩`. Rewrite using `[hv]`.

Conclude with `(holValueAt_finset_sum Finset.univ fun j _ => key j).congr ⟨t, fun z hz => (ht z hz).symm⟩`.
-/
theorem whitKAOfGen : PositivityTheory.PfSWUS.WhitKAOfGen := by
  intro hGen hDict D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨N, φs, vals, ⟨t, ht⟩, hv, hm⟩ := hDict D n V ψ χ θ μ ω H l s ν Φ hS hR lam 𝓖 nb hC w hw β hβ a k hk
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν hS.hν
  have key : ∀ j, HolValueAt (whitT ψ V μ lam nb w H (φs j) (adj a.1 * β.1.map (incA D) * a.1) k) (s0 V n) (vals j) := by
    intro j
    obtain ⟨d, bs, θG, lG, εG, frG, gG, PG, lamG, L₁, L₂, ΦG, Φf, Φv, μG, νG, ψG, hDat, C, ⟨t', ht'⟩, hval⟩ := hm j
    have h := hGen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hDat ⟨t', fun z hz => (ht' z hz).1⟩ ν 𝓕 hS.hν h𝓕
    have e : ((V.rank : ℂ) - n) / 2 = s0 V n := by
      simp only [s0]
      ring
    rw [hval ν 𝓕 hS.hν h𝓕]
    have h2 := (holValueAt_const C _).mul h
    rw [e] at h2
    exact h2.congr ⟨t', fun z hz => ((ht' z hz).2).symm⟩
  rw [hv]
  exact (holValueAt_finset_sum Finset.univ fun j _ => key j).congr ⟨t, fun z hz => (ht z hz).symm⟩

end GlobalTheory.CompanionTheory.IwaAd

end
