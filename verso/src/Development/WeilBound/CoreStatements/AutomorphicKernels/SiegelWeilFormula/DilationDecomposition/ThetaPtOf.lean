import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

/- English proof (translation)
Conclude with `d.ok.dbl.weil.2.1.toIsSplitting.pres x Φ hΦ`.
-/
theorem om_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (d : SD σ) (x : d.G) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) : d.om x Φ ∈ d.sch := by
  exact d.ok.dbl.weil.2.1.toIsSplitting.pres x Φ hΦ

/- English proof (translation)
Conclude with `d.ok.dbl.lin.toIsSplitting.pres h Φ hΦ`.
-/
theorem S_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (d : SD σ) (h : UA σ d.A.J) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) : d.S h Φ ∈ d.sch := by
  exact d.ok.dbl.lin.toIsSplitting.pres h Φ hΦ

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d Φ hΦ x h`. Take `⟨-, hPar, -, hTh, -⟩` from `hT`. Establish `hΦ' : d.om x (d.S h Φ) ∈ d.sch` using `om_mem d x (S_mem d h hΦ)`. Rewrite using `[← ((hTh F E σ d _ hΦ').1).tsum_eq, (hTh F E σ d Φ hΦ).2 x h]`. Use `tsum_congr fun X => ?_` and prove the remaining obligations.

Conclude with `(hPar F E σ d _ (om_mem d x hΦ)).2.2 h _`.
-/
theorem thetaPt_of (hT : TAll) : ThetaPt := by
  intro F E _ _ _ _ _ σ d Φ hΦ x h
  obtain ⟨-, hPar, -, hTh, -⟩ := hT
  have hΦ' : d.om x (d.S h Φ) ∈ d.sch := om_mem d x (S_mem d h hΦ)
  rw [← ((hTh F E σ d _ hΦ').1).tsum_eq, (hTh F E σ d Φ hΦ).2 x h]
  refine tsum_congr fun X => ?_
  exact (hPar F E σ d _ (om_mem d x hΦ)).2.2 h _

end PositivityTheory.SiegelWeilFormula.Kdil

end
