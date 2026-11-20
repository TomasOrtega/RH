import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.ThetaPtOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

/- English proof (translation)
Take `⟨S, hS⟩` from `KFock.fPSch (1 : PX m n) hδ`. Use `⟨S, funext fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[hS u]`. Simplify using `[evX, gs, sq, Complex.ofReal_exp, neg_mul]`.
-/
theorem isSw_gauss {m n : ℕ} {δ : ℝ} (hδ : 0 < δ) : IsSw (fun u : Fin m → Fin n → ℂ => (Real.exp (-δ * sq u) : ℂ)) := by
  obtain ⟨S, hS⟩ := KFock.fPSch (1 : PX m n) hδ
  refine ⟨S, funext fun u => ?_⟩
  rw [hS u]
  simp [evX, gs, sq, Complex.ofReal_exp, neg_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d R w L hL Ψ hΨ g`. Take `⟨x, y₀, hg, hx⟩` from `hD F E σ d R w g`. Establish `hind : d.Indep w Ψ` using `KFock.away_inv R w Ψ hΨ`. Take `⟨A, hA⟩` from `hAw F E σ d R w x hx`. Take `⟨-, hAT⟩` from `hA Ψ hind`.

Use `⟨y₀, A Ψ, ?_, ?_⟩` and prove the remaining obligations. Introduce `Φ hΦ f hf hT' y`. Establish `h1` using `(hL (y₀ * y) f hf).2 Ψ hind Φ hΦ hT'`. Establish `hmem : d.om (R.ι w (y₀ * y)) Φ ∈ d.sch` using `om_mem d _ hΦ`. Establish `h2` using `hAT (L (y₀ * y) f) (hL (y₀ * y) f hf).1 _ hmem h1`.

Rewrite using `[hg, mul_assoc, ← map_mul (R.ι w), map_mul d.om, Module.End.mul_apply]`. Conclude with `h2`. Introduce `δ hδ`. Take `⟨hTs, hTsurj, -⟩` from `hT.1 F E σ d`. Establish `hm` using `KFock.tens_mem d R w _ (isSw_gauss hδ) Ψ hΨ`.

Take `⟨Φ, hΦ, hTΦ⟩` from `hTsurj _ hm`. Establish `h2` using `hAT _ (isSw_gauss hδ) Φ hΦ hTΦ`. Rewrite using `[← h2]`. Conclude with `hTs _ (om_mem d x hΦ)`.
-/
theorem splitDom_of (hT : TAll) (hAw : AwayAct) (hD : DecompW) : SplitDom := by
  intro F E _ _ _ _ _ σ d R w L hL Ψ hΨ g
  obtain ⟨x, y₀, hg, hx⟩ := hD F E σ d R w g
  have hind : d.Indep w Ψ := KFock.away_inv R w Ψ hΨ
  obtain ⟨A, hA⟩ := hAw F E σ d R w x hx
  obtain ⟨-, hAT⟩ := hA Ψ hind
  refine ⟨y₀, A Ψ, ?_, ?_⟩
  · intro Φ hΦ f hf hT' y
    have h1 := (hL (y₀ * y) f hf).2 Ψ hind Φ hΦ hT'
    have hmem : d.om (R.ι w (y₀ * y)) Φ ∈ d.sch := om_mem d _ hΦ
    have h2 := hAT (L (y₀ * y) f) (hL (y₀ * y) f hf).1 _ hmem h1
    rw [hg, mul_assoc, ← map_mul (R.ι w), map_mul d.om, Module.End.mul_apply]
    exact h2
  · intro δ hδ
    obtain ⟨hTs, hTsurj, -⟩ := hT.1 F E σ d
    have hm := KFock.tens_mem d R w _ (isSw_gauss hδ) Ψ hΨ
    obtain ⟨Φ, hΦ, hTΦ⟩ := hTsurj _ hm
    have h2 := hAT _ (isSw_gauss hδ) Φ hΦ hTΦ
    rw [← h2]
    exact hTs _ (om_mem d x hΦ)

end PositivityTheory.SiegelWeilFormula.Kdil

end
