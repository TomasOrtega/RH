import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabIffLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivGOfLocalIsometry

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivMove

/- English proof (translation)
Break down `h with ⟨he, rfl⟩ | ⟨rfl, ⟨v, ε, ⟨a, rfl, h1, h2⟩, he⟩, -⟩` into its components or cases. Take `⟨hee, hec, v, ε, ⟨a, rfl, h1, h2⟩, hs⟩` from `he.1`. Use `⟨v, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hs]`. Conclude with `GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2`.

Rewrite using `[add_mul, hee, mul_comm, hec, add_zero]`. Establish `hi : GlobalTheory.PlaceComp.IsIdemOf D.host.E v f`. Rewrite using `[he]`. Conclude with `GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2`. Conclude with `⟨v, hi, (GlobalTheory.SuppLocal.idem_mul_iff hi f).2 ⟨hi.1, hi.2.2⟩⟩`.
-/
theorem exists_place {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), GlobalTheory.PlaceComp.IsIdemOf D.host.E v f ∧ f * e = e := by
  rcases h with ⟨he, rfl⟩ | ⟨rfl, ⟨v, ε, ⟨a, rfl, h1, h2⟩, he⟩, -⟩
  · obtain ⟨hee, hec, v, ε, ⟨a, rfl, h1, h2⟩, hs⟩ := he.1
    refine ⟨v, ?_, ?_⟩
    · rw [hs]; exact GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2
    · rw [add_mul, hee, mul_comm, hec, add_zero]
  · have hi : GlobalTheory.PlaceComp.IsIdemOf D.host.E v f := by
      rw [he]; exact GlobalTheory.PlaceComp.isIdemOf_algebraMap h1 h2
    exact ⟨v, hi, (GlobalTheory.SuppLocal.idem_mul_iff hi f).2 ⟨hi.1, hi.2.2⟩⟩

/- English proof (translation)
Introduce `D V V' P e f ϖ d α hr hP hα hd`. Take `⟨v, hf, hfe⟩` from `exists_place hP`. Apply the tactic sequence `obtain ⟨φ, ψ, h1, h2, hJ, hL⟩ := GlobalTheory.LocalIsometryEqualRank.exists_local_isometry D V V' hr v`. Take `⟨α', hs, hm, -⟩` from `GlobalTheory.IsomTransport.transport D.host.F D.host.E D.sp.cm V V' v f φ ψ hf h1 h2 hL hJ α hα`. Apply the tactic sequence `exact ⟨α', hs, hd.1.trans hr.symm, GlobalTheory.DivTransport.divG_of_local_isometry D.host.F D.host.E D.sp.cm V V' v f φ ψ hf h1 h2 hL hr e ϖ (fun i => d.getD i.1 0) α α' hfe hm hd.2⟩`.
-/
theorem exists_divAt_of_rank_eq : ∀ {D : D7} (V V' : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : D.host.E) (d : List ℤ) (α : GA D V), V'.rank = V.rank → IsPrimeIdem P e f → SuppF V f α → DivAt V e ϖ d α → ∃ α' : GA D V', SuppF V' f α' ∧ DivAt V' e ϖ d α' := by
  intro D V V' P e f ϖ d α hr hP hα hd
  obtain ⟨v, hf, hfe⟩ := exists_place hP
  obtain ⟨φ, ψ, h1, h2, hJ, hL⟩ := GlobalTheory.LocalIsometryEqualRank.exists_local_isometry D V V' hr v
  obtain ⟨α', hs, hm, -⟩ :=
    GlobalTheory.IsomTransport.transport D.host.F D.host.E D.sp.cm V V' v f φ ψ hf h1 h2 hL hJ α hα
  exact ⟨α', hs, hd.1.trans hr.symm,
    GlobalTheory.DivTransport.divG_of_local_isometry D.host.F D.host.E D.sp.cm V V' v f φ ψ hf h1 h2 hL hr e ϖ
      (fun i => d.getD i.1 0) α α' hfe hm hd.2⟩

end GlobalTheory.DivMove
