import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.PlanePure

/- English proof (translation)
Introduce `F _ _ _ _ _ _ φ hφ`. Establish `hφ' : φ ∈ GJMatrix.localSchwartzBruhatPi F (ι` using `Fin 2) := hφ`. Use `clear hφ`. Rewrite `hφ'` using `[GJMatrix.localSchwartzBruhatPi_eq_span]`. Proceed by induction on `hφ' using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨⟨N, a⟩, rfl⟩` from `hx`. Use `⟨1, fun _ => GJMatrix.cosetInd (valBall F N) (a 0), fun _ => GJMatrix.cosetInd (valBall F N) (a 1), fun _ => ⟨GJMatrix.cosetInd_valBall_mem N _, GJMatrix.cosetInd_valBall_mem N _⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Simplify using `[GJMatrix.localTensor, pt, Fin.prod_univ_two]`.

Consider the case `zero`. Conclude with `⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩`. Consider the case `add x y _ _ ihx ihy`. Take `⟨n, f, g, hfg, rfl⟩` from `ihx`. Take `⟨m, f', g', hfg', rfl⟩` from `ihy`.

Use `⟨n + m, Fin.append f f', Fin.append g g', ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i => simpa using hfg i`. Consider the case `right i => simpa using hfg' i`.

Rewrite using `[Fin.sum_univ_add]`. Simplify using the standard rewrite rules. Consider the case `smul c x _ ih`. Take `⟨n, f, g, hfg, rfl⟩` from `ih`. Use `⟨n, fun i => c • f i, g, fun i => ⟨Submodule.smul_mem _ c (hfg i).1, (hfg i).2⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Simplify using `[pt, mul_assoc]`.
-/
theorem schwartzBruhat2_eq_sum_pt : Ad3.SchwartzSpaceL2.SPure := by
  intro F _ _ _ _ _ _ φ hφ
  have hφ' : φ ∈ GJMatrix.localSchwartzBruhatPi F (ι := Fin 2) := hφ
  clear hφ
  rw [GJMatrix.localSchwartzBruhatPi_eq_span] at hφ'
  induction hφ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨N, a⟩, rfl⟩ := hx
    refine ⟨1, fun _ => GJMatrix.cosetInd (valBall F N) (a 0),
      fun _ => GJMatrix.cosetInd (valBall F N) (a 1),
      fun _ => ⟨GJMatrix.cosetInd_valBall_mem N _, GJMatrix.cosetInd_valBall_mem N _⟩, ?_⟩
    funext y
    simp [GJMatrix.localTensor, pt, Fin.prod_univ_two]
  | zero =>
    exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, f, g, hfg, rfl⟩ := ihx
    obtain ⟨m, f', g', hfg', rfl⟩ := ihy
    refine ⟨n + m, Fin.append f f', Fin.append g g', ?_, ?_⟩
    · intro i
      induction i using Fin.addCases with
      | left i => simpa using hfg i
      | right i => simpa using hfg' i
    · rw [Fin.sum_univ_add]
      simp
  | smul c x _ ih =>
    obtain ⟨n, f, g, hfg, rfl⟩ := ih
    refine ⟨n, fun i => c • f i, g, fun i => ⟨Submodule.smul_mem _ c (hfg i).1, (hfg i).2⟩, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext y
    simp [pt, mul_assoc]

end GlobalTheory.CompanionTheory.PlanePure
