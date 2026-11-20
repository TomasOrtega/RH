import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwInputs.Move GlobalTheory.HeightCounting.SideCopy
open Formalism.L2.DIV Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.SideCopy.LamCopy
open GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

/- English proof (translation)
Introduce and unpack `D D' ι e h cf cf' ⟨f1, f2, f3, f4⟩ ⟨⟨C, q, w0, c, chi⟩, hOk, hT, rfl, hq, hF⟩`. Establish `he : ∀ x : ↥D'.LL0, D'.what₂.embLL (x : D'.what₂.LL) = D.what₂.embLL (e x : D.what₂.LL)` using `fun x => (h.cp.embLL0_eq x).symm`. Use `copy_cases h D D'`. Use `rename Rows.Data _ => r1`. Consider the cases of `r1`.

Use `rename Rows.Data _ => r2`. Consider the cases of `r2`. Simplify using `only at hTau`. Substitute `hTau` using the available equality. Simplify using `only at heTau hhc`.

Substitute `heTau` using the available equality. Substitute `hhc` using the available equality. Consider the cases of `C`. Consider the cases of `cf'`. Simplify using `only at f1 f2 f3 f4`.

Substitute `f1` using the available equality. Substitute `f2` using the available equality. Substitute `f3` using the available equality. Substitute `f4` using the available equality. Use `⟨⟨_, q, w0, c, chi⟩, ⟨(by with_unfolding_all exact (hOk.places :)), (by with_unfolding_all exact (hOk.aux :)), (by with_unfolding_all exact (hOk.big :))⟩, (by with_unfolding_all exact (hT :)), rfl, (by with_unfolding_all exact (hq :)), fun i hi => ?_⟩` and prove the remaining obligations.

Take `⟨t0, j, t1, t2⟩` from `hF i ((hinW1 i i HEq.rfl).2 hi)`. Use `⟨(by with_unfolding_all exact (t0 :)), (by with_unfolding_all exact (j :)), fun x => ?_, (by with_unfolding_all exact (t2 :))⟩` and prove the remaining obligations. Conclude with `(congrArg j (he x)).trans ((t1 (e x)).trans ((by with_unfolding_all exact ((congrArg (GlobalTheory.ToricDenom.toBar _ i) (eq_of_heq (hemb0 i i HEq.rfl x))) :))))`.
-/
theorem lam_copy : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyAll D D' ι e → ∀ {cf : CharFrame D} {cf' : CharFrame D'}, SameFrame cf cf' → (∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) → ∃ Z : GlobalTheory.LamTie.LamDat D', Z.Ok ∧ Z.Teich ∧ Z.C = cf' ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D' ∧ GlobalTheory.LamTie.IsLamTieFull D'.ntw Z := by
  rintro D D' ι e h cf cf' ⟨f1, f2, f3, f4⟩ ⟨⟨C, q, w0, c, chi⟩, hOk, hT, rfl, hq, hF⟩
  have he : ∀ x : ↥D'.LL0, D'.what₂.embLL (x : D'.what₂.LL) = D.what₂.embLL (e x : D.what₂.LL) := fun x => (h.cp.embLL0_eq x).symm
  copy_cases h D D'
  rename Rows.Data _ => r1; cases r1; rename Rows.Data _ => r2; cases r2
  dsimp only at hTau
  subst hTau
  dsimp only at heTau hhc
  subst heTau; subst hhc
  cases C; cases cf'
  dsimp only at f1 f2 f3 f4
  subst f1; subst f2; subst f3; subst f4
  refine ⟨⟨_, q, w0, c, chi⟩, ⟨(by with_unfolding_all exact (hOk.places :)), (by with_unfolding_all exact (hOk.aux :)), (by with_unfolding_all exact (hOk.big :))⟩, (by with_unfolding_all exact (hT :)), rfl, (by with_unfolding_all exact (hq :)), fun i hi => ?_⟩
  obtain ⟨t0, j, t1, t2⟩ := hF i ((hinW1 i i HEq.rfl).2 hi)
  refine ⟨(by with_unfolding_all exact (t0 :)), (by with_unfolding_all exact (j :)), fun x => ?_, (by with_unfolding_all exact (t2 :))⟩
  exact (congrArg j (he x)).trans ((t1 (e x)).trans ((by with_unfolding_all exact ((congrArg (GlobalTheory.ToricDenom.toBar _ i) (eq_of_heq (hemb0 i i HEq.rfl x))) :))))

end GlobalTheory.HeightCounting.SideCopy.LamCopy
