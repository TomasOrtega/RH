import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.LevExt

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove

/- English proof (translation)
Break down `B' with ⟨P'⟩` into its components or cases. Express the relevant statement in the definitionally equal form `P' = B.toPre at hP`. Substitute `hP` using the available equality. Use the proof step `( (`. Establish `e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f')` using `(by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))`.

Use `clear (hf)`. Substitute `e))` using the available equality. Conclude with `(by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).delAt l)) :))`.
-/
theorem frat_delAt_heq {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'} (hP : B'.toPre = B.toPre)
    {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) (l : ℕ) :
    HEq ((Top.Fr.at a'.st f').delAt l) ((Top.Fr.at a.st f).delAt l) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).delAt l)) :))

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Introduce `K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'`. Establish `hP : B'.toPre = B.toPre` using `l.enl.1`. Establish `hC : x.m.z.R.toLevCh.C = Top.Fr.at (w.st x.o.Z) f` using `x.m.z.lev.C.trans (by rw [w.C_eq])`. Establish `hC' : x'.m.z.R.toLevCh.C = Top.Fr.at (w'.st x'.o.Z) f'` using `x'.m.z.lev.C.trans (by rw [w'.C_eq])`. Establish `hs` using `x.m.z.lev.is`.

Establish `hs'` using `x'.m.z.lev.is`. Establish `hm : (Dof x').R.m = (Dof x).R.m`. Conclude with `congrArg (fun p : Pre => p.R.m) hP`. Establish `hmu0 : ∀ (i : Fin (Dof x).R.m) (i' : Fin (Dof x').R.m), (i : ℕ) = i' → HEq (x'.m.z.R.toLevCh.C.mu0 i') (x.m.z.R.toLevCh.C.mu0 i)`. Introduce `i i' h`.

Rewrite using `[hC, hC']`. Conclude with `hermitianCodeCharFrame_referenceCharacter_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr h`. Use `⟨?_, fun j => ?_, fun j j' h => ?_, fun l0 => ?_⟩` and prove the remaining obligations. Establish `heta : HEq x'.m.z.R.toLevCh.C.eta x.m.z.R.toLevCh.C.eta`. Rewrite using `[hC, hC']`.

Conclude with `frat_eta_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr`. Conclude with `(idc_heq (a := x.o.Z) (a' := x'.o.Z) hP heta hs.eta hs'.eta).symm`. Set `j' : Fin (Dof x').R.m` to `⟨j, lt_of_lt_of_eq j.2 hm.symm⟩`. Conclude with `(idc_heq (a := x.o.Z) (a' := x'.o.Z) hP (hmu0 j j' rfl) (hs.mu0 j) (hs'.mu0 j')).symm`. Conclude with `(hmu0 j j' h).symm`.

Use `show HEq (x.m.z.R.toLevCh.C.delAt l0) (x'.m.z.R.toLevCh.C.delAt l0)`. Rewrite using `[hC, hC']`. Conclude with `(frat_delAt_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr l0).symm`.
-/
theorem chars_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), Chars (sideAt x g hg a) (sideAt x' g' hg' a') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hP : B'.toPre = B.toPre := l.enl.1
  have hC : x.m.z.R.toLevCh.C = Top.Fr.at (w.st x.o.Z) f := x.m.z.lev.C.trans (by rw [w.C_eq])
  have hC' : x'.m.z.R.toLevCh.C = Top.Fr.at (w'.st x'.o.Z) f' := x'.m.z.lev.C.trans (by rw [w'.C_eq])
  have hs := x.m.z.lev.is
  have hs' := x'.m.z.lev.is
  have hm : (Dof x').R.m = (Dof x).R.m := by
    exact congrArg (fun p : Pre => p.R.m) hP
  have hmu0 : ∀ (i : Fin (Dof x).R.m) (i' : Fin (Dof x').R.m), (i : ℕ) = i' →
      HEq (x'.m.z.R.toLevCh.C.mu0 i') (x.m.z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr h
  refine ⟨?_, fun j => ?_, fun j j' h => ?_, fun l0 => ?_⟩
  · have heta : HEq x'.m.z.R.toLevCh.C.eta x.m.z.R.toLevCh.C.eta := by
      rw [hC, hC']
      exact frat_eta_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP heta hs.eta hs'.eta).symm
  · let j' : Fin (Dof x').R.m := ⟨j, lt_of_lt_of_eq j.2 hm.symm⟩
    exact (idc_heq (a := x.o.Z) (a' := x'.o.Z) hP (hmu0 j j' rfl) (hs.mu0 j) (hs'.mu0 j')).symm
  · exact (hmu0 j j' h).symm
  · show HEq (x.m.z.R.toLevCh.C.delAt l0) (x'.m.z.R.toLevCh.C.delAt l0)
    rw [hC, hC']
    exact (frat_delAt_heq (a := x.o.Z) (a' := x'.o.Z) hP l.fr l0).symm

end GlobalTheory.HeightCounting.SerMove

end
