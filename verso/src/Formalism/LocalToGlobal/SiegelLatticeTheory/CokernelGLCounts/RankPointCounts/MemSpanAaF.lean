import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AaF
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (Z : LocDat D) (p : PlF D)

/- English proof (translation)
Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨x, hx, rfl⟩` from `hy`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨x * N, hN x hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, mul_comm]`. Consider the case `zero => rw [mul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [mul_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul o y _ hy`. Establish `e : (D.s.atP p).ιE N * (o • y) = o • ((D.s.atP p).ιE N * y)` using `by show _ * ((o : (D.s.atP p).Ep) * y) = (o : (D.s.atP p).Ep) * (_ * y)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem mem_span_aaF {N : D.host.E} {c b : Fin (D.R.rS + 1)} (hN : ∀ x ∈ aaF D b, x * N ∈ aaF D c)
    {y : (D.s.atP p).Ep}
    (hy : y ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D b : FractionalIdeal _ _) : Set D.host.E))) :
    (D.s.atP p).ιE N * y ∈
      Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D c : FractionalIdeal _ _) : Set D.host.E)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨x * N, hN x hx, ?_⟩
    rw [map_mul, mul_comm]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul o y _ hy =>
    have e : (D.s.atP p).ιE N * (o • y) = o • ((D.s.atP p).ιE N * y) := by
      show _ * ((o : (D.s.atP p).Ep) * y) = (o : (D.s.atP p).Ep) * (_ * y)
      ring
    rw [e]
    exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Establish `hD` using `Formalism.L2.SG.Pf.locDiffC_holds D Z`. Establish `hb : frFac Z.δ p b ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D b : FractionalIdeal _ _) : Set D.host.E))`. Rewrite using `[hD p b]`. Conclude with `Submodule.subset_span rfl`. Establish `h` using `mem_span_aaF Z p hN hb`.

Rewrite `h` using `[hD p c, Submodule.mem_span_singleton]`. Take `⟨o, ho⟩` from `h`. Use `⟨o, o.2, ?_⟩` and prove the remaining obligations. Rewrite using `[← ho]`. Use `show (o : (D.s.atP p).Ep) * frFac Z.δ p c = frFac Z.δ p c * o`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem loc_int {N : D.host.E} {c b : Fin (D.R.rS + 1)} (hN : ∀ x ∈ aaF D b, x * N ∈ aaF D c) :
    ∃ o ∈ (Z.M p).L.O, (D.s.atP p).ιE N * frFac Z.δ p b = frFac Z.δ p c * o := by
  have hD := Formalism.L2.SG.Pf.locDiffC_holds D Z
  have hb : frFac Z.δ p b ∈
      Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D b : FractionalIdeal _ _) : Set D.host.E)) := by
    rw [hD p b]
    exact Submodule.subset_span rfl
  have h := mem_span_aaF Z p hN hb
  rw [hD p c, Submodule.mem_span_singleton] at h
  obtain ⟨o, ho⟩ := h
  refine ⟨o, o.2, ?_⟩
  rw [← ho]
  show (o : (D.s.atP p).Ep) * frFac Z.δ p c = frFac Z.δ p c * o
  ring

def locU (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * N.map (D.s.atP p).ιE *
    Matrix.diagonal (frFac Z.δ p)

/- English proof (translation)
Simplify using `[locU, Matrix.mul_diagonal, Matrix.diagonal_mul]`.
-/
theorem locU_apply (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (c b : Fin (D.R.rS + 1)) :
    locU Z p N c b = Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (N c b) * frFac Z.δ p b := by
  simp [locU, Matrix.mul_diagonal, Matrix.diagonal_mul]

/- English proof (translation)
Establish `hu : ∀ a, Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1` using `fun a => Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)`. Use `⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[locU_apply, hd, map_one, mul_one, hu]`. Rewrite using `[locU_apply, hU a b h, map_zero, mul_zero, zero_mul]`. Break down `lt_trichotomy a b with h | h | h` into its components or cases.

Take `⟨o, ho, he⟩` from `loc_int Z p (hN a b h)`. Rewrite using `[locU_apply, mul_assoc, he, ← mul_assoc, hu, one_mul]`. Conclude with `ho`. Substitute `h` using the available equality. Rewrite using `[locU_apply, hd, map_one, mul_one, hu]`.

Conclude with `Subring.one_mem _`. Rewrite using `[locU_apply, hU a b h, map_zero, mul_zero, zero_mul]`. Conclude with `Subring.zero_mem _`.
-/
theorem locU_int (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hU : ∀ a b, b < a → N a b = 0) (hd : ∀ a, N a a = 1)
    (hN : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c) :
    (∀ a, locU Z p N a a = 1) ∧ (∀ a b, b < a → locU Z p N a b = 0) ∧ ∀ a b, locU Z p N a b ∈ (Z.M p).L.O := by
  have hu : ∀ a, Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1 := fun a =>
    Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)
  refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
  · rw [locU_apply, hd, map_one, mul_one, hu]
  · rw [locU_apply, hU a b h, map_zero, mul_zero, zero_mul]
  · rcases lt_trichotomy a b with h | h | h
    · obtain ⟨o, ho, he⟩ := loc_int Z p (hN a b h)
      rw [locU_apply, mul_assoc, he, ← mul_assoc, hu, one_mul]
      exact ho
    · subst h
      rw [locU_apply, hd, map_one, mul_one, hu]
      exact Subring.one_mem _
    · rw [locU_apply, hU a b h, map_zero, mul_zero, zero_mul]
      exact Subring.zero_mem _

end Loc

end Formalism.L2.SG.Pf.FibQ
