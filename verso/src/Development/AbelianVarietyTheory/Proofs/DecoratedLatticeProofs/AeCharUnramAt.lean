import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PZeroHyperbolicZeroEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ShapeSecond

variable {D : D7}

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Take `⟨N, hN, hker, -⟩` from `GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ`. Use `filter_upwards [GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (N : D.host.E)⁻¹] with v hv x h1 h2 h3 h4`. Establish `ha : (x : AE D) - 1 ∈ GlobalTheory.FinPl.intAt D (· = v)`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show infPart D ((x : AE D) - 1) = 0`.

Rewrite using `[RingHom.map_sub, h1, RingHom.map_one, sub_self]`. Use `(Submodule.mem_iInf _).2 fun w => ?_ show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (finPart D ((x : AE D) - 1)) = 0` and prove the remaining obligations. Rewrite using `[RingHom.map_sub, RingHom.map_sub, h2 w.1 w.2, RingHom.map_one, RingHom.map_one, sub_self]`. Rewrite using `[RingHom.map_sub, RingHom.map_one]`. Conclude with `sub_mem h3 (GlobalTheory.HeckeConj.one_mem_intAE D)`.

Establish `e : (x : AE D) - 1 = N • (incA D (N : D.host.E)⁻¹ * ((x : AE D) - 1))`. Rewrite using `[nsmul_eq_mul, ← mul_assoc, ← map_natCast (incA D), ← RingHom.map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), RingHom.map_one, one_mul]`. Establish `key : ∃ z ∈ intAE D, finPart D (x : AE D) - 1 = N • z`. Use `⟨_, (hv _ ha).2, ?_⟩` and prove the remaining obligations. Establish `e2 : finPart D ((x : AE D) - 1) = finPart D (x : AE D) - 1` using `by rw [RingHom.map_sub, RingHom.map_one]`.

Rewrite using `[← e2]`. Conclude with `(congrArg (finPart D) e).trans ((finPart D).toAddMonoidHom.map_nsmul _ _)`. Conclude with `hker x ⟨h1, h3, h4⟩ key`.
-/
theorem ae_charUnramAt (χ : (AE D)ˣ →* Circle) (hχ : Continuous χ) :
    ∀ᶠ v : GlobalTheory.FinPl.Pl D in Filter.cofinite, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χ v := by
  obtain ⟨N, hN, hker, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ
  filter_upwards [GlobalTheory.FinPl.AeUnit.eventually_incA_mul_mem_intAt D (N : D.host.E)⁻¹] with v hv x h1 h2 h3 h4
  have ha : (x : AE D) - 1 ∈ GlobalTheory.FinPl.intAt D (· = v) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show infPart D ((x : AE D) - 1) = 0
      rw [RingHom.map_sub, h1, RingHom.map_one, sub_self]
    · refine (Submodule.mem_iInf _).2 fun w => ?_
      show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w.1 (finPart D ((x : AE D) - 1)) = 0
      rw [RingHom.map_sub, RingHom.map_sub, h2 w.1 w.2, RingHom.map_one, RingHom.map_one, sub_self]
    · rw [RingHom.map_sub, RingHom.map_one]
      exact sub_mem h3 (GlobalTheory.HeckeConj.one_mem_intAE D)
  have e : (x : AE D) - 1 = N • (incA D (N : D.host.E)⁻¹ * ((x : AE D) - 1)) := by
    rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (incA D), ← RingHom.map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), RingHom.map_one, one_mul]
  have key : ∃ z ∈ intAE D, finPart D (x : AE D) - 1 = N • z := by
    refine ⟨_, (hv _ ha).2, ?_⟩
    have e2 : finPart D ((x : AE D) - 1) = finPart D (x : AE D) - 1 := by rw [RingHom.map_sub, RingHom.map_one]
    rw [← e2]
    exact (congrArg (finPart D) e).trans ((finPart D).toAddMonoidHom.map_nsmul _ _)
  exact hker x ⟨h1, h3, h4⟩ key

end GlobalTheory.FinPl.ShapeSecond
