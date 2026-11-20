import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

/- English proof (translation)
Introduce `φ H p hc hp`. Establish `hN : H.condN ≠ 0` using `(Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos).ne'`. Establish `hnd : ¬ p ∣ H.condN` using `fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc h)`. Take `⟨hloc, hfrob⟩` from `Formalism.LFunctionChainParameters.LHost.unramified_spec H.condN p hN hp hnd`. Prove the components needed by the constructor for the conclusion.

Use `show Subgroup.toAddSubgroup' (Subgroup.map (recH H) (Formalism.LFunctionChainParameters.LHost.localUnits H.condN p)) = ⊥`. Rewrite using `[hloc, Subgroup.map_bot]`. Conclude with `Subgroup.toAddSubgroup'.map_bot`. Use `show (recH H (Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p)).toAdd = _`. Establish `he : Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p = ZMod.unitOfCoprime p hc` using `Units.ext (by rw [hfrob, ZMod.coe_unitOfCoprime])`.

Rewrite using `[he]`.
-/
theorem UpperTheory.GL.unram :
    ∀ {φ : Frame} (H : HostRaw φ) (p : ℕ) (hc : p.Coprime H.condN), p.Prime →
      (arith H).inertia p = ⊥ ∧ (arith H).frob p = (recH H (ZMod.unitOfCoprime p hc)).toAdd := by
  intro φ H p hc hp
  have hN : H.condN ≠ 0 := (Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos).ne'
  have hnd : ¬ p ∣ H.condN := fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc h)
  obtain ⟨hloc, hfrob⟩ := Formalism.LFunctionChainParameters.LHost.unramified_spec H.condN p hN hp hnd
  constructor
  · show Subgroup.toAddSubgroup' (Subgroup.map (recH H) (Formalism.LFunctionChainParameters.LHost.localUnits H.condN p)) = ⊥
    rw [hloc, Subgroup.map_bot]
    exact Subgroup.toAddSubgroup'.map_bot
  · show (recH H (Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p)).toAdd = _
    have he : Formalism.LFunctionChainParameters.LHost.frobUnit H.condN p = ZMod.unitOfCoprime p hc :=
      Units.ext (by rw [hfrob, ZMod.coe_unitOfCoprime])
    rw [he]
