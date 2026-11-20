import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.ImgOneGcd

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Introduce `φ H`. Establish `hN0 : H.condN ≠ 0` using `H.condN_ne_zero`. Establish `hN : H.imgOne H.condN = ⊥`. Rewrite using `[H.imgOne_eq_bot_iff dvd_rfl]`. Introduce `u hu`.

Establish `h1 : u = 1` using `by haveI : NeZero H.condN := ⟨hN0⟩`. Apply `Units.ext` to reduce the goal to its premises. Establish `h2` using `(ZMod.natCast_eq_natCast_iff _ _ _).2 hu`. Rewrite `h2` using `[ZMod.natCast_zmod_val, Nat.cast_one]`. Conclude with `h2`.

Rewrite using `[h1, map_one]`. Establish `hmem : H.condE ∣ H.condN ∧ H.imgOne H.condE = ⊥` using `Nat.sInf_mem (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥}) ⟨H.condN, dvd_rfl, hN⟩`. Establish `hpos : 0 < H.condE` using `Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hN0)`. Use `⟨hmem.1, hpos, fun f hf => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `hg : H.imgOne (Nat.gcd H.condE f) = ⊥`.

Rewrite using `[UpperTheory.HF.imgOne_gcd H hmem.1 hf, hmem.2, h, sup_bot_eq]`. Establish `hle : H.condE ≤ Nat.gcd H.condE f` using `Nat.sInf_le (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥}) ⟨(Nat.gcd_dvd_right _ _).trans hf, hg⟩`. Establish `heq : Nat.gcd H.condE f = H.condE` using `le_antisymm (Nat.gcd_le_left _ hpos) hle`. Rewrite using `[← heq]`. Conclude with `Nat.gcd_dvd_right _ _`.

Conclude with `le_bot_iff.1 (hmem.2 ▸ H.imgOne_anti h hf)`.
-/
theorem UpperTheory.HF.condE_spec :
    ∀ {φ : Frame} (H : HostRaw φ), H.condE ∣ H.condN ∧ 0 < H.condE ∧ ∀ f : ℕ, f ∣ H.condN → (H.imgOne f = ⊥ ↔ H.condE ∣ f) := by
  intro φ H
  have hN0 : H.condN ≠ 0 := H.condN_ne_zero
  have hN : H.imgOne H.condN = ⊥ := by
    rw [H.imgOne_eq_bot_iff dvd_rfl]
    intro u hu
    have h1 : u = 1 := by
      haveI : NeZero H.condN := ⟨hN0⟩
      apply Units.ext
      have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 hu
      rw [ZMod.natCast_zmod_val, Nat.cast_one] at h2
      exact h2
    rw [h1, map_one]
  have hmem : H.condE ∣ H.condN ∧ H.imgOne H.condE = ⊥ :=
    Nat.sInf_mem (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥}) ⟨H.condN, dvd_rfl, hN⟩
  have hpos : 0 < H.condE := Nat.pos_of_dvd_of_pos hmem.1 (Nat.pos_of_ne_zero hN0)
  refine ⟨hmem.1, hpos, fun f hf => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hg : H.imgOne (Nat.gcd H.condE f) = ⊥ := by
      rw [UpperTheory.HF.imgOne_gcd H hmem.1 hf, hmem.2, h, sup_bot_eq]
    have hle : H.condE ≤ Nat.gcd H.condE f :=
      Nat.sInf_le (s := {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥})
        ⟨(Nat.gcd_dvd_right _ _).trans hf, hg⟩
    have heq : Nat.gcd H.condE f = H.condE := le_antisymm (Nat.gcd_le_left _ hpos) hle
    rw [← heq]
    exact Nat.gcd_dvd_right _ _
  · exact le_bot_iff.1 (hmem.2 ▸ H.imgOne_anti h hf)
