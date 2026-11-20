import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Introduce `φ H`. Prove the components needed by the constructor for the conclusion. Introduce `θ θ' h`. Apply `MonoidHom.ext` to reduce the goal to its premises. Introduce `g`.

Take `⟨u, rfl⟩` from `HostDer.art_surj H.der g`. Establish `h1` using `(H.toHostRaw.isPrimOf_prim θ).2`. Establish `h2` using `(H.toHostRaw.isPrimOf_prim θ').2`. Rewrite `h2` using `[← h]`. Establish `hc` using `ZMod.val_coe_unit_coprime u`.

Establish `e` using `(h1 _ hc).symm.trans (h2 _ hc)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[← HostRaw.dir_unit, ← HostRaw.dir_unit]`. Simplify `e` using `[HostRaw.dirAt, ZMod.natCast_zmod_val]`. Establish `hd : H.toHostRaw.dir 1 = 1`.

Apply `MulChar.ext` to reduce the goal to its premises. Introduce `u`. Rewrite using `[HostRaw.dir_unit]`. Simplify using the standard rewrite rules. Rewrite using `[HostRaw.prim, hd, PChar.of_one]`.
-/
theorem UpperTheory.Comparison₂.prim_inj :
    ∀ (φ : Frame) (H : HostAx φ), Function.Injective H.toHostRaw.prim ∧ H.toHostRaw.prim 1 = PChar.one := by
  intro φ H
  constructor
  · intro θ θ' h
    apply MonoidHom.ext
    intro g
    obtain ⟨u, rfl⟩ := HostDer.art_surj H.der g
    have h1 := (H.toHostRaw.isPrimOf_prim θ).2
    have h2 := (H.toHostRaw.isPrimOf_prim θ').2
    rw [← h] at h2
    have hc := ZMod.val_coe_unit_coprime u
    have e := (h1 _ hc).symm.trans (h2 _ hc)
    apply Units.ext
    rw [← HostRaw.dir_unit, ← HostRaw.dir_unit]
    simpa [HostRaw.dirAt, ZMod.natCast_zmod_val] using e
  · have hd : H.toHostRaw.dir 1 = 1 := by
      apply MulChar.ext
      intro u
      rw [HostRaw.dir_unit]
      simp
    rw [HostRaw.prim, hd, PChar.of_one]
