import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.KappaZeroD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OrbEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SemiSemi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.ExistsRho

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L c d m h δ ι P hM`. Use `⟨orbEq O K Δ τ L c d m h δ ι P hM, ?_, ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `finU O K Δ τ L c d m h δ ι P hM`. Use `⟨s, fun y hy => hs y ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Conclude with `hy (by simp [UpperTheory.V.Z.Sym.Glob.one, hn])`. Introduce `y`. Use `QuotientGroup.induction_on y ?_` and prove the remaining obligations. Introduce `y`. Establish `e : MulAction.stabilizer (U3 Δ) (QuotientGroup.mk y : U3 Δ ⧸ KU O Δ) = (KU O Δ).comap (MulAut.conj y⁻¹).toMonoidHom`.

Use extensionality with `g`. Simplify using `[MulAction.mem_stabilizer_iff, QuotientGroup.eq, mul_assoc]`. Prove the components needed by the constructor for the conclusion. Introduce `hg`. Simplify `(KU O Δ).inv_mem hg` using `[mul_assoc]`.

Introduce `hg`. Simplify `(KU O Δ).inv_mem hg` using `[mul_assoc]`. Rewrite using `[e]`. Conclude with `stabU O K Δ τ L c d m h δ ι P hM y`.
-/
theorem UpperTheory.V.Z.Sym.Loc.finUq : UpperTheory.V.Z.Sym.Loc.FinUq := by
  intro O K _ _ _ _ _ Δ τ L c d m h δ ι P hM
  refine ⟨orbEq O K Δ τ L c d m h δ ι P hM, ?_, ?_⟩
  · obtain ⟨s, hs⟩ := finU O K Δ τ L c d m h δ ι P hM
    refine ⟨s, fun y hy => hs y ?_⟩
    by_contra hn
    exact hy (by simp [UpperTheory.V.Z.Sym.Glob.one, hn])
  · intro y
    refine QuotientGroup.induction_on y ?_
    intro y
    have e : MulAction.stabilizer (U3 Δ) (QuotientGroup.mk y : U3 Δ ⧸ KU O Δ)
        = (KU O Δ).comap (MulAut.conj y⁻¹).toMonoidHom := by
      ext g
      simp [MulAction.mem_stabilizer_iff, QuotientGroup.eq, mul_assoc]
      constructor
      · intro hg
        simpa [mul_assoc] using (KU O Δ).inv_mem hg
      · intro hg
        simpa [mul_assoc] using (KU O Δ).inv_mem hg
    rw [e]
    exact stabU O K Δ τ L c d m h δ ι P hM y
