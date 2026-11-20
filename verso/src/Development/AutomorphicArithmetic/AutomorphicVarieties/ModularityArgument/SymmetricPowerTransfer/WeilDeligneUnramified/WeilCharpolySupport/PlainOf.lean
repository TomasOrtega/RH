import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnramOfFixedIwahori

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `_ L _ _ n w τ ψ hψ hs hl`. Use `⟨GlobalTheory.RoadU.chars ψ hψ, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.IwahoriSupport.hasSupport_chars τ.irred ψ hψ hs).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)`. Introduce `y hy`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hy`.

Both sides reduce to the same expression. Introduce `y hy z hz h`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 hy`. Take `⟨j, -, rfl⟩` from `Multiset.mem_map.1 hz`. Rewrite `h` using `[IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]`.

Conclude with `hl i j h`.
-/
theorem UpperTheory.V.Z.Sym.W.plainOf :
    UpperTheory.V.Z.Sym.W.PlainOf := by
  intro _ L _ _ n w τ ψ hψ hs hl
  refine ⟨GlobalTheory.RoadU.chars ψ hψ, ?_, ?_, ?_⟩
  · exact (GlobalTheory.IwahoriSupport.hasSupport_chars τ.irred ψ hψ hs).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · intro y hy z hz h
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at h
    exact hl i j h
