import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PfinDim
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PhiEx
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.IsClosedCharpolyEq

namespace PositivityTheory.RgUd.TP.Desc.Restr.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `p _ _ n Z hZ`. Take `⟨c, hc⟩ : ∃ c : ℕ, n ≤ p ^ c` from `⟨n, (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le⟩`. Take `⟨N, Z', φ, e, hd⟩` from `hP p c n Z hZ hc`. Conclude with `⟨N, p ^ c, Z', hd.cr, hd.mu, ⟨c, rfl⟩, hd.roots, hd.nil, hQ Z Z' φ e hZ hd⟩`.
-/
theorem restrL (hP : PhiEx k) (hQ : PullPieces k) : RestrL k := by
  intro p _ _ n Z hZ
  obtain ⟨c, hc⟩ : ∃ c : ℕ, n ≤ p ^ c := ⟨n, (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le⟩
  obtain ⟨N, Z', φ, e, hd⟩ := hP p c n Z hZ hc
  exact ⟨N, p ^ c, Z', hd.cr, hd.mu, ⟨c, rfl⟩, hd.roots, hd.nil, hQ Z Z' φ e hZ hd⟩

/- English proof (translation)
The claim follows from `restrL k (Pphi1.phiEx k (PfinDim.finDim k)) Ppull2.pullPieces`.
-/
theorem restr : Restr k := restrL k (Pphi1.phiEx k (PfinDim.finDim k)) Ppull2.pullPieces

end PositivityTheory.RgUd.TP.Desc.Restr.Final
