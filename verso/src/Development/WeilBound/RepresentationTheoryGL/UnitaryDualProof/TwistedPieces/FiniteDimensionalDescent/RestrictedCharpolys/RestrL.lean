import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PfinDim
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PhiEx
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.IsClosedCharpolyEq

namespace PositivityTheory.RgUd.TP.Desc.Restr.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem restrL (hP : PhiEx k) (hQ : PullPieces k) : RestrL k := by
  intro p _ _ n Z hZ
  obtain ⟨c, hc⟩ : ∃ c : ℕ, n ≤ p ^ c := ⟨n, (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le⟩
  obtain ⟨N, Z', φ, e, hd⟩ := hP p c n Z hZ hc
  exact ⟨N, p ^ c, Z', hd.cr, hd.mu, ⟨c, rfl⟩, hd.roots, hd.nil, hQ Z Z' φ e hZ hd⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem restr : Restr k := restrL k (Pphi1.phiEx k (PfinDim.finDim k)) Ppull2.pullPieces

end PositivityTheory.RgUd.TP.Desc.Restr.Final
