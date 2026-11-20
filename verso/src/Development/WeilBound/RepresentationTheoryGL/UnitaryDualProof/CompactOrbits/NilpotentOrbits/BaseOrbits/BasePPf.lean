import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseOrbits.MainE
import GroundTheory.AutomorphicForms.WhittakerDistribution

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Nil

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil.BasePf

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `n Z hZ h0 ξ hS hI`. Establish `: TotallyDisconnectedSpace k` using `totallyDisconnectedSpace_localField`. Establish `: LocallyCompactSpace (Matrix (Fin n) (Fin n) k)` using `inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))`. Establish `: TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k)` using `inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))`. Establish `: T2Space (Matrix (Fin n) (Fin n) k)` using `inferInstanceAs (T2Space (Fin n → Fin n → k))`.

Introduce `f hf`. Establish `hle : supportedIn {p : Sp k n | p.2 ≠ 0} ≤ LinearMap.ker ξ` using `supportedIn_le_of_local fun p hp => by`. Take `⟨e, he, hee, hev, hprim⟩` from `prim Z hZ.1 hZ.2 p.2 hp`. Use `⟨{q : Sp k n | e *ᵥ q.2 ≠ 0}, ?_, hev, fun g hg => LinearMap.mem_ker.2 (mainE Z hZ h0 e he hee hprim p.2 hev ξ hS hI g hg)⟩` and prove the remaining obligations. Conclude with `isOpen_ne_fun (continuous_const.matrix_mulVec continuous_snd) continuous_const`.

Conclude with `LinearMap.mem_ker.1 (hle hf)`.
-/
theorem usage₁₀ [CharZero k] : BaseP (k := k) := by
  intro n Z hZ h0 ξ hS hI
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  have : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  have : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  intro f hf
  have hle : supportedIn {p : Sp k n | p.2 ≠ 0} ≤ LinearMap.ker ξ := supportedIn_le_of_local fun p hp => by
    obtain ⟨e, he, hee, hev, hprim⟩ := prim Z hZ.1 hZ.2 p.2 hp
    refine ⟨{q : Sp k n | e *ᵥ q.2 ≠ 0}, ?_, hev, fun g hg =>
      LinearMap.mem_ker.2 (mainE Z hZ h0 e he hee hprim p.2 hev ξ hS hI g hg)⟩
    exact isOpen_ne_fun (continuous_const.matrix_mulVec continuous_snd) continuous_const
  exact LinearMap.mem_ker.1 (hle hf)

end PositivityTheory.RgUd.T.Nil
