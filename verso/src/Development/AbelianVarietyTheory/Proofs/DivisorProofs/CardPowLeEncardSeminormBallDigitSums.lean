import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr.DigitSums

/- English proof (translation)
Establish `h0` using `hB.zero_mem (r' - r) (by linarith)`. Use `hB.sub_mem r (r' - r) x 0 hx h0` as an intermediate fact. Simplify using `using this`.
-/
theorem mono {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (hB : IsBallFam Λ B) {r r' : ℝ} (h : r ≤ r') {x : G} (hx : x ∈ B r) : x ∈ B r' := by
  have h0 := hB.zero_mem (r' - r) (by linarith)
  have := hB.sub_mem r (r' - r) x 0 hx h0
  simpa using this

end GlobalTheory.VolBr.DigitSums

namespace GlobalTheory.VolBr

end GlobalTheory.VolBr
