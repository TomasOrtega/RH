import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

/- English proof (translation)
Establish `hl : (l : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero`. Establish `hK : (l : K) ≠ 0`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] K)]`. Conclude with `(map_ne_zero (algebraMap ℚ_[l] K)).mpr hl`. Rewrite using `[← map_natCast (algebraMap K L.B)]`.

Conclude with `(IsUnit.mk0 _ hK).map _`.
-/
theorem unit_B_pf {L : Lev R m} (hL : L.Good) : IsUnit ((l : L.B)) := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hK : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero (algebraMap ℚ_[l] K)).mpr hl
  rw [← map_natCast (algebraMap K L.B)]
  exact (IsUnit.mk0 _ hK).map _

end CrystallineSemistableComparison.Pb.Kap
