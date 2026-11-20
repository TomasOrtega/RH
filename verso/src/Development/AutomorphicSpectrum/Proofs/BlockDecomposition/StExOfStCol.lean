import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

/- English proof (translation)
Introduce `hcol R _ C _ F T hG s`. Take `⟨hι, hdv, hinj, hex0, hex⟩` from `hcol R C F T hG`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `k j hsk x hv hd`.

Establish `hjk : j = k` using `by omega`. Substitute `hjk` using the available equality. Take `⟨z, hz⟩` from `(hex0 j x).1 hv`. Use `⟨z, ?_, ⟨rfl, hz⟩⟩` and prove the remaining obligations. Apply `hinj (j + 1)` to reduce the goal to its premises.

Rewrite using `[← hι, hz, hd, map_zero]`. Consider the case `succ s ih`. Introduce `k j hsk x hv hd`. Take `⟨a, ha⟩` from `(hex s k x).1 hv`. Establish `h1 : T.dvC s (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0`.

Rewrite using `[map_zsmul, ← hdv, ha, hd, smul_zero]`. Establish `h2 : d (T.K s) (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0`. Rewrite using `[map_zsmul, d_d, smul_zero]`. Take `⟨z, hz, hst⟩` from `ih (k + 1) j (by omega) _ h1 h2`. Conclude with `⟨z, hz, ⟨a, ha, hst⟩⟩`.
-/
theorem stEx_of_stCol : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StEx := by
  intro hcol R _ C _ F T hG s
  obtain ⟨hι, hdv, hinj, hex0, hex⟩ := hcol R C F T hG
  induction s with
  | zero =>
    intro k j hsk x hv hd
    have hjk : j = k := by omega
    subst hjk
    obtain ⟨z, hz⟩ := (hex0 j x).1 hv
    refine ⟨z, ?_, ⟨rfl, hz⟩⟩
    apply hinj (j + 1)
    rw [← hι, hz, hd, map_zero]
  | succ s ih =>
    intro k j hsk x hv hd
    obtain ⟨a, ha⟩ := (hex s k x).1 hv
    have h1 : T.dvC s (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0 := by
      rw [map_zsmul, ← hdv, ha, hd, smul_zero]
    have h2 : d (T.K s) (k + 1) ((-1 : ℤ) ^ k • d (T.K s) k a) = 0 := by
      rw [map_zsmul, d_d, smul_zero]
    obtain ⟨z, hz, hst⟩ := ih (k + 1) j (by omega) _ h1 h2
    exact ⟨z, hz, ⟨a, ha, hst⟩⟩

end GlobalTheory.CompanionTheory.EdgeStair
