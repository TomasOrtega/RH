import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

/- English proof (translation)
Introduce `hCol R _ C _ F T hT j z hz s`. Take `⟨hι, hdv, -, hex0, hex⟩` from `hCol R C F T hT`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `k x hx`.

Take `⟨rfl, rfl⟩` from `hx`. Conclude with `⟨(hex0 j _).2 ⟨_, rfl⟩, by rw [hι, hz, map_zero]⟩`. Consider the case `succ s ih`. Introduce `k x hx`. Take `⟨a, rfl, ha⟩` from `hx`.

Establish `h1` using `(ih (k + 1) _ ha).1`. Rewrite `h1` using `[map_zsmul]`. Establish `h2 : T.dvC s (k + 1) (d _ k a) = 0` using `(IsUnit.smul_eq_zero ((isUnit_neg_one (α := ℤ)).pow k)).1 h1`. Conclude with `⟨(hex s k _).2 ⟨a, rfl⟩, by rw [hdv]; exact h2⟩`.
-/
theorem stTop_of_stCol : CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.StTop := by
  intro hCol R _ C _ F T hT j z hz s
  obtain ⟨hι, hdv, -, hex0, hex⟩ := hCol R C F T hT
  induction s with
  | zero =>
    intro k x hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨(hex0 j _).2 ⟨_, rfl⟩, by rw [hι, hz, map_zero]⟩
  | succ s ih =>
    intro k x hx
    obtain ⟨a, rfl, ha⟩ := hx
    have h1 := (ih (k + 1) _ ha).1
    rw [map_zsmul] at h1
    have h2 : T.dvC s (k + 1) (d _ k a) = 0 :=
      (IsUnit.smul_eq_zero ((isUnit_neg_one (α := ℤ)).pow k)).1 h1
    exact ⟨(hex s k _).2 ⟨a, rfl⟩, by rw [hdv]; exact h2⟩

end GlobalTheory.CompanionTheory.EdgeMap
