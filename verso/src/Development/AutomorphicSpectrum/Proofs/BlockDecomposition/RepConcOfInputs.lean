import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

/- English proof (translation)
Introduce `hEv hSch hRep R _ I X n a`. Establish `hS` using `hSch R X I (n - 1) n (n + 1) (by ring) rfl`. Establish `hR` using `hRep R I X n`. Establish `hconc : Sec.map (I.d n (n + 1)) a = 0 → ∃ α : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.IsConc α.1 a`. Introduce `ha`.

Take `⟨α, h0, h1⟩` from `hS.1 a ha`. Use `⟨α, ?_⟩` and prove the remaining obligations. Unfold `CrystallineSemistableComparison.E.IsConc`. Conclude with `⟨h0, h1⟩`. Establish `huniq : ∀ x y : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.Rep x a → CrystallineSemistableComparison.E.Rep y a → x = y`.

Introduce `x y hx hy`. Establish `hxy : CrystallineSemistableComparison.E.Rep (x - y) (a - a)` using `(hR.2.2.1 x y a a hx hy).2`. Rewrite `hxy` using `[sub_self]`. Take `⟨γ, hγ, hγa⟩` from `hxy`. Establish `h00 : CrystallineSemistableComparison.E.Rep (0 : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n) 0`.

Establish `h` using `(hR.2.2.1 x x a a hx hx).2`. Rewrite `h` using `[sub_self, sub_self]`. Then use the resulting hypothesis. Take `⟨b, hb⟩` from `hR.2.2.2.1 0 h00 (n - 1) (by ring)`. Establish `hγ0 : CochainComplex.HomComplex.CohomologyClass.mk γ = 0` using `((hS.2 γ).2).2 ⟨b, by rw [hb, hγa]⟩`. Rewrite using `[← sub_eq_zero, ← hγ, hγ0]`.

Use `⟨hconc, fun x hx => ?_, huniq⟩` and prove the remaining obligations. Establish `hx'` using `hx`. Take `⟨β, hβ, hβa⟩` from `hx'`. Establish `ha : Sec.map (I.d n (n + 1)) a = 0`. Establish `h` using `(hS.2 β).1`.

Rewrite `h` using `[hβa]`. Then use the resulting hypothesis. Take `⟨α, hα⟩` from `hconc ha`. Establish `hα'` using `hα`. Unfold `CrystallineSemistableComparison.E.IsConc at hα'`. Take `⟨hα1, -⟩` from `hα'`.

Establish `hRα : CrystallineSemistableComparison.E.Rep (CochainComplex.HomComplex.CohomologyClass.mk α) a`. Unfold `CrystallineSemistableComparison.E.Rep`. Use `⟨α, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[hα1 X (𝟙 X)]`. Simplify using `[GlobalTheory.EtC.Sec.res]`.

Conclude with `⟨α, hα, huniq _ _ hRα hx⟩`.
-/
theorem repConc_of_inputs : CrystallineSemistableComparison.E.EvExt → CrystallineSemistableComparison.E.InSch → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepConc := by
  intro hEv hSch hRep R _ I X n a
  have hS := hSch R X I (n - 1) n (n + 1) (by ring) rfl
  have hR := hRep R I X n
  have hconc : Sec.map (I.d n (n + 1)) a = 0 →
      ∃ α : CochainComplex.HomComplex.Cocycle ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.IsConc α.1 a := by
    intro ha
    obtain ⟨α, h0, h1⟩ := hS.1 a ha
    refine ⟨α, ?_⟩
    unfold CrystallineSemistableComparison.E.IsConc
    exact ⟨h0, h1⟩
  have huniq : ∀ x y : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n, CrystallineSemistableComparison.E.Rep x a → CrystallineSemistableComparison.E.Rep y a → x = y := by
    intro x y hx hy
    have hxy : CrystallineSemistableComparison.E.Rep (x - y) (a - a) := (hR.2.2.1 x y a a hx hy).2
    rw [sub_self] at hxy
    obtain ⟨γ, hγ, hγa⟩ := hxy
    have h00 : CrystallineSemistableComparison.E.Rep (0 : CochainComplex.HomComplex.CohomologyClass ((chains R).obj (sch.obj X)) I n) 0 := by
      have h := (hR.2.2.1 x x a a hx hx).2
      rwa [sub_self, sub_self] at h
    obtain ⟨b, hb⟩ := hR.2.2.2.1 0 h00 (n - 1) (by ring)
    have hγ0 : CochainComplex.HomComplex.CohomologyClass.mk γ = 0 := ((hS.2 γ).2).2 ⟨b, by rw [hb, hγa]⟩
    rw [← sub_eq_zero, ← hγ, hγ0]
  refine ⟨hconc, fun x hx => ?_, huniq⟩
  have hx' := hx
  obtain ⟨β, hβ, hβa⟩ := hx'
  have ha : Sec.map (I.d n (n + 1)) a = 0 := by
    have h := (hS.2 β).1
    rwa [hβa] at h
  obtain ⟨α, hα⟩ := hconc ha
  have hα' := hα
  unfold CrystallineSemistableComparison.E.IsConc at hα'
  obtain ⟨hα1, -⟩ := hα'
  have hRα : CrystallineSemistableComparison.E.Rep (CochainComplex.HomComplex.CohomologyClass.mk α) a := by
    unfold CrystallineSemistableComparison.E.Rep
    refine ⟨α, rfl, ?_⟩
    rw [hα1 X (𝟙 X)]
    simp [GlobalTheory.EtC.Sec.res]
  exact ⟨α, hα, huniq _ _ hRα hx⟩

end GlobalTheory.CompanionTheory.EdgeMap
