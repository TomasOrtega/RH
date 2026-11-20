import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Supply the required witnesses or components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Supply the required witnesses or components.
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
