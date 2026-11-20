import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalModelRegularUnitValuesStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

/- English proof (translation)
Introduce `k _ X Y _ _ p q π hπ φ hM B J f w hs`. Take `⟨β, hβ, hreg, hnorm⟩` from `hs`. Take `⟨hR, -, hF, hV⟩` from `GlobalTheory.T.birationalModel_regular_unit_values k X Y p q π hπ φ hM`. Use `⟨fun c => Units.map φ.toMonoidHom (β (c PUnit.unit)), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j h`.

Establish `hi : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (i PUnit.unit)` using `LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit h.1`. Establish `hj : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (j PUnit.unit)` using `LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit h.2`. Establish `hX : genericPoint X ∈ B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit)`. Rewrite using `[← hM.gen]`. Conclude with `⟨hi, hj⟩`.

Establish `eg : ((B.B.pull π).g i j).val = resG Y (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) (π.app _ (B.B.g (i P …` using `by dsimp only [LB.pull, LB.LinComb]`. Simplify using `only [Fintype.prod_unique, zpow_one, LB.val_res, pullU, Units.coe_map]`. Both sides reduce to the same expression. Use `show φ (β (i PUnit.unit)) = fnOf _ h ((B.B.pull π).g i j).val * φ (β (j PUnit.unit))`. Rewrite using `[hβ (i PUnit.unit) (j PUnit.unit) hX, map_mul, hF _ hX ⟨hi, hj⟩, eg]`.

Conclude with `congrArg (· * φ (β (j PUnit.unit))) (fnOf_resG (X := Y) (U := π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j …`. Introduce `y c hy j show RegAt y (φ (f j) * φ (β (c PUnit.unit)))`. Rewrite using `[← map_mul]`. Conclude with `hR y _ (hreg (π y) (c PUnit.unit) (LB.wchart_le B.B (fun _ : PUnit => π) c PUnit.unit hy) j)`. Introduce `σ z c hz j`.

Establish `hm` using `mem_of_mem_linComb (m := fun _ => GlobalTheory.Points.PtsOver.map π hπ _ z) (fun _ => rfl) hz PUnit.unit`. Establish `hr` using `hreg (π (under z)) (c PUnit.unit) (mem_ptsIn.1 hm) j`. Establish `e2 : ((B.φ σ).pull π hπ).φ c z = (B.φ σ).φ (c PUnit.unit) (GlobalTheory.Points.PtsOver.map π hπ _ z)` using `(B.φ σ).pull_φ π hπ c z`. Use `show ‖ratVal (φ (f j) * φ (β (c PUnit.unit))) z‖ * Real.exp (-((B.φ σ).pull π hπ).φ c z / 2) ≤ _`. Rewrite using `[← map_mul, hV σ z _ hr, e2]`.

Conclude with `hnorm σ _ (c PUnit.unit) hm j`.
-/
theorem smallFam_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  intro k _ X Y _ _ p q π hπ φ hM B J f w hs
  obtain ⟨β, hβ, hreg, hnorm⟩ := hs
  obtain ⟨hR, -, hF, hV⟩ := GlobalTheory.T.birationalModel_regular_unit_values k X Y p q π hπ φ hM
  refine ⟨fun c => Units.map φ.toMonoidHom (β (c PUnit.unit)), ?_, ?_, ?_⟩
  · intro i j h
    have hi : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (i PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit h.1
    have hj : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (j PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit h.2
    have hX : genericPoint X ∈ B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit) := by
      rw [← hM.gen]; exact ⟨hi, hj⟩
    have eg : ((B.B.pull π).g i j).val = resG Y (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit)))
        (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val) := by
      dsimp only [LB.pull, LB.LinComb]
      simp only [Fintype.prod_unique, zpow_one, LB.val_res, pullU, Units.coe_map]
      rfl
    show φ (β (i PUnit.unit)) = fnOf _ h ((B.B.pull π).g i j).val * φ (β (j PUnit.unit))
    rw [hβ (i PUnit.unit) (j PUnit.unit) hX, map_mul, hF _ hX ⟨hi, hj⟩, eg]
    exact congrArg (· * φ (β (j PUnit.unit))) (fnOf_resG (X := Y) (U := π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) h (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val)).symm
  · intro y c hy j
    show RegAt y (φ (f j) * φ (β (c PUnit.unit)))
    rw [← map_mul]
    exact hR y _ (hreg (π y) (c PUnit.unit) (LB.wchart_le B.B (fun _ : PUnit => π) c PUnit.unit hy) j)
  · intro σ z c hz j
    have hm := mem_of_mem_linComb (m := fun _ => GlobalTheory.Points.PtsOver.map π hπ _ z) (fun _ => rfl) hz
      PUnit.unit
    have hr := hreg (π (under z)) (c PUnit.unit) (mem_ptsIn.1 hm) j
    have e2 : ((B.φ σ).pull π hπ).φ c z = (B.φ σ).φ (c PUnit.unit) (GlobalTheory.Points.PtsOver.map π hπ _ z) :=
      (B.φ σ).pull_φ π hπ c z
    show ‖ratVal (φ (f j) * φ (β (c PUnit.unit))) z‖ * Real.exp (-((B.φ σ).pull π hπ).φ c z / 2) ≤ _
    rw [← map_mul, hV σ z _ hr, e2]
    exact hnorm σ _ (c PUnit.unit) hm j

end GlobalTheory.HSNef
