import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTwOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsPbSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsZwSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
open scoped ContDiff Topology in
/- English proof (translation)
Introduce `E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k B hB`. Take `⟨hfl, hflow⟩` from `fieldFlow E a ho U Ξ Y C hS.fld W hW`. Take `⟨c₁, hc₁⟩` from `Cs.zwSz E a U Y C hS.fld W hW (k + 1)`. Take `⟨C₁, hC₁, hpb⟩` from `Cs.pbSz (HV E a) (Fin Ξ.d → ℂ) q k c₁`. Take `⟨D₁, hD₁, hmv⟩` from `Cs.move E a ho U Ξ q k C`.

Take `⟨B₁, hB₁⟩` from `hl.bdd C`. Use `⟨C₁ * D₁ * Real.exp (B * B₁), by positivity, fun A M hA hM w hw g x hg => ?_⟩` and prove the remaining obligations. Take `⟨hF, hfe, hops⟩` from `Cs.twOps E a ho U Ξ W hfl g x`. Take `⟨hsm, hpe⟩` from `(hops q).1 w`. Take `⟨h, hh, hb⟩` from `hS.root (Cs.pt g x) 1 (by simp)`.

Establish `hone : hOne E a ∈ cone E a` using `hOne_mem_cone`. Establish `hpt : flow (Cs.Zw U W g x) 1 (hOne E a) = sand h (hOne E a)`. Rewrite using `[hfe, hflow g h x 1 hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]`. Establish `hup : f (Cs.pt g x) + c ≤ f (Cs.pt (g * h) x)`. Rewrite using `[Cs.pt_mul]`.

Conclude with `hS.up _ h hg (by rw [hh, one_smul])`. Establish `hlam : |lam (Cs.pt (g * h) x)| ≤ |lam (Cs.pt g x)| + B₁`. Rewrite using `[Cs.pt_mul, hl.add]`. Conclude with `(abs_add_le _ _).trans (add_le_add le_rfl (hB₁ h hb))`. Establish `h1` using `hmv w g x h _ hb (hw (g * h) x (by linarith [hS.c_pos]))`.

Rewrite `h1` using `[← hpt]`. Establish `hmem : flow (Cs.Zw U W g x) 1 (hOne E a) ∈ cone E a` using `hF.2 _ hone 1 ⟨zero_le_one, le_rfl⟩`. Establish `h2` using `hpb (Cs.Zw U W g x) 1 (Cs.Tw U Ξ w.1 g x) (hOne E a) _ (by simp) (hF.1.contDiffAt (ho.mem_nhds hone)) (hc₁ g x) (hsm.contDiffAt (ho.mem_nhds hmem)) h1`. Use `(h2.congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hone) fun p hp => (hpe p hp).symm)).mono ?_` and prove the remaining obligations. Establish `he : Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) ≤ Real.exp (B * B₁) * Real.exp (-(A * c)) * Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x))`.

Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Use `Real.exp_le_exp.2 ?_` and prove the remaining obligations. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hlam hB, mul_le_mul_of_nonneg_left hup hA]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Lit.Geo.Cs.decP :
    UpperTheory.V.Lit.Geo.Cs.DecP := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k B hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨c₁, hc₁⟩ := Cs.zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hpb⟩ := Cs.pbSz (HV E a) (Fin Ξ.d → ℂ) q k c₁
  obtain ⟨D₁, hD₁, hmv⟩ := Cs.move E a ho U Ξ q k C
  obtain ⟨B₁, hB₁⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * B₁), by positivity, fun A M hA hM w hw g x hg => ?_⟩
  obtain ⟨hF, hfe, hops⟩ := Cs.twOps E a ho U Ξ W hfl g x
  obtain ⟨hsm, hpe⟩ := (hops q).1 w
  obtain ⟨h, hh, hb⟩ := hS.root (Cs.pt g x) 1 (by simp)
  have hone : hOne E a ∈ cone E a := hOne_mem_cone
  have hpt : flow (Cs.Zw U W g x) 1 (hOne E a) = sand h (hOne E a) := by
    rw [hfe, hflow g h x 1 hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
  have hup : f (Cs.pt g x) + c ≤ f (Cs.pt (g * h) x) := by
    rw [Cs.pt_mul]
    exact hS.up _ h hg (by rw [hh, one_smul])
  have hlam : |lam (Cs.pt (g * h) x)| ≤ |lam (Cs.pt g x)| + B₁ := by
    rw [Cs.pt_mul, hl.add]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hB₁ h hb))
  have h1 := hmv w g x h _ hb (hw (g * h) x (by linarith [hS.c_pos]))
  rw [← hpt] at h1
  have hmem : flow (Cs.Zw U W g x) 1 (hOne E a) ∈ cone E a := hF.2 _ hone 1 ⟨zero_le_one, le_rfl⟩
  have h2 := hpb (Cs.Zw U W g x) 1 (Cs.Tw U Ξ w.1 g x) (hOne E a) _ (by simp)
    (hF.1.contDiffAt (ho.mem_nhds hone)) (hc₁ g x) (hsm.contDiffAt (ho.mem_nhds hmem)) h1
  refine (h2.congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hone) fun p hp => (hpe p hp).symm)).mono ?_
  have he : Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) ≤
      Real.exp (B * B₁) * Real.exp (-(A * c)) * Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hlam hB, mul_le_mul_of_nonneg_left hup hA]
  calc _ = C₁ * D₁ * M * Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) := by ring
    _ ≤ C₁ * D₁ * M * (Real.exp (B * B₁) * Real.exp (-(A * c)) *
        Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x))) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring
