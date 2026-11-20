import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsTwOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsHomSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsZwSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullFieldFlow
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped Topology
open UpperTheory.V.Lit.Geo

/- English proof (translation)
Introduce `E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k A B hA hB`. Take `⟨hfl, hflow⟩` from `fieldFlow E a ho U Ξ Y C hS.fld W hW`. Take `⟨z, hz⟩` from `zwSz E a U Y C hS.fld W hW (k + 1)`. Take `⟨C₁, hC₁, hhom⟩` from `homSz (HV E a) (Fin Ξ.d → ℂ) q k z`. Take `⟨D₁, hD₁, hmv⟩` from `move E a ho U Ξ (q + 1) k C`.

Take `⟨L, hL⟩` from `hl.bdd C`. Use `⟨C₁ * D₁ * Real.exp (B * L + A * C), by positivity, fun M hM w hw g x hg => ?_⟩` and prove the remaining obligations. Take `⟨hfield, hfz, hq⟩` from `twOps E a ho U Ξ W hfl g x`. Establish `hsm` using `((hq (q + 1)).1 w).1`. Establish `heq` using `(hq q).2 w`.

Establish `key : ∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k (Tw U Ξ w.1 g x) (flow (Zw U W g x) t (hOne E a)) (D₁ * (M * (Real.exp (B * L + A * C) * Real.exp (B * |lam (pt g x)| - A * f (pt g x)))))`. Introduce `t ht`. Establish `ht' : |t| ≤ 1` using `abs_le.2 ⟨by linarith [ht.1], ht.2⟩`. Take `⟨h, hh, h1, h2⟩` from `hS.root (pt g x) t ht'`. Establish `hn` using `abs_le.1 (hS.near (pt g x) t h ht' hh)`.

Establish `e : flow (Zw U W g x) t (hOne E a) = sand h (hOne E a)`. Rewrite using `[hfz, hflow g h x t hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]`. Rewrite using `[e]`. Use `hmv w g x h _ ⟨h1, h2⟩ ((hw (g * h) x (by rw [pt_mul]; linarith [hn.1])).mono ?_)` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left ?_ hM` and prove the remaining obligations.

Rewrite using `[← Real.exp_add, pt_mul, hl.add]`. Use `Real.exp_le_exp.2 ?_` and prove the remaining obligations. Establish `b1 : |lam (pt g x) + lam (infGL E a h)| ≤ L + |lam (pt g x)|`. Combine the linear relations using `[abs_add_le (lam (pt g x)) (lam (infGL E a h)), hL h ⟨h1, h2⟩]`. Establish `b2` using `mul_le_mul_of_nonneg_left b1 hB`.

Establish `b3` using `mul_le_mul_of_nonneg_left hn.1 hA`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `main` using `hhom (cone E a) (Zw U W g x) (Tw U Ξ w.1 g x) _ ho hfield hsm (hOne E a) hOne_mem_cone (hz g x) key`. Use `(main.congr ?_).mono (le_of_eq (by ring))` and prove the remaining obligations. Use `filter_upwards [ho.mem_nhds hOne_mem_cone] with p hp`.

Conclude with `(heq p hp).symm`.
-/
theorem UpperTheory.V.Lit.Geo.Cs.decK :
    UpperTheory.V.Lit.Geo.Cs.DecK := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k A B hA hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨z, hz⟩ := zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hhom⟩ := homSz (HV E a) (Fin Ξ.d → ℂ) q k z
  obtain ⟨D₁, hD₁, hmv⟩ := move E a ho U Ξ (q + 1) k C
  obtain ⟨L, hL⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * L + A * C), by positivity, fun M hM w hw g x hg => ?_⟩
  obtain ⟨hfield, hfz, hq⟩ := twOps E a ho U Ξ W hfl g x
  have hsm := ((hq (q + 1)).1 w).1
  have heq := (hq q).2 w
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k (Tw U Ξ w.1 g x) (flow (Zw U W g x) t (hOne E a))
      (D₁ * (M * (Real.exp (B * L + A * C) * Real.exp (B * |lam (pt g x)| - A * f (pt g x))))) := by
    intro t ht
    have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨h, hh, h1, h2⟩ := hS.root (pt g x) t ht'
    have hn := abs_le.1 (hS.near (pt g x) t h ht' hh)
    have e : flow (Zw U W g x) t (hOne E a) = sand h (hOne E a) := by
      rw [hfz, hflow g h x t hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
    rw [e]
    refine hmv w g x h _ ⟨h1, h2⟩ ((hw (g * h) x (by rw [pt_mul]; linarith [hn.1])).mono ?_)
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [← Real.exp_add, pt_mul, hl.add]
    refine Real.exp_le_exp.2 ?_
    have b1 : |lam (pt g x) + lam (infGL E a h)| ≤ L + |lam (pt g x)| := by
      linarith [abs_add_le (lam (pt g x)) (lam (infGL E a h)), hL h ⟨h1, h2⟩]
    have b2 := mul_le_mul_of_nonneg_left b1 hB
    have b3 := mul_le_mul_of_nonneg_left hn.1 hA
    linarith
  have main := hhom (cone E a) (Zw U W g x) (Tw U Ξ w.1 g x) _ ho hfield hsm (hOne E a) hOne_mem_cone (hz g x) key
  refine (main.congr ?_).mono (le_of_eq (by ring))
  filter_upwards [ho.mem_nhds hOne_mem_cone] with p hp
  exact (heq p hp).symm
