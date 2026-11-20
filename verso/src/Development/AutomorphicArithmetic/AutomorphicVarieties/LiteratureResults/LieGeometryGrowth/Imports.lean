import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsLocBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsMove

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs
open scoped Topology

/- English proof (translation)
Introduce `E _ _ _ a ho U Ξ f lam hf hl Φ hD hΦ q k A B R hA hB s p hp hR`. Take `⟨c, hc⟩` from `UpperTheory.V.Lit.Geo.Cs.locBd E a p hp`. Take `⟨D, hD0, hmv⟩` from `UpperTheory.V.Lit.Geo.Cs.move E a ho U Ξ q k c`. Take `⟨B₀, hB₀⟩` from `hl.bdd c`. Take `⟨y, rfl⟩` from `QuotientGroup.mk_surjective s`.

Establish `hcont : ContinuousAt (Φ (y : GL (Fin a) (Af E) ⧸ U)) p` using `((hΦ.1 _).continuousOn.continuousAt (ho.mem_nhds hp))`. Establish `hev : ∀ᶠ x in 𝓝 p, R < Φ (y : GL (Fin a) (Af E) ⧸ U) x` using `hcont.eventually (lt_mem_nhds hR)`. Use `⟨_, hc.and hev, D * Real.exp (B * (B₀ + |lam (finGL E a y)|)), fun M hM w hw x hx => ?_⟩` and prove the remaining obligations. Take `⟨⟨h, hh, rfl⟩, hx⟩` from `hx`. Rewrite `hx` using `[hD h y]`.

Establish `h1` using `hw h y hx.le`. Establish `h2` using `hmv w 1 y h _ hh (by rw [one_mul]; exact h1)`. Rewrite `h2` using `[Tw_one]`. Use `h2.mono ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, mul_comm _ M]`.

Use `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM) hD0` and prove the remaining obligations. Establish `h3 : |lam (pt h y)| ≤ B₀ + |lam (finGL E a y)|`. Rewrite using `[pt, hl.add]`. Conclude with `(abs_add_le _ _).trans (add_le_add (hB₀ h hh) le_rfl)`. Establish `h4` using `mul_nonneg hA (hf (pt h y))`.

Establish `h5` using `mul_le_mul_of_nonneg_left h3 hB`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.Lit.Geo.Cs.loc :
    UpperTheory.V.Lit.Geo.Cs.Loc := by
  intro E _ _ _ a ho U Ξ f lam hf hl Φ hD hΦ q k A B R hA hB s p hp hR
  obtain ⟨c, hc⟩ := UpperTheory.V.Lit.Geo.Cs.locBd E a p hp
  obtain ⟨D, hD0, hmv⟩ := UpperTheory.V.Lit.Geo.Cs.move E a ho U Ξ q k c
  obtain ⟨B₀, hB₀⟩ := hl.bdd c
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
  have hcont : ContinuousAt (Φ (y : GL (Fin a) (Af E) ⧸ U)) p :=
    ((hΦ.1 _).continuousOn.continuousAt (ho.mem_nhds hp))
  have hev : ∀ᶠ x in 𝓝 p, R < Φ (y : GL (Fin a) (Af E) ⧸ U) x := hcont.eventually (lt_mem_nhds hR)
  refine ⟨_, hc.and hev, D * Real.exp (B * (B₀ + |lam (finGL E a y)|)), fun M hM w hw x hx => ?_⟩
  obtain ⟨⟨h, hh, rfl⟩, hx⟩ := hx
  rw [hD h y] at hx
  have h1 := hw h y hx.le
  have h2 := hmv w 1 y h _ hh (by rw [one_mul]; exact h1)
  rw [Tw_one] at h2
  refine h2.mono ?_
  rw [mul_assoc, mul_comm _ M]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM) hD0
  have h3 : |lam (pt h y)| ≤ B₀ + |lam (finGL E a y)| := by
    rw [pt, hl.add]
    exact (abs_add_le _ _).trans (add_le_add (hB₀ h hh) le_rfl)
  have h4 := mul_nonneg hA (hf (pt h y))
  have h5 := mul_le_mul_of_nonneg_left h3 hB
  linarith
