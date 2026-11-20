import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BasicDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltAddRadial
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullB
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullEquiv
open UpperTheory.V.Lit.Geo.Cs UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `Γ V S _ _ _ _ d G hc l hl Φ hΦ R q w z hw hb hz h`. Establish `hB` using `fun s => pullB V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s) q (z.1 s) (z.2 s).1`. Establish `hA` using `fun s => pullA V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s)`. Establish `hs : ∀ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pull (l s) (z.1 s)) G.Y` using `fun s => (hB s).1`. Establish `hv` using `fun s p (hp : p ∈ G.Y) => UpperTheory.V.Lit.Geo.toOm_apply G hs s hp`.

Establish `hd : ∀ s, ∀ p ∈ G.Y, (G.dOm q (UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s))).1 s p = pull (l s) (extDeriv (z.1 s)) p` using `fun s p hp => by`. Rewrite using `[G.dOm_apply _ s hp, ← (hB s).2 p hp]`. Use `Filter.EventuallyEq.extDeriv_eq ?_` and prove the remaining obligations. Use `filter_upwards [G.isOpen.mem_nhds hp] with y hy using hv s y hy`. Use `⟨UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s), ⟨fun γ => ?_, fun s p hp v i hi => ?_, fun s p hp v i hi => ?_⟩, fun s p hp hR => ?_⟩` and prove the remaining obligations.

Use `Subtype.ext (funext fun s => funext fun p => ?_)` and prove the remaining obligations. Distinguish the cases in `hp : p ∈ G.Y`. Rewrite using `[hv s p hp, ← pullEquiv Γ V S d G hc l hl q z hz γ s p hp, ← hv _ _ (G.maps _ _ hp)]`. Both sides reduce to the same expression. Rewrite using `[((G.act q γ _).2 s).2 p hp, (Subtype.prop (p := fun x => x ∈ G.Om q) _ s).2 p hp]`.

Rewrite using `[hv s p hp]`. Conclude with `(hA s q _).1 p hp v i hi`. Rewrite using `[hd s p hp]`. Conclude with `(hA s (q + 1) _).1 p hp v i hi`. Establish `hcl : ∀ x ∈ G.Y, extDeriv (w.1 s) x = 0` using `fun x hx => by`.

Rewrite using `[← G.dOm_apply w s hx, hw]`. Both sides reduce to the same expression. Establish `hH` using `homog V (Fin d → ℂ) G.Y G.isOpen hc (q + 1) _ (w.2 s).1 (hb s) hcl`. Establish `hpos` using `(hl.1 s).2.1 p hp`. Establish `hm` using `hc _ hpos p hp`.

Rewrite using `[hd s p hp, ← (hA s (q + 1) _).2 (hb s) hH p hp]`. Unfold `pull`. Rewrite using `[← G.dOm_apply z s hm, h s _ hm (by rw [hΦ.2.2 s _ hpos p hp]; exact hR)]`.
-/
theorem UpperTheory.V.Lit.Geo.Cs.geoRet :
    GeoRet := by
  intro Γ V S _ _ _ _ d G hc l hl Φ hΦ R q w z hw hb hz h
  have hB := fun s => pullB V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s) q (z.1 s) (z.2 s).1
  have hA := fun s => pullA V (Fin d → ℂ) G.Y G.isOpen hc (l s) (hl.1 s)
  have hs : ∀ s, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pull (l s) (z.1 s)) G.Y := fun s => (hB s).1
  have hv := fun s p (hp : p ∈ G.Y) => UpperTheory.V.Lit.Geo.toOm_apply G hs s hp
  have hd : ∀ s, ∀ p ∈ G.Y, (G.dOm q (UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s))).1 s p =
      pull (l s) (extDeriv (z.1 s)) p := fun s p hp => by
    rw [G.dOm_apply _ s hp, ← (hB s).2 p hp]
    refine Filter.EventuallyEq.extDeriv_eq ?_
    filter_upwards [G.isOpen.mem_nhds hp] with y hy using hv s y hy
  refine ⟨UpperTheory.V.Lit.Geo.toOm G fun s => pull (l s) (z.1 s), ⟨fun γ => ?_, fun s p hp v i hi => ?_,
    fun s p hp v i hi => ?_⟩, fun s p hp hR => ?_⟩
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ G.Y
    · rw [hv s p hp, ← pullEquiv Γ V S d G hc l hl q z hz γ s p hp, ← hv _ _ (G.maps _ _ hp)]
      rfl
    · rw [((G.act q γ _).2 s).2 p hp, (Subtype.prop (p := fun x => x ∈ G.Om q) _ s).2 p hp]
  · rw [hv s p hp]
    exact (hA s q _).1 p hp v i hi
  · rw [hd s p hp]
    exact (hA s (q + 1) _).1 p hp v i hi
  · have hcl : ∀ x ∈ G.Y, extDeriv (w.1 s) x = 0 := fun x hx => by
      rw [← G.dOm_apply w s hx, hw]
      rfl
    have hH := homog V (Fin d → ℂ) G.Y G.isOpen hc (q + 1) _ (w.2 s).1 (hb s) hcl
    have hpos := (hl.1 s).2.1 p hp
    have hm := hc _ hpos p hp
    rw [hd s p hp, ← (hA s (q + 1) _).2 (hb s) hH p hp]
    unfold pull
    rw [← G.dOm_apply z s hm, h s _ hm (by rw [hΦ.2.2 s _ hpos p hp]; exact hR)]
