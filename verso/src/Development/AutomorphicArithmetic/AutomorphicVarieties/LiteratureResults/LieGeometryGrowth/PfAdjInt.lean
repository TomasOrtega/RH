import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtDiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfStokesFn
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfTwLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsTens
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfBddInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsBdd
open UpperTheory.V.Lit.Geo

/- English proof (translation)
Introduce `E _ _ _ a μ _ Ξ r χ G htw hadm X x y hx hy hs`. Establish `hint : ∀ u v, Pf.TwInv χ u → Pf.TwInv χ v → Pf.Cs (Pf.pt χ G u v) → Pf.QInt μ (Pf.pt χ G u v)` using `fun u v hu hv hc =>`. Establish `hC` using `(Pf.ptInv E a χ _ G u v).2.1 hu hv`. Use the proof step `(Pf.bddInt E a μ _ hC (Pf.csBdd E a _ hC (.inl hc))).1`. Use `(fun (h : _ ∧ _) (h3 : _ ∧ _ → _) => ⟨h.1, h.2, h3 h⟩) ⟨?_, ?_⟩ ?_` and prove the remaining obligations.

Conclude with `hint _ _ hx (Pf.twLie E a Ξ r χ htw _ y hy).1 (hs.elim (fun h => Pf.cs_pt_left χ G _ h) fun h => Pf.cs_pt_right χ G _ (Pf.csTens E a Ξ r _ y h).1)`. Conclude with `hint _ _ (Pf.twLie E a Ξ r χ htw _ x hx).2 hy (hs.elim (fun h => Pf.cs_pt_left χ G _ (Pf.csTens E a Ξ r _ x h).2) fun h => Pf.cs_pt_right χ G _ h)`. Introduce and unpack `⟨h1, h2⟩`. Take `⟨θ, hθ, hd⟩` from `Pf.ptDiv E a Ξ r χ G htw hadm x y`. Establish `hS` using `(Pf.ptInv E a χ _ G x y).2.2 θ hθ hx hy`.

Establish `hc : Pf.Cs θ.1`. Rewrite using `[show θ.1 = _ from funext hθ]`. Conclude with `hs.elim (fun h => Pf.cs_pt_left χ G _ h) fun h => Pf.cs_pt_right χ G _ h`. Establish `h0` using `fun Y => Pf.stokesFn E a μ θ Y hS hc`. Use `sub_eq_zero.1 ?_` and prove the remaining obligations.

Unfold `Pf.qint at h0 ⊢`. Rewrite using `[← MeasureTheory.integral_sub h1 h2]`. Simplify using `only [← hd X]`. Conclude with `h0 _`.
-/
theorem UpperTheory.V.Lit.Geo.Pf.adjInt :
    UpperTheory.V.Lit.Geo.Pf.AdjInt := by
  intro E _ _ _ a μ _ Ξ r χ G htw hadm X x y hx hy hs
  have hint : ∀ u v, Pf.TwInv χ u → Pf.TwInv χ v → Pf.Cs (Pf.pt χ G u v) → Pf.QInt μ (Pf.pt χ G u v) :=
    fun u v hu hv hc =>
      have hC := (Pf.ptInv E a χ _ G u v).2.1 hu hv
      (Pf.bddInt E a μ _ hC (Pf.csBdd E a _ hC (.inl hc))).1
  refine (fun (h : _ ∧ _) (h3 : _ ∧ _ → _) => ⟨h.1, h.2, h3 h⟩) ⟨?_, ?_⟩ ?_
  · exact hint _ _ hx (Pf.twLie E a Ξ r χ htw _ y hy).1
      (hs.elim (fun h => Pf.cs_pt_left χ G _ h)
        fun h => Pf.cs_pt_right χ G _ (Pf.csTens E a Ξ r _ y h).1)
  · exact hint _ _ (Pf.twLie E a Ξ r χ htw _ x hx).2 hy
      (hs.elim (fun h => Pf.cs_pt_left χ G _ (Pf.csTens E a Ξ r _ x h).2)
        fun h => Pf.cs_pt_right χ G _ h)
  rintro ⟨h1, h2⟩
  obtain ⟨θ, hθ, hd⟩ := Pf.ptDiv E a Ξ r χ G htw hadm x y
  have hS := (Pf.ptInv E a χ _ G x y).2.2 θ hθ hx hy
  have hc : Pf.Cs θ.1 := by
    rw [show θ.1 = _ from funext hθ]
    exact hs.elim (fun h => Pf.cs_pt_left χ G _ h) fun h => Pf.cs_pt_right χ G _ h
  have h0 := fun Y => Pf.stokesFn E a μ θ Y hS hc
  refine sub_eq_zero.1 ?_
  unfold Pf.qint at h0 ⊢
  rw [← MeasureTheory.integral_sub h1 h2]
  simp only [← hd X]
  exact h0 _
