import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Introduce `hKN hEq hOrb hWC p _ D G L R _ _ gb X N' N π Φ hW k _ _ x y hxy`. Take `⟨ox, oy, mx, my, hys, u, hu, θ, hθ, hθΦ⟩` from `hOrb p D G L R gb N' N (X N') (X N) π Φ hW k x y hxy`. Use `⟨u, hu, fun π' Φ' hW' => ?_⟩` and prove the remaining obligations. Establish `hu1 : u ∈ L.KN 1` using `UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu`. Establish `h1 : (1 : G.GAf) ∈ L.KN 1` using `one_mem _`.

Establish `hid` using `(hWC p D G L R gb N' N' N' (X N') (X N') (X N') 1 1).1 1 (one_mem _)`. Take `⟨hA, hB⟩` from `hEq p D G L R gb N' N' N' (X N') (X N') (X N') u 1 u 1 π' Φ' (𝟙 _) (𝟙 _) hW' hid (UpperTheory.Gal.Int.Geo.integ_of_mem hu1) (UpperTheory.Gal.Int.Geo.integ_of_mem h1) ((hKN p D G L N').1 u hu1) ((hKN p D G L N').1 1 h1) (one_mem _) (by simp) k (x ≫ (X N').s) x y rfl hys ox oy mx m …`. Use `⟨by simpa using hA, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨l, rfl⟩ : ∃ l, l ≫ mx.φ = a` from `⟨_, mx.cart.1.lift_fst a (𝟙 _) (by rw [ha, Category.id_comp])⟩`. Simplify using `only [Category.assoc]`.

Rewrite using `[reassoc_of% hB, hθΦ]`.
-/
theorem UpperTheory.Gal.G3.pWitTrans :
    KNBasic → PtEq → PtOrbit → WitComp → WitTrans := by
  intro hKN hEq hOrb hWC p _ D G L R _ _ gb X N' N π Φ hW k _ _ x y hxy
  obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, hθΦ⟩ := hOrb p D G L R gb N' N (X N') (X N) π Φ hW k x y hxy
  refine ⟨u, hu, fun π' Φ' hW' => ?_⟩
  have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
  have h1 : (1 : G.GAf) ∈ L.KN 1 := one_mem _
  have hid := (hWC p D G L R gb N' N' N' (X N') (X N') (X N') 1 1).1 1 (one_mem _)
  obtain ⟨hA, hB⟩ := hEq p D G L R gb N' N' N' (X N') (X N') (X N') u 1 u 1 π' Φ' (𝟙 _) (𝟙 _) hW' hid
    (UpperTheory.Gal.Int.Geo.integ_of_mem hu1) (UpperTheory.Gal.Int.Geo.integ_of_mem h1)
    ((hKN p D G L N').1 u hu1) ((hKN p D G L N').1 1 h1) (one_mem _) (by simp) k (x ≫ (X N').s) x y rfl hys
    ox oy mx my θ hθ
  refine ⟨by simpa using hA, fun a ha => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ mx.φ = a :=
    ⟨_, mx.cart.1.lift_fst a (𝟙 _) (by rw [ha, Category.id_comp])⟩
  simp only [Category.assoc]
  rw [reassoc_of% hB, hθΦ]
