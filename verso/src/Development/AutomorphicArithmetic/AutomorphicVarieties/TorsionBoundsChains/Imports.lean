import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.QuotientsEquivOfKerEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.L1MapDomainLeAndL1FaceDSingleLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.CokerTors
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `G X Y _ _ M e d A b hsurj hex hA hb hd`. Use `set S : Set (X →₀ ℤ) := Set.range (fun y => d (Finsupp.single y 1)) with hS`. Establish `hspan : Submodule.span ℤ S = LinearMap.range d`. Establish `h1 : S = d '' Set.range (fun y : Y => Finsupp.single y (1 : ℤ))`. Rewrite using `[hS, ← Set.range_comp]`.

Both sides reduce to the same expression. Rewrite using `[h1, Submodule.span_image, ← Submodule.map_top]`. Use `congr 1`. Use `(Finsupp.basisSingleOne (R := ℤ) (ι := Y)).span_eq` as an intermediate fact. Rewrite `this` using `[Finsupp.coe_basisSingleOne]`.

Conclude with `this`. Establish `hker : ∀ f : X →₀ ℤ, e.hom f = 0 ↔ f ∈ Submodule.span ℤ S`. Introduce `f`. Rewrite using `[hspan, LinearMap.mem_range]`. Conclude with `(hex f).trans Set.mem_range`.

Take `⟨φ⟩` from `hZero G X M e S hsurj hker`. Establish `hL : ∀ x ∈ Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel G X)) '' S, l1 x ≤ b`. Introduce and unpack `x ⟨s, ⟨y, rfl⟩, rfl⟩`. Conclude with `(l1_mapDomain_le_and_l1_faceD_single_le.1 _ _ _ _).trans (hd y)`. Establish `hT` using `cokerTors (MulAction.orbitRel.Quotient G X) A b _ hA hb hL`.

Conclude with `transport.1 _ _ φ.symm _ hT`.
-/
theorem UpperTheory.V.KH.base :
    ∀ (G X Y : Type) [Group G] [MulAction G X] (M : Rep ℤ G) (e : permRep G X ⟶ M)
      (d : (Y →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ)) (A b : ℕ), Function.Surjective e.hom → Function.Exact d e.hom →
      OrbLe G X A → 1 ≤ b → (∀ y, l1 (d (Finsupp.single y 1)) ≤ b) →
      TorsLe (groupHomology M 0) (b ^ A) := by
  intro G X Y _ _ M e d A b hsurj hex hA hb hd
  set S : Set (X →₀ ℤ) := Set.range (fun y => d (Finsupp.single y 1)) with hS
  have hspan : Submodule.span ℤ S = LinearMap.range d := by
    have h1 : S = d '' Set.range (fun y : Y => Finsupp.single y (1 : ℤ)) := by
      rw [hS, ← Set.range_comp]
      rfl
    rw [h1, Submodule.span_image, ← Submodule.map_top]
    congr 1
    have := (Finsupp.basisSingleOne (R := ℤ) (ι := Y)).span_eq
    rw [Finsupp.coe_basisSingleOne] at this
    exact this
  have hker : ∀ f : X →₀ ℤ, e.hom f = 0 ↔ f ∈ Submodule.span ℤ S := by
    intro f
    rw [hspan, LinearMap.mem_range]
    exact (hex f).trans Set.mem_range
  obtain ⟨φ⟩ := hZero G X M e S hsurj hker
  have hL : ∀ x ∈ Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel G X)) '' S, l1 x ≤ b := by
    rintro x ⟨s, ⟨y, rfl⟩, rfl⟩
    exact (l1_mapDomain_le_and_l1_faceD_single_le.1 _ _ _ _).trans (hd y)
  have hT := cokerTors (MulAction.orbitRel.Quotient G X) A b _ hA hb hL
  exact transport.1 _ _ φ.symm _ hT
