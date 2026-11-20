import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomMapOfEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AdjoinMemGenusIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbitRepresentatives

/- English proof (translation)
Set `r` to `MulAction.orbitRel G X`. Set `f : X → X` to `fun x => (@Quotient.mk _ r x).out`. Establish `hf1 : ∀ x, ∃ g : G, g • x = f x` using `fun x => MulAction.orbitRel_apply.mp (@Quotient.mk_out _ r x)`. Establish `hf2 : ∀ x y (g : G), g • y = x → f x = f y` using `fun x y g hg => congrArg Quotient.out (@Quotient.sound _ r x y (MulAction.orbitRel_apply.mpr ⟨g, hg⟩))`. Use `⟨hfin.toFinset.image f, ?_, ?_⟩` and prove the remaining obligations.

Introduce `t ht`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.mp ht`. Take `⟨g, hg⟩` from `hf1 x`. Rewrite using `[← hg]`. Conclude with `hA g x (hfin.mem_toFinset.mp hx)`.

Introduce `x hx`. Take `⟨g, hg⟩` from `hf1 x`. Use `⟨f x, ⟨Finset.mem_image_of_mem f (hfin.mem_toFinset.mpr hx), g⁻¹, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hg, inv_smul_smul]`. Introduce and unpack `y ⟨hy, g', hg'⟩`.

Take `⟨z, -, rfl⟩` from `Finset.mem_image.mp hy`. Take `⟨k, hk⟩` from `hf1 z`. Conclude with `(hf2 x z (g' * k) (by rw [mul_smul, hk, hg'])).symm`.
-/
theorem exists_orbit_reps {G X : Type*} [Group G] [MulAction G X] (A : Set X) (hfin : A.Finite)
    (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by
  classical
  let r := MulAction.orbitRel G X
  let f : X → X := fun x => (@Quotient.mk _ r x).out
  have hf1 : ∀ x, ∃ g : G, g • x = f x := fun x => MulAction.orbitRel_apply.mp (@Quotient.mk_out _ r x)
  have hf2 : ∀ x y (g : G), g • y = x → f x = f y := fun x y g hg =>
    congrArg Quotient.out (@Quotient.sound _ r x y (MulAction.orbitRel_apply.mpr ⟨g, hg⟩))
  refine ⟨hfin.toFinset.image f, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨g, hg⟩ := hf1 x
    rw [← hg]
    exact hA g x (hfin.mem_toFinset.mp hx)
  · intro x hx
    obtain ⟨g, hg⟩ := hf1 x
    refine ⟨f x, ⟨Finset.mem_image_of_mem f (hfin.mem_toFinset.mpr hx), g⁻¹, ?_⟩, ?_⟩
    · rw [← hg, inv_smul_smul]
    · rintro y ⟨hy, g', hg'⟩
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨k, hk⟩ := hf1 z
      exact (hf2 x z (g' * k) (by rw [mul_smul, hk, hg'])).symm

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
The claim follows from `Nat.card_congr { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩ invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`.
-/
theorem card_stabilizer_autSub (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (t : V) :
    Nat.card (MulAction.stabilizer (autSub h L) t) =
      Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} :=
  Nat.card_congr
    { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/- English proof (translation)
Take `⟨hLat, hG⟩` from `hL`. Establish `hiso : ∀ x y, h (g x) (g y) = h x y` using `hg`. Use `show Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) ∧ Formalism.HermitianLatticesTheory.SameGenus h I (Formalism.HermitianLatticesTheory.gmap g L)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Unfold `Formalism.HermitianLatticesTheory.gmap`. Conclude with `hLat.fg.map _`. Unfold `Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[Submodule.map_coe]`. Use `show Submodule.span K (⇑(g : V →ₗ[K] V) '' L) = ⊤`.

Rewrite using `[Submodule.span_image, hLat.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.mpr g.surjective]`. Unfold `Formalism.HermitianLatticesTheory.SameGenus`. Introduce `p hp`. Take `⟨g', hg', he⟩` from `hG p hp`. Use `⟨g * g', mul_mem hg hg', ?_⟩` and prove the remaining obligations.

Rewrite using `[autSub_gmap_mul, he, Formalism.HermitianLattices.Ext.L3.loc_gmap]`.
-/
theorem gmap_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    Formalism.HermitianLatticesTheory.gmap g L ∈ Formalism.HermitianLatticesTheory.genus h I := by
  obtain ⟨hLat, hG⟩ := hL
  have hiso : ∀ x y, h (g x) (g y) = h x y := hg
  show Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) ∧ Formalism.HermitianLatticesTheory.SameGenus h I (Formalism.HermitianLatticesTheory.gmap g L)
  refine ⟨?_, ?_⟩
  · constructor
    · unfold Formalism.HermitianLatticesTheory.gmap
      exact hLat.fg.map _
    · unfold Formalism.HermitianLatticesTheory.gmap
      rw [Submodule.map_coe]
      show Submodule.span K (⇑(g : V →ₗ[K] V) '' L) = ⊤
      rw [Submodule.span_image, hLat.span_eq_top, Submodule.map_top,
        LinearMap.range_eq_top.mpr g.surjective]
  · unfold Formalism.HermitianLatticesTheory.SameGenus
    intro p hp
    obtain ⟨g', hg', he⟩ := hG p hp
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    rw [autSub_gmap_mul, he, Formalism.HermitianLattices.Ext.L3.loc_gmap]

/- English proof (translation)
Take `⟨-, -, hi⟩` from `Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range`. Conclude with `((hi I L (isLattice_of_ortho hI).fg hL.1.fg hL.2).2).mp (isIntegralLat_of_ortho hI)`.
-/
theorem integral_of_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n) (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h L := by
  obtain ⟨-, -, hi⟩ := Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  exact ((hi I L (isLattice_of_ortho hI).fg hL.1.fg hL.2).2).mp (isIntegralLat_of_ortho hI)

/- English proof (translation)
Unfold `Formalism.HermitianLattices.Ext.L3.repCount`. Establish `hfin` using `finite_repSet_of_ortho hK hs hI hL 1`. Use `haveI : Finite (autSub h L) := by`. Use `(finite_autL_of_ortho hK hs hI hL).to_subtype` as an intermediate fact. Conclude with `this`.

Use `haveI : Finite ({x : V | x ∈ L ∧ h x x = 1} : Set V) := hfin.to_subtype`. Establish `hA : ∀ g : autSub h L, ∀ x ∈ ({x : V | x ∈ L ∧ h x x = 1} : Set V), g • x ∈ ({x : V | x ∈ L ∧ h x x = 1} : Set V)`. Introduce and unpack `⟨g, hgI, hgL⟩ x ⟨hxL, hxx⟩`. Establish `hgI' : ∀ x y, h (g x) (g y) = h x y` using `hgI`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `show g x ∈ L`. Rewrite using `[← hgL]`. Unfold `Formalism.HermitianLatticesTheory.gmap`. Conclude with `Submodule.mem_map_of_mem hxL`. Use `show h (g x) (g x) = 1`.

Rewrite using `[hgI' x x, hxx]`. Take `⟨T, hTA, hT⟩` from `exists_orbit_reps (G := autSub h L) _ hfin hA`. Use `⟨T, hTA, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hxL hxx`. Take `⟨t, ⟨htT, g, hg⟩, -⟩` from `hT x ⟨hxL, hxx⟩`.

Conclude with `⟨t, htT, g.1, g.2, hg⟩`. Introduce and unpack `t₁ h₁ t₂ h₂ ⟨a, ha, hat⟩`. Take `⟨t, -, huniq⟩` from `hT t₂ (hTA t₂ h₂)`. Establish `e1` using `huniq t₁ ⟨h₁, ⟨a, ha⟩, hat⟩`. Establish `e2` using `huniq t₂ ⟨h₂, 1, one_smul _ _⟩`.

Rewrite using `[e1, e2]`. Establish `key` using `sum_inv_card_stab (G := autSub h L) _ hA T hTA hT`. Establish `e : ∀ t ∈ T, ((Nat.card (MulAction.stabilizer (autSub h L) t) : ℕ) : ℝ)⁻¹ = ((Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} : ℕ) : ℝ)⁻¹` using `fun t _ => by rw [card_stabilizer_autSub]`. Rewrite using `[← Finset.sum_congr rfl e]`. Conclude with `key`.
-/
theorem exists_reps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
    ∃ T : Finset V, (∀ t ∈ T, t ∈ L ∧ h t t = 1) ∧
      (∀ x, x ∈ L → h x x = 1 → ∃ t ∈ T, ∃ a ∈ Formalism.ThetaLiftIndependence.autL h L, a t = x) ∧
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, (∃ a ∈ Formalism.ThetaLiftIndependence.autL h L, a t₁ = t₂) → t₁ = t₂) ∧
      (repCount h L 1 : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h L) : ℕ) : ℝ) =
        ∑ t ∈ T, ((Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} : ℕ) : ℝ)⁻¹ := by
  classical
  unfold Formalism.HermitianLattices.Ext.L3.repCount
  have hfin := finite_repSet_of_ortho hK hs hI hL 1
  haveI : Finite (autSub h L) := by
    have := (finite_autL_of_ortho hK hs hI hL).to_subtype
    exact this
  haveI : Finite ({x : V | x ∈ L ∧ h x x = 1} : Set V) := hfin.to_subtype
  have hA : ∀ g : autSub h L, ∀ x ∈ ({x : V | x ∈ L ∧ h x x = 1} : Set V),
      g • x ∈ ({x : V | x ∈ L ∧ h x x = 1} : Set V) := by
    rintro ⟨g, hgI, hgL⟩ x ⟨hxL, hxx⟩
    have hgI' : ∀ x y, h (g x) (g y) = h x y := hgI
    refine ⟨?_, ?_⟩
    · show g x ∈ L
      rw [← hgL]
      unfold Formalism.HermitianLatticesTheory.gmap
      exact Submodule.mem_map_of_mem hxL
    · show h (g x) (g x) = 1
      rw [hgI' x x, hxx]
  obtain ⟨T, hTA, hT⟩ := exists_orbit_reps (G := autSub h L) _ hfin hA
  refine ⟨T, hTA, ?_, ?_, ?_⟩
  · intro x hxL hxx
    obtain ⟨t, ⟨htT, g, hg⟩, -⟩ := hT x ⟨hxL, hxx⟩
    exact ⟨t, htT, g.1, g.2, hg⟩
  · rintro t₁ h₁ t₂ h₂ ⟨a, ha, hat⟩
    obtain ⟨t, -, huniq⟩ := hT t₂ (hTA t₂ h₂)
    have e1 := huniq t₁ ⟨h₁, ⟨a, ha⟩, hat⟩
    have e2 := huniq t₂ ⟨h₂, 1, one_smul _ _⟩
    rw [e1, e2]
  · have key := sum_inv_card_stab (G := autSub h L) _ hA T hTA hT
    have e : ∀ t ∈ T, ((Nat.card (MulAction.stabilizer (autSub h L) t) : ℕ) : ℝ)⁻¹ =
        ((Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} : ℕ) : ℝ)⁻¹ :=
      fun t _ => by rw [card_stabilizer_autSub]
    rw [← Finset.sum_congr rfl e]
    exact key

end OrbitRepresentatives

end Formalism.HermitianLattices.Ext.L3
