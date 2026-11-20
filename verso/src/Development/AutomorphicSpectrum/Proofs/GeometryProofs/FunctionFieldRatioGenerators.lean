import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart

/- English proof (translation)
Take `⟨U, hU, hUc⟩` from `hT.affine c hc`. Establish `hreg0 : ∀ b : Ω, b ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩`. Introduce `b`. Take `⟨s, hs⟩` from `hT.gen.bij.2 b`. Use `show b ∈ (genMap ξ _).range`.

Use `RingHom.mem_range.mpr ⟨s, ?_⟩` and prove the remaining obligations. Simplify using `only [genMap, TopCat.Presheaf.stalkSpecializes_refl]`. Use `first`. Consider the case `exact hs`. Consider the case `(rw [Category.id_comp]; exact hs)`.

Consider the case `simpa using hs`. Establish `hgU : genPt ξ ∈ U` using `(hUc (genPt ξ)).mpr ⟨specializes_refl _, And.intro hc fun _ => hreg0 _⟩`. Set `φ : Γ(X, U) →+* Ω` to `(X.presheaf.germ U (genPt ξ) hgU ≫ Scheme.stalkClosedPointTo ξ).hom`. Establish `key : ∀ r : Γ(X, U), φ r ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)`. Introduce `r`.

Use `(hT.ring c hc (φ r)).mpr fun p hp => ?_` and prove the remaining obligations. Establish `hpU : p.1 ∈ U` using `(hUc p.1).mpr ⟨p.2, hp⟩`. Use `show φ r ∈ (genMap ξ p).range`. Use `RingHom.mem_range.mpr ⟨(X.presheaf.germ U p.1 hpU).hom r, ?_⟩` and prove the remaining obligations. Establish `e0 : X.presheaf.germ U p.1 hpU ≫ X.presheaf.stalkSpecializes p.2 = X.presheaf.germ U (genPt ξ) hgU` using `by first`.

Consider the case `simp`. Consider the case `exact TopCat.Presheaf.germ_stalkSpecializes X.presheaf hpU p.2`. Consider the case `exact TopCat.Presheaf.germ_stalkSpecializes hpU p.2`. Use `show (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U p.1 hpU).hom r) = φ r`. Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp]`.

Use `first`. Consider the case `exact congrArg (fun (m : Γ(X, U) ⟶ CommRingCat.of Ω) => CommRingCat.Hom.hom m r) ((reassoc_of% e0) (Scheme.stalkClosedPointTo ξ))`. Consider the case `(simp only [reassoc_of% e0]; rfl)`. Establish `gres : ∀ {W W' : X.Opens} (hle : W ≤ W') (hw : genPt ξ ∈ W) (z : Γ(X, W')), (X.presheaf.germ W (genPt ξ) hw).hom ((X.presheaf.map (homOfLE hle).op).hom z) = (X.presheaf.germ W' (genPt ξ) (hle hw)).hom z`. Introduce `W W' hle hw z`.

Establish `e : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ W (genPt ξ) hw = X.presheaf.germ W' (genPt ξ) (hle hw)` using `by first`. Consider the case `simp`. Consider the case `exact TopCat.Presheaf.germ_res _ _ _ _`. Conclude with `congrArg (fun m => m.hom z) e`. Take `⟨s0, hs0⟩ : ∃ s0 : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s0 = a` from `hT.gen.bij.2 a`.

Take `⟨V, hV, f, rfl⟩` from `TopCat.Presheaf.germ_exist X.presheaf s0`. Take `⟨t, htV, hgt⟩` from `hU.exists_basicOpen_le ⟨genPt ξ, hV⟩ hgU`. Establish `hD : genPt ξ ∈ X.basicOpen t` using `hgt`. Take `⟨n, y, hy⟩` from `exists_eq_pow_mul_of_isAffineOpen X U hU t ((X.presheaf.map (homOfLE htV).op).hom f)`. Establish `hy' : (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom y = ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom t) ^ n * (X.presheaf.map (homOfLE htV).op).hom f` using `hy`.

Establish `h2 : (X.presheaf.germ U (genPt ξ) hgU).hom y = ((X.presheaf.germ U (genPt ξ) hgU).hom t) ^ n * (X.presheaf.germ V (genPt ξ) hV).hom f`. Establish `h2'` using `congrArg (X.presheaf.germ (X.basicOpen t) (genPt ξ) hD).hom hy'`. Simplify using `only [map_mul, map_pow, gres] at h2'`. Conclude with `h2'`. Set `ψ : X.presheaf.stalk (genPt ξ) →+* Ω` to `(Scheme.stalkClosedPointTo ξ).hom`.

Establish `hφ : ∀ r, φ r = ψ ((X.presheaf.germ U (genPt ξ) hgU).hom r)`. Introduce `r`. Use `first`. Consider the case `rfl`. Consider the case `simp [φ, ψ]`.

Establish `hs0' : ψ ((X.presheaf.germ V (genPt ξ) hV).hom f) = a` using `hs0`. Establish `h3 : φ y = φ t ^ n * a`. Rewrite using `[hφ, hφ, h2, map_mul, map_pow, hs0']`. Establish `hunit : IsUnit ((X.presheaf.germ U (genPt ξ) hgU).hom t)` using `(X.mem_basicOpen t (genPt ξ) hgU).mp hD`. Establish `hφt : φ t ≠ 0`.

Rewrite using `[hφ]`. Conclude with `(hunit.map ψ).ne_zero`. Use `⟨φ y, key y, φ (t ^ n), key (t ^ n), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `pow_ne_zero _ hφt`.

Rewrite using `[map_pow]`. Conclude with `eq_div_of_mul_eq (pow_ne_zero _ hφt) (by rw [h3]; ring)`.
-/
theorem exists_eq_div_adjoin (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ)
    (hT : CoordTie ℤ ξ x) (hc : x c ≠ 0) (a : Ω) :
    ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), h ≠ 0 ∧ a = g / h := by
  obtain ⟨U, hU, hUc⟩ := hT.affine c hc
  have hreg0 : ∀ b : Ω, b ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩ := by
    intro b
    obtain ⟨s, hs⟩ := hT.gen.bij.2 b
    show b ∈ (genMap ξ _).range
    refine RingHom.mem_range.mpr ⟨s, ?_⟩
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    first
      | exact hs
      | (rw [Category.id_comp]; exact hs)
      | simpa using hs
  have hgU : genPt ξ ∈ U :=
    (hUc (genPt ξ)).mpr ⟨specializes_refl _, And.intro hc fun _ => hreg0 _⟩
  let φ : Γ(X, U) →+* Ω := (X.presheaf.germ U (genPt ξ) hgU ≫ Scheme.stalkClosedPointTo ξ).hom
  have key : ∀ r : Γ(X, U), φ r ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    intro r
    refine (hT.ring c hc (φ r)).mpr fun p hp => ?_
    have hpU : p.1 ∈ U := (hUc p.1).mpr ⟨p.2, hp⟩
    show φ r ∈ (genMap ξ p).range
    refine RingHom.mem_range.mpr ⟨(X.presheaf.germ U p.1 hpU).hom r, ?_⟩
    have e0 : X.presheaf.germ U p.1 hpU ≫ X.presheaf.stalkSpecializes p.2 =
        X.presheaf.germ U (genPt ξ) hgU := by
      first
        | simp
        | exact TopCat.Presheaf.germ_stalkSpecializes X.presheaf hpU p.2
        | exact TopCat.Presheaf.germ_stalkSpecializes hpU p.2
    show (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom
        ((X.presheaf.germ U p.1 hpU).hom r) = φ r
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
    first
      | exact congrArg (fun (m : Γ(X, U) ⟶ CommRingCat.of Ω) => CommRingCat.Hom.hom m r)
          ((reassoc_of% e0) (Scheme.stalkClosedPointTo ξ))
      | (simp only [reassoc_of% e0]; rfl)
  have gres : ∀ {W W' : X.Opens} (hle : W ≤ W') (hw : genPt ξ ∈ W) (z : Γ(X, W')),
      (X.presheaf.germ W (genPt ξ) hw).hom ((X.presheaf.map (homOfLE hle).op).hom z) =
        (X.presheaf.germ W' (genPt ξ) (hle hw)).hom z := by
    intro W W' hle hw z
    have e : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ W (genPt ξ) hw =
        X.presheaf.germ W' (genPt ξ) (hle hw) := by
      first
        | simp
        | exact TopCat.Presheaf.germ_res _ _ _ _
    exact congrArg (fun m => m.hom z) e
  obtain ⟨s0, hs0⟩ : ∃ s0 : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s0 = a :=
    hT.gen.bij.2 a
  obtain ⟨V, hV, f, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s0
  obtain ⟨t, htV, hgt⟩ := hU.exists_basicOpen_le ⟨genPt ξ, hV⟩ hgU
  have hD : genPt ξ ∈ X.basicOpen t := hgt
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X U hU t
    ((X.presheaf.map (homOfLE htV).op).hom f)
  have hy' : (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom y =
      ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom t) ^ n *
        (X.presheaf.map (homOfLE htV).op).hom f := hy
  have h2 : (X.presheaf.germ U (genPt ξ) hgU).hom y =
      ((X.presheaf.germ U (genPt ξ) hgU).hom t) ^ n * (X.presheaf.germ V (genPt ξ) hV).hom f := by
    have h2' := congrArg (X.presheaf.germ (X.basicOpen t) (genPt ξ) hD).hom hy'
    simp only [map_mul, map_pow, gres] at h2'
    exact h2'
  let ψ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
  have hφ : ∀ r, φ r = ψ ((X.presheaf.germ U (genPt ξ) hgU).hom r) := by
    intro r
    first
      | rfl
      | simp [φ, ψ]
  have hs0' : ψ ((X.presheaf.germ V (genPt ξ) hV).hom f) = a := hs0
  have h3 : φ y = φ t ^ n * a := by
    rw [hφ, hφ, h2, map_mul, map_pow, hs0']
  have hunit : IsUnit ((X.presheaf.germ U (genPt ξ) hgU).hom t) :=
    (X.mem_basicOpen t (genPt ξ) hgU).mp hD
  have hφt : φ t ≠ 0 := by
    rw [hφ]
    exact (hunit.map ψ).ne_zero
  refine ⟨φ y, key y, φ (t ^ n), key (t ^ n), ?_, ?_⟩
  · rw [map_pow]
    exact pow_ne_zero _ hφt
  · rw [map_pow]
    exact eq_div_of_mul_eq (pow_ne_zero _ hφt) (by rw [h3]; ring)

end GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart
