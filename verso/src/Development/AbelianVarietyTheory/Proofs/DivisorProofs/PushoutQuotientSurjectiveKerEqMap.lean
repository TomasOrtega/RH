import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `R C E _ _ _ c f π χ h`. Establish `hw' : ∀ r, π (f r) = χ (Ideal.Quotient.mk c r)` using `fun r => by`. Use `congrArg (fun g => g.hom r) h.w` as an intermediate fact. Simplify using `using this`. Establish `hle : c.map f ≤ RingHom.ker π`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `r hr`. Simplify using `[RingHom.mem_ker, hw', Ideal.Quotient.eq_zero_iff_mem.mpr hr]`. Set `q : C →+* C ⧸ c.map f` to `Ideal.Quotient.mk _`. Set `qm : R ⧸ c →+* C ⧸ c.map f` to `Ideal.quotientMap (c.map f) f Ideal.le_comap_map`.

Set `φ : C ⧸ c.map f →+* E` to `Ideal.Quotient.lift _ π (fun x hx => hle hx)`. Establish `hcomm : CommRingCat.ofHom f ≫ CommRingCat.ofHom q = CommRingCat.ofHom (Ideal.Quotient.mk c) ≫ CommRingCat.ofHom qm`. Use extensionality with `r`. Both sides reduce to the same expression. Set `ψ` to `h.desc (CommRingCat.ofHom q) (CommRingCat.ofHom qm) hcomm`.

Establish `h1 : CommRingCat.ofHom π ≫ ψ = CommRingCat.ofHom q` using `h.inl_desc _ _ _`. Establish `h2 : CommRingCat.ofHom χ ≫ ψ = CommRingCat.ofHom qm` using `h.inr_desc _ _ _`. Establish `hid : ψ ≫ CommRingCat.ofHom φ = 𝟙 _`. Apply `h.hom_ext` to reduce the goal to its premises. Rewrite using `[← Category.assoc, h1, Category.comp_id]`.

Use extensionality with `x`. Both sides reduce to the same expression. Rewrite using `[← Category.assoc, h2, Category.comp_id]`. Use extensionality with `r`. Express the relevant statement in the definitionally equal form `φ (qm (Ideal.Quotient.mk c r)) = χ (Ideal.Quotient.mk c r)`.

Rewrite using `[← hw']`. Both sides reduce to the same expression. Establish `hφsurj : Function.Surjective φ` using `fun e => ⟨ψ e, by`. Use `congrArg (fun g => g.hom e) hid` as an intermediate fact. Simplify using `using this⟩`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `e`. Take `⟨y, hy⟩` from `hφsurj e`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨x, hy⟩`.

Use `le_antisymm ?_ hle` and prove the remaining obligations. Introduce `x hx`. Establish `hx1 : ψ.hom (π x) = q x`. Rewrite using `[← CommRingCat.hom_ofHom q, ← h1]`. Both sides reduce to the same expression.

Rewrite `hx` using `[RingHom.mem_ker]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Express the relevant statement in the definitionally equal form `q x = 0`. Rewrite using `[← hx1, hx, map_zero]`.
-/
theorem pushout_quotient_map_eq_quotient_map_ideal : ∀ (R C E : Type) [CommRing R] [CommRing C] [CommRing E] (c : Ideal R) (f : R →+* C) (π : C →+* E) (χ : R ⧸ c →+* E), IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom χ) → Function.Surjective π ∧ RingHom.ker π = c.map f := by
  intro R C E _ _ _ c f π χ h
  have hw' : ∀ r, π (f r) = χ (Ideal.Quotient.mk c r) := fun r => by
    have := congrArg (fun g => g.hom r) h.w
    simpa using this
  have hle : c.map f ≤ RingHom.ker π := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp [RingHom.mem_ker, hw', Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  let q : C →+* C ⧸ c.map f := Ideal.Quotient.mk _
  let qm : R ⧸ c →+* C ⧸ c.map f := Ideal.quotientMap (c.map f) f Ideal.le_comap_map
  let φ : C ⧸ c.map f →+* E := Ideal.Quotient.lift _ π (fun x hx => hle hx)
  have hcomm : CommRingCat.ofHom f ≫ CommRingCat.ofHom q =
      CommRingCat.ofHom (Ideal.Quotient.mk c) ≫ CommRingCat.ofHom qm := by
    ext r; rfl
  let ψ := h.desc (CommRingCat.ofHom q) (CommRingCat.ofHom qm) hcomm
  have h1 : CommRingCat.ofHom π ≫ ψ = CommRingCat.ofHom q := h.inl_desc _ _ _
  have h2 : CommRingCat.ofHom χ ≫ ψ = CommRingCat.ofHom qm := h.inr_desc _ _ _
  have hid : ψ ≫ CommRingCat.ofHom φ = 𝟙 _ := by
    apply h.hom_ext
    · rw [← Category.assoc, h1, Category.comp_id]
      ext x; rfl
    · rw [← Category.assoc, h2, Category.comp_id]
      ext r
      change φ (qm (Ideal.Quotient.mk c r)) = χ (Ideal.Quotient.mk c r)
      rw [← hw']
      rfl
  have hφsurj : Function.Surjective φ := fun e =>
    ⟨ψ e, by
      have := congrArg (fun g => g.hom e) hid
      simpa using this⟩
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨y, hy⟩ := hφsurj e
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, hy⟩
  · refine le_antisymm ?_ hle
    intro x hx
    have hx1 : ψ.hom (π x) = q x := by
      rw [← CommRingCat.hom_ofHom q, ← h1]; rfl
    rw [RingHom.mem_ker] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q x = 0
    rw [← hx1, hx, map_zero]

end GlobalTheory
